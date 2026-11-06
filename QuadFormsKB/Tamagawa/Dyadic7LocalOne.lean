/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Dyadic7Local
import QuadFormsKB.Tamagawa.AlphaLawSplit
import QuadFormsKB.Literature.Hanke2011Structure.DyadicOdd
import QuadFormsKB.Literature.Cassels.Ch14.Existence

/-!
# Paper 7 at $p = 2$: the row $h = 1$ of Table 5.3, unconditionally

**Setting.** $v$ is the prime $2$ of $\mathbb Q$, $S \in \mathrm{SqCl}(\mathbb Q_2^\times, \mathbb Z_2^\times)$ a squareclass of valuation
$h = \operatorname{ord}_2(S) = 1$, and $G_0$ a nondegenerate primitive ternary local genus with $\det_H(G_0) = \widetilde S$
(`Dyadic7.tildeTernary`). For $\varepsilon \in \{\pm1\}$ let $\widetilde M^{\varepsilon}(S) = \sum_G \beta(G_0)/\beta(G)$ over the
local genera $G$ with `G.IsGenStar S ε` (nondegenerate, primitive, $\det_H(G) = S$, Hasse invariant $c_2(G) = \varepsilon$).

**What is proved.** For $h = 1$ one has $\widetilde S = S\cdot 2^{1-h} = S$, and a squareclass of valuation
$1 = \operatorname{ord}_2(2)$ is *normalized* for $n = 3$ (Hanke 2011, Definition 4.1). By Theorem 2.6 at the dyadic primes
(`uniqueNormalizedLocalGenus_completion_dyadic`, proved), every nondegenerate primitive genus $G$ with $\det_H(G) = S$ equals
$G_0$. Hence the set of genera with `IsGenStar S ε` is $\{G_0\}$ if $c_2(G_0) = \varepsilon$ and $\emptyset$ otherwise, and
$\beta(G_0) \ne 0$ (the local self-density of a nondegenerate form is positive), so
$$\widetilde M^{+}(S) + \widetilde M^{-}(S) = 1,\qquad \widetilde M^{+}(S) - \widetilde M^{-}(S) = c_2(G_0) \in \{\pm1\}.$$
Table 5.3 at $h = 1$ (row 5, $\nu = -2$) gives `dyadicA 1` $= 1$ and `dyadicBmag 1` $= 4$, so these are exactly the
fields `A_eq` and `B_eq` of `DyadicTernaryLocalMassTable` restricted to $h = 1$:
`dyadicTernaryLocalMassTable_A_one` and `dyadicTernaryLocalMassTable_B_one`. Both are unconditional (no named input).

Indices are 0-based.
-/

open IsDedekindDomain NumberField

namespace QuadFormsKB.Dyadic7

open QuadFormsKB.Hanke2011Structure QuadFormsKB.Hanke2011Ternary

noncomputable section

/-! ### Arithmetic of $2$ in $\mathbb Q_2$ -/

/-- The prime ideal $v$ of $\mathbb Z$ containing $2$ does not contain $2$ to the second power: $\mathbb Q$ is unramified at $2$. -/
theorem two_not_mem_sq (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v.asIdeal ≠ ⊤) :
    (2 : 𝓞 ℚ) ∉ v.asIdeal ^ 2 := by
  intro h
  obtain ⟨π, hπ⟩ := (IsPrincipalIdealRing.principal v.asIdeal).principal
  rw [hπ, Ideal.submodule_span_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have hπu : ¬ IsUnit π := by
    intro hu
    apply hv
    rw [hπ, Ideal.submodule_span_eq]
    exact Ideal.span_singleton_eq_top.mpr hu
  have e1 : ((Rat.ringOfIntegersEquiv π) ^ 2) * Rat.ringOfIntegersEquiv c = 2 := by
    rw [← map_pow, ← map_mul, ← hc]; exact map_ofNat _ 2
  have hg : ¬ IsUnit (Rat.ringOfIntegersEquiv π) := fun hu => hπu ((MulEquiv.isUnit_map _).mp hu)
  have hd : (Rat.ringOfIntegersEquiv π).natAbs ^ 2 ∣ 2 := by
    have : (Rat.ringOfIntegersEquiv π) ^ 2 ∣ (2 : ℤ) := ⟨_, e1.symm⟩
    have := Int.natAbs_dvd_natAbs.mpr this
    simpa [Int.natAbs_pow] using this
  have hle := Nat.le_of_dvd (by norm_num) hd
  have h0 : (Rat.ringOfIntegersEquiv π).natAbs ≠ 0 := by
    intro h0
    rw [h0] at hd
    simp at hd
  have h1 : (Rat.ringOfIntegersEquiv π).natAbs ≠ 1 := by
    intro h1
    exact hg (Int.isUnit_iff_natAbs_eq.mpr h1)
  have : 2 ≤ (Rat.ringOfIntegersEquiv π).natAbs := by omega
  nlinarith

/-- **$\operatorname{ord}_2(2) = 1$ in $\mathbb Q_2$:** for the prime $v \mid 2$ of $\mathbb Q$, the class of $2$ has valuation $1$
(so `twoSqCl v` is a uniformizing class). -/
theorem localOrd_two (v : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) :
    localOrd v (Units.mk0 (algebraMap ℚ (v.adicCompletion ℚ) 2) (by simp)) = Multiplicative.ofAdd 1 := by
  have hv : v.asIdeal ≠ ⊤ := v.isPrime.ne_top
  have h1 : v.intValuation (2 : 𝓞 ℚ) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (v.intValuation_le_pow_iff_mem _ 1).mpr (by simpa using h2)
  have h2' : ¬ v.intValuation (2 : 𝓞 ℚ) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => two_not_mem_sq v hv ((v.intValuation_le_pow_iff_mem _ 2).mp h)
  have hvalQ : v.valuation ℚ (2 : ℚ) = v.intValuation (2 : 𝓞 ℚ) := by
    have := HeightOneSpectrum.valuation_of_algebraMap (K := ℚ) v (2 : 𝓞 ℚ)
    simpa only [map_ofNat] using this
  have hne : v.intValuation (2 : 𝓞 ℚ) ≠ 0 := by
    rw [← hvalQ]; exact (Valuation.ne_zero_iff _).mpr two_ne_zero
  have hval : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) 2) = v.intValuation (2 : 𝓞 ℚ) := by
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v (2 : 𝓞 ℚ)
    simp only [map_ofNat] at h ⊢
    rw [h, hvalQ]
  change Multiplicative.ofAdd (-WithZero.log (Valued.v (algebraMap ℚ (v.adicCompletion ℚ) 2))) = _
  rw [hval]
  have hk := WithZero.exp_log hne
  rw [← hk] at h1 h2'
  rw [WithZero.exp_le_exp] at h1 h2'
  have : WithZero.log (v.intValuation (2 : 𝓞 ℚ)) = -1 := by push_cast at h1 h2'; omega
  rw [this]; rfl

/-! ### Uniqueness of the genus of valuation $1$ -/

section Unique

variable (v : HeightOneSpectrum (𝓞 ℚ))

/-- For $\operatorname{ord}_2(S) = 1$ the normalization $\widetilde S = S \cdot 2^{1 - 1}$ is $S$. -/
theorem tildeTernary_of_ordZ_one {S : LocalSqCl v} (hS : SqCl.ordZ (localOrd v) (localUnits_le_ker v) S = 1) :
    tildeTernary v S = S := by
  unfold tildeTernary
  rw [hS]; simp

/-- **Theorem 2.6 at $p = 2$, $n = 3$, valuation $1$.** If $G_0, G$ are nondegenerate primitive ternary local genera over
$\mathbb Z_2$ with the same Hessian determinant squareclass $S$ of valuation $1 = \operatorname{ord}_2(2)$, then $G = G_0$. -/
@[kb "hanke2011ternary" "Thm. 4.12 / Table 5.3 row h = 1 (via Thm. 2.6 of Hanke 2011 structure paper, dyadic case)"]
theorem locGenus_eq_of_det_ordZ_one (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {S : LocalSqCl v}
    (hS : SqCl.ordZ (localOrd v) (localUnits_le_ker v) S = 1) (G₀ G : LocGenus v 3)
    (hn₀ : G₀.Nondeg) (hp₀ : G₀.Prim) (hd₀ : G₀.det = S) (hn : G.Nondeg) (hp : G.Prim) (hd : G.det = S) :
    G = G₀ := by
  obtain ⟨Q₀, hQ₀⟩ := Quotient.exists_rep G₀
  obtain ⟨Q, hQ⟩ := Quotient.exists_rep G
  have eG₀ : G₀ = LocGenus.mk Q₀ := hQ₀.symm
  have eG : G = LocGenus.mk Q := hQ.symm
  subst eG₀ eG
  have hne₀ : Q₀.hessian.det ≠ 0 := (LocGenus.nondeg_mk Q₀).mp hn₀
  have hne : Q.hessian.det ≠ 0 := (LocGenus.nondeg_mk Q).mp hn
  have hpr₀ : IsPrimitiveForm Q₀ := (LocGenus.prim_mk Q₀).mp hp₀
  have hpr : IsPrimitiveForm Q := (LocGenus.prim_mk Q).mp hp
  have hm₀ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) Q₀.hessian.det ≠ 0 :=
    algebraMap_ne_zero_iff.mpr hne₀
  have hm : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) Q.hessian.det ≠ 0 :=
    algebraMap_ne_zero_iff.mpr hne
  rw [LocGenus.det_mk, detSqForm_of_ne hm₀] at hd₀
  rw [LocGenus.det_mk, detSqForm_of_ne hm] at hd
  have hab : (SqCl.mk (Units.mk0 _ hm₀) : LocalSqCl v) = SqCl.mk (Units.mk0 _ hm) := hd₀.trans hd.symm
  -- the determinants agree up to a square of a unit
  obtain ⟨w, ⟨u0, hu0⟩, hwe⟩ := SqCl.exists_eq_mul_sq hab
  have hdetT : Q.hessian.det = (u0 : v.adicCompletionIntegers ℚ) ^ 2 * Q₀.hessian.det := by
    apply IsFractionRing.injective (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)
    have := congrArg Units.val hwe
    rw [Units.val_mul, Units.val_pow_eq_pow_val, ← hu0] at this
    change algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) Q.hessian.det =
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) Q₀.hessian.det *
        (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (u0 : v.adicCompletionIntegers ℚ)) ^ 2 at this
    rw [map_mul, map_pow, this, mul_comm]
  -- normalization: $\operatorname{ord}(\det_H Q_0) = \operatorname{ord}(2)$
  have hord : localOrd v (Units.mk0 _ hm₀) = Multiplicative.ofAdd 1 := by
    have : SqCl.ordZ (localOrd v) (localUnits_le_ker v) (SqCl.mk (Units.mk0 _ hm₀)) = 1 := hd₀ ▸ hS
    rw [SqCl.ordZ_mk] at this
    exact congrArg Multiplicative.ofAdd this
  have hquot : (Units.mk0 _ hm₀) * (Units.mk0 (algebraMap ℚ (v.adicCompletion ℚ) 2) (by simp))⁻¹ ∈ localUnits v := by
    rw [mem_localUnits_iff_ord, map_mul, map_inv, hord, localOrd_two v h2]
    simp
  obtain ⟨u1, hu1⟩ := hquot
  have hdet2 : Q₀.hessian.det = 2 * (u1 : v.adicCompletionIntegers ℚ) := by
    apply IsFractionRing.injective (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)
    have h := congrArg Units.val hu1
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0] at h
    have h2ne : (algebraMap ℚ (v.adicCompletion ℚ) 2) ≠ 0 := by simp
    have h' : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) Q₀.hessian.det =
        (Units.map (v.adicCompletionIntegers ℚ).subtype.toMonoidHom u1 : (v.adicCompletion ℚ)ˣ).val *
          algebraMap ℚ (v.adicCompletion ℚ) 2 := by
      rw [h, inv_mul_cancel_right₀ h2ne]
    simp only [map_ofNat, map_mul] at h' ⊢
    rw [h', mul_comm]
    rfl
  have hN : IsNormalizedHessian (v.adicCompletionIntegers ℚ) Q₀ := by
    unfold IsNormalizedHessian
    have : ¬ Even 3 := by decide
    simp only [this, ite_false]
    rw [IsDiscreteValuationRing.addVal_eq_iff_associated]
    exact ⟨u1⁻¹, by rw [hdet2, mul_assoc, Units.mul_inv, mul_one]⟩
  have hiso := (Dyadic.uniqueNormalizedLocalGenus_completion_dyadic v h2 3).unique Q₀ Q hpr₀ hpr hN u0 u0.isUnit hdetT
  exact LocGenus.mk_eq_mk.mpr hiso.symm

/-! ### The invariants of $G_0$ -/

/-- **The Hasse invariant of a local genus is $\pm 1$.** -/
theorem LocGenus.hasse_pm (G : LocGenus v 3) : G.hasse = 1 ∨ G.hasse = -1 := by
  obtain ⟨Q, hQ⟩ := Quotient.exists_rep G
  have e : G = LocGenus.mk Q := hQ.symm
  subst e
  rw [LocGenus.hasse_mk]
  exact Composition.hasseC_pm _

/-- **The local self-density of a nondegenerate genus is positive**, so $\beta(G) \ne 0$: Hanke's $\beta$ is
$\|2\|^{n(n-1)/2}\cdot\tfrac12\,\alpha_{\mathfrak p}(Q,Q)$ (`Hanke2005.hankeBeta_std_hessian`) and $\alpha_{\mathfrak p}(Q,Q) > 0$
(`Tamagawa.localDensityForm_self_pos'`). -/
theorem LocGenus.beta_pos (G : LocGenus v 3) (hG : G.Nondeg) : 0 < G.beta := by
  obtain ⟨Q, hQ⟩ := Quotient.exists_rep G
  have e : G = LocGenus.mk Q := hQ.symm
  subst e
  have hne : Q.hessian.det ≠ 0 := (LocGenus.nondeg_mk Q).mp hG
  have hpos := Tamagawa.localDensityForm_self_pos' v Q hne
  rw [LocGenus.beta_mk]
  unfold betaForm
  rw [Hanke2005.hankeBeta_std_hessian v Q hne]
  have h2 : (0 : ℝ) < ‖(2 : v.adicCompletion ℚ)‖ := norm_pos_iff.mpr two_ne_zero
  unfold LocalDensity.DVR.siegelDensity
  simp only [ite_true]
  exact mul_pos (pow_pos h2 _) (mul_pos (by norm_num) hpos)

/-! ### The two sums at $h = 1$ -/

variable {v}

/-- **The mass sum at $h = 1$:** $\widetilde M^{\varepsilon}(S) = 1$ if $c_2(G_0) = \varepsilon$ and $0$ otherwise. -/
theorem massSum_one (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {S : LocalSqCl v}
    (hS : SqCl.ordZ (localOrd v) (localUnits_le_ker v) S = 1) (G₀ : LocGenus v 3)
    (hn₀ : G₀.Nondeg) (hp₀ : G₀.Prim) (hd₀ : G₀.det = tildeTernary v S) (ε : ℤ) :
    (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S ε}, G₀.beta / G.beta) = if G₀.hasse = ε then 1 else 0 := by
  rw [tildeTernary_of_ordZ_one v hS] at hd₀
  have hb : G₀.beta ≠ 0 := (LocGenus.beta_pos v G₀ hn₀).ne'
  by_cases hε : G₀.hasse = ε
  · have : {G : LocGenus v 3 | G.IsGenStar S ε} = {G₀} := by
      ext G
      constructor
      · rintro ⟨hn, hp, hd, -⟩
        exact locGenus_eq_of_det_ordZ_one v h2 hS G₀ G hn₀ hp₀ hd₀ hn hp hd
      · rintro (rfl : G = G₀)
        exact ⟨hn₀, hp₀, hd₀, hε⟩
    rw [this, finsum_mem_singleton, div_self hb]
    simp [hε]
  · have : {G : LocGenus v 3 | G.IsGenStar S ε} = ∅ := by
      ext G
      constructor
      · rintro ⟨hn, hp, hd, hh⟩
        have := locGenus_eq_of_det_ordZ_one v h2 hS G₀ G hn₀ hp₀ hd₀ hn hp hd
        subst this
        exact absurd hh hε
      · intro h; exact h.elim
    rw [this, finsum_mem_empty]
    simp [hε]

/-! ### Table 5.3 at $h = 1$ -/

/-- Table 5.3, row $5$ ($\nu = -2$): $A^*_2 = 1$ at $h = 1$, i.e. `dyadicA 1 = 1`. -/
theorem dyadicA_one : dyadicA 1 = 1 := by
  norm_num [dyadicA, dyadicA4, single, family, family20, Finset.sum_range_succ]

/-- Table 5.3, row $5$ ($\nu = -2$): $|4B^*_2| = 4$ at $h = 1$, i.e. `dyadicBmag 1 = 4`. -/
theorem dyadicBmag_one : dyadicBmag 1 = 4 := by
  norm_num [dyadicBmag, single, family, family20, Finset.sum_range_succ]

/-- **Theorem 4.12 / Table 5.3, the row $h = 1$, field `A_eq`.** For $v$ the prime $2$ of $\mathbb Q$, $S$ of valuation $1$ and $G_0$ a
nondegenerate primitive ternary local genus with $\det_H(G_0) = \widetilde S$,
$\widetilde M^{+}(S) + \widetilde M^{-}(S) = A^*_2(S) = 1$ (`dyadicA 1`). Unconditional: the unique genus of Theorem 2.6 is $G_0$. -/
@[kb "hanke2011ternary" "Thm. 4.12 and Table 5.3, row h = 1 (unique genus, Thm. 2.6 of Hanke 2011 structure paper)"]
theorem dyadicTernaryLocalMassTable_A_one (v : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (S : LocalSqCl v) (G₀ : LocGenus v 3) (hS : SqCl.ordZ (localOrd v) (localUnits_le_ker v) S = 1)
    (hn₀ : G₀.Nondeg) (hp₀ : G₀.Prim) (hd₀ : G₀.det = tildeTernary v S) :
    (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S 1}, G₀.beta / G.beta) +
      (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S (-1)}, G₀.beta / G.beta) =
      ((dyadicA (SqCl.ordZ (localOrd v) (localUnits_le_ker v) S).toNat : ℚ) : ℝ) := by
  rw [massSum_one h2 hS G₀ hn₀ hp₀ hd₀, massSum_one h2 hS G₀ hn₀ hp₀ hd₀, hS]
  rcases LocGenus.hasse_pm v G₀ with h | h
  · simp [h, dyadicA_one]
  · simp [h, dyadicA_one]

/-- **Theorem 4.12 / Table 5.3, the row $h = 1$, field `B_eq`.** Under the same hypotheses,
$\widetilde M^{+}(S) - \widetilde M^{-}(S) = c_2(G_0)\cdot\tfrac14\cdot$`dyadicBmag 1` $= c_2(G_0)$. Unconditional. -/
@[kb "hanke2011ternary" "Thm. 4.12 and Table 5.3, row h = 1 (unique genus, Thm. 2.6 of Hanke 2011 structure paper)"]
theorem dyadicTernaryLocalMassTable_B_one (v : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (S : LocalSqCl v) (G₀ : LocGenus v 3) (hS : SqCl.ordZ (localOrd v) (localUnits_le_ker v) S = 1)
    (hn₀ : G₀.Nondeg) (hp₀ : G₀.Prim) (hd₀ : G₀.det = tildeTernary v S) :
    (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S 1}, G₀.beta / G.beta) -
      (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S (-1)}, G₀.beta / G.beta) =
      (G₀.hasse : ℝ) *
        ((dyadicBmag (SqCl.ordZ (localOrd v) (localUnits_le_ker v) S).toNat : ℚ) : ℝ) / 4 := by
  rw [massSum_one h2 hS G₀ hn₀ hp₀ hd₀, massSum_one h2 hS G₀ hn₀ hp₀ hd₀, hS]
  rcases LocGenus.hasse_pm v G₀ with h | h
  · simp [h, dyadicBmag_one]
  · simp [h, dyadicBmag_one]

end Unique

end

end QuadFormsKB.Dyadic7
