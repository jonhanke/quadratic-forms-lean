/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Odd7Beta

/-!
# Paper 7 at odd primes: Table 1 for the true local genera

For a place $v \nmid 2$ of $\mathbb Q$ ($p = p_v$) and a Jordan tuple $(a, b; u_1, u_2, u_3)$ of Lemma 2.1,
`invBeta_eq_normDensity` identifies the normalized density $(1 - p^{-2})/\beta_{G,v}(G)$ of the *true* local genus of
$u_1x^2 + p^au_2y^2 + p^bu_3z^2$ with paper 7's `normDensity` (Lemma 2.3, Table 1):

$$\frac{1 - p^{-2}}{\beta_{G,v}(G)} = (1 - p^{-2})\,\beta_{Q,p}(Q)^{-1}.$$

*Proof.* `Odd7Beta.invBeta_tupG` expresses the left side through Conway–Sloane's $p$-mass $m_p(\sigma)$ of the symbol
`symT a b u₁ u₂ u₃` (formula (3), proved at odd $p$). The $p$-mass is evaluated in the four shapes of the symbol
(Jordan types $(3)$, $(2,1)$, $(1,2)$, $(1,1,1)$) from Table 2 of Conway–Sloane (`Species.diagFactor`, the species
rule of Table 1 turning the sign of a binary block into $\varepsilon'\varepsilon_i\varepsilon_j$, $\varepsilon' =
\left(\frac{-1}{p}\right)$) and the cross-product exponent $2b$ (`crossExp_T`), and compared with the closed forms of
paper 7's Table 1 (`normDensity_case1` … `normDensity_case4`).

Indices are 0-based.
-/

open IsDedekindDomain NumberField Matrix Finset

namespace QuadFormsKB.Odd7

open QuadFormsKB.Hanke2011Structure QuadFormsKB.Hanke2011Ternary QuadFormsKB.ConwaySloane
  QuadFormsKB.ConwaySloane.Mass Cassels QuadFormsKB.HilbertLocal QuadFormsKB.Siegel QuadFormsKB.Tamagawa

noncomputable section

/-! ### The cross-product exponent of the symbol of a tuple -/

theorem cross_step (u w N : ℕ) (hw : w < N) :
    ∑ k' ∈ range N, ∑ k ∈ range k', (k' - k) * (if u = k then 1 else 0) * (if w = k' then 1 else 0) = w - u := by
  have h1 : ∀ k' : ℕ, ∑ k ∈ range k', (k' - k) * (if u = k then 1 else 0) = k' - u := by
    intro k'
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range]
    split_ifs with h <;> omega
  calc ∑ k' ∈ range N, ∑ k ∈ range k', (k' - k) * (if u = k then 1 else 0) * (if w = k' then 1 else 0)
      = ∑ k' ∈ range N, (if w = k' then (k' - u) else 0) := by
        refine Finset.sum_congr rfl fun k' _ => ?_
        rw [← Finset.sum_mul, h1]
        split_ifs <;> simp
    _ = w - u := by rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.2 hw)]

/-- **The cross-product exponent of the symbol of a tuple is $2b$:**
$\sum_{k<k'}(k'-k)n_kn_{k'} = a + b + (b - a) = 2b$ for the multiplicities $n_k = [0=k]+[a=k]+[b=k]$. -/
theorem crossExp_T {a b : ℕ} (hab : a ≤ b) (x y z : ℤˣ) :
    crossExp (fun k => (symT a b x y z k).dim) (b + 1) = 2 * b := by
  unfold crossExp
  show ∑ k' ∈ range (b + 1), ∑ k ∈ range k', (k' - k) *
      ((if 0 = k then 1 else 0) + (if a = k then 1 else 0) + (if b = k then 1 else 0)) *
      ((if 0 = k' then 1 else 0) + (if a = k' then 1 else 0) + (if b = k' then 1 else 0)) = 2 * b
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  rw [cross_step 0 0 (b + 1) (by omega), cross_step 0 a (b + 1) (by omega), cross_step 0 b (b + 1) (by omega),
    cross_step a 0 (b + 1) (by omega), cross_step a a (b + 1) (by omega), cross_step a b (b + 1) (by omega),
    cross_step b 0 (b + 1) (by omega), cross_step b a (b + 1) (by omega), cross_step b b (b + 1) (by omega)]
  omega

section Species

variable {p : ℕ} [hp : Fact p.Prime]

theorem lowerProd_zero' : lowerProd (p : ℚ) 0 = 1 := by simp [lowerProd]

theorem lowerProd_one' : lowerProd (p : ℚ) 1 = 1 - ((p : ℚ) ^ 2)⁻¹ := by simp [lowerProd]

theorem diagFactor_one (s : Sign) : (oddSpecies p ⟨1, s⟩).diagFactor p = 1 / 2 := by
  have h : Odd (1 : ℕ) := by decide
  simp [oddSpecies, Species.diagFactor, lowerProd_zero', h]

theorem diagFactor_three (s : Sign) :
    (oddSpecies p ⟨3, s⟩).diagFactor p = (2 * (1 - ((p : ℚ) ^ 2)⁻¹))⁻¹ := by
  have h : Odd (3 : ℕ) := by decide
  simp [oddSpecies, Species.diagFactor, lowerProd_one', h]

theorem diagFactor_two (hodd : p % 2 = 1) (w : ℤˣ) :
    (oddSpecies p ⟨2, if w = 1 then Sign.plus else Sign.minus⟩).diagFactor p =
      (2 * (1 - (((negOneChar p * w : ℤˣ) : ℤ) : ℚ) * (p : ℚ)⁻¹))⁻¹ := by
  have h : ¬ Odd (2 : ℕ) := by decide
  by_cases h3 : p % 4 = 3
  · have h1 : ¬ p % 4 = 1 := by omega
    rcases Int.units_eq_one_or w with rfl | rfl <;>
      simp [oddSpecies, Species.diagFactor, lowerProd_zero', h, h3, negOneChar, h1, Sign.flip, Sign.toInt]
  · have h1 : p % 4 = 1 := by omega
    rcases Int.units_eq_one_or w with rfl | rfl <;>
      simp [oddSpecies, Species.diagFactor, lowerProd_zero', h, h3, negOneChar, h1, Sign.flip, Sign.toInt]

theorem diagFactor_trivial : (oddSpecies p OddFactor.trivial).diagFactor p = 1 := by
  simp [oddSpecies, OddFactor.trivial, Species.diagFactor]

/-- The $p$-mass of the symbol of a tuple: diagonal product over the exponents $\{0, a, b\}$ times $p^b$. -/
theorem pMassOdd_symT {a b : ℕ} (hab : a ≤ b) (x y z : ℤˣ) :
    pMassOdd p (symT a b x y z) (b + 1) =
      ((∏ k ∈ ({0, a, b} : Finset ℕ), (oddSpecies p (symT a b x y z k)).diagFactor p : ℚ) : ℝ) * (p : ℝ) ^ b := by
  unfold pMassOdd
  have hprod : ∏ k ∈ range (b + 1), (oddSpecies p (symT a b x y z k)).diagFactor p =
      ∏ k ∈ ({0, a, b} : Finset ℕ), (oddSpecies p (symT a b x y z k)).diagFactor p := by
    symm
    refine Finset.prod_subset ?_ ?_
    · intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rw [Finset.mem_range]
      omega
    · intro k hk hnk
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnk
      have h : symT a b x y z k = OddFactor.trivial := by
        simp [symT, OddFactor.trivial, Ne.symm hnk.1, Ne.symm hnk.2.1, Ne.symm hnk.2.2]
      rw [h]
      exact diagFactor_trivial
  rw [hprod, crossExp_T hab, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]

end Species

/-! ### Real-number identities -/

theorem alg1 (q : ℝ) (hq : 1 < q) :
    2 * (1 - (q ^ 2)⁻¹) * ((2 * (1 - (q ^ 2)⁻¹))⁻¹ * 1) / 1 = 1 := by
  have h : 1 - (q ^ 2)⁻¹ ≠ 0 := by
    have : (q ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (by norm_num))
    linarith
  have hq0 : q ≠ 0 := by positivity
  have h' : q ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp

theorem alg2 (q t : ℝ) (hq : 1 < q) (ht : 0 < t) (χ : ℝ) (hχ : χ = 1 ∨ χ = -1) :
    2 * (1 - (q ^ 2)⁻¹) * ((2 * (1 - χ * q⁻¹))⁻¹ * (1 / 2) * t) / t ^ 2 = (1 + χ * q⁻¹) * t⁻¹ / 2 := by
  have hq0 : q ≠ 0 := by positivity
  have hq1 : q - 1 ≠ 0 := by linarith
  have hq2 : q + 1 ≠ 0 := by linarith
  have hq3 : 1 + q ≠ 0 := by linarith
  have ht0 : t ≠ 0 := ht.ne'
  have e : (q ^ 2 - 1) * (1 + q)⁻¹ = q - 1 := by
    rw [show q ^ 2 - 1 = (q - 1) * (1 + q) by ring, mul_assoc, mul_inv_cancel₀ hq3, mul_one]
  rcases hχ with rfl | rfl <;> field_simp <;> first | ring1 | linear_combination e

theorem alg3 (q t : ℝ) (hq : 1 < q) (ht : 0 < t) (χ : ℝ) (hχ : χ = 1 ∨ χ = -1) :
    2 * (1 - (q ^ 2)⁻¹) * ((1 / 2) * (2 * (1 - χ * q⁻¹))⁻¹ * t) / t ^ 4 = (1 + χ * q⁻¹) * (t⁻¹) ^ 3 / 2 := by
  have hq0 : q ≠ 0 := by positivity
  have hq1 : q - 1 ≠ 0 := by linarith
  have hq2 : q + 1 ≠ 0 := by linarith
  have hq3 : 1 + q ≠ 0 := by linarith
  have ht0 : t ≠ 0 := ht.ne'
  have e : (q ^ 2 - 1) * (1 + q)⁻¹ = q - 1 := by
    rw [show q ^ 2 - 1 = (q - 1) * (1 + q) by ring, mul_assoc, mul_inv_cancel₀ hq3, mul_one]
  rcases hχ with rfl | rfl <;> field_simp <;> first | ring1 | linear_combination e

theorem alg4 (q s t : ℝ) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t) :
    2 * (1 - (q ^ 2)⁻¹) * ((1 / 2 * (1 / 2 * (1 / 2))) * t) / (s ^ 2 * t ^ 2) =
      (1 - (q⁻¹) ^ 2) * (s⁻¹) ^ 2 * t⁻¹ / 4 := by
  have hq0 : q ≠ 0 := by positivity
  have hs0 : s ≠ 0 := hs.ne'
  have ht0 : t ≠ 0 := ht.ne'
  field_simp
  ring

section AtV

variable {v : HeightOneSpectrum (𝓞 ℚ)}

theorem cast_pv_gt_one : (1 : ℚ) < ((pv v : ℕ) : ℚ) := by
  exact_mod_cast (Fact.out : (pv v).Prime).one_lt

theorem cast_pv_gt_one_real : (1 : ℝ) < ((pv v : ℕ) : ℝ) := by
  exact_mod_cast (Fact.out : (pv v).Prime).one_lt

theorem chi_real (e : ℤˣ) : (((e : ℤ) : ℝ) = 1 ∨ ((e : ℤ) : ℝ) = -1) := by
  rcases Int.units_eq_one_or e with rfl | rfl <;> simp

/-- **Paper 7, Table 1 for the true local genera.** For $v \nmid 2$ and a Jordan tuple $(a, b; u_1, u_2, u_3)$
(constraints (1)–(3) of Lemma 2.1), the normalized density $(1 - p^{-2})/\beta_{G,v}(G)$ of the genus $G$ of
$u_1x^2 + p^au_2y^2 + p^bu_3z^2$ is paper 7's `normDensity` (`Hanke2011Ternary.normDensity`) with
$q = p$ and $\varepsilon' = \left(\frac{-1}{p}\right)$ (`negOneChar p`). Unconditional (Conway–Sloane's formula (3) is
proved at odd primes). -/
@[kb "hanke2011ternary" "§2, Lemma 2.3 and Thm. 2.4, Table 1, p. 6 (true local genera)"]
theorem invBeta_eq_normDensity (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal) {c : ℤ} (hc : jacobiSym c (pv v) = -1)
    {a b : ℕ} {e₁ e₂ e₃ : ℤˣ} (h : IsJordanTuple a b e₁ e₂ e₃) :
    (1 - (((pv v : ℕ) : ℝ) ^ 2)⁻¹) / (tupG v c a b e₁ e₂ e₃).beta =
      ((normDensity ((pv v : ℕ) : ℚ) (negOneChar (pv v)) a b e₁ e₂ e₃ : ℚ) : ℝ) := by
  have hp2 := pv_ne_two v hv
  have hodd : pv v % 2 = 1 := (Fact.out : (pv v).Prime).eq_two_or_odd.resolve_left hp2
  obtain ⟨hab, h1, h2, h3⟩ := h
  have hq := cast_pv_gt_one (v := v)
  have hqR := cast_pv_gt_one_real (v := v)
  rw [invBeta_tupG hp2 hc hab, pMassOdd_symT hab]
  rcases jordan_shape hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · -- shape (3): a = b = 0
    subst ha hb
    rw [normDensity_case1 hq]
    have hs : symT 0 0 e₁ e₂ e₃ 0 = ⟨3, if e₁ * e₂ * e₃ = 1 then Sign.plus else Sign.minus⟩ := by
      simp [symT]
    have hS : ({0, 0, 0} : Finset ℕ) = {0} := by ext; simp
    rw [hS, Finset.prod_singleton, hs, diagFactor_three]
    push_cast
    have := alg1 ((pv v : ℕ) : ℝ) hqR
    simpa using this
  · -- shape (2,1): a = 0 < b
    subst ha
    have hb0 : b ≠ 0 := by omega
    rw [normDensity_case2 hq _ _ _ _ hb0]
    have hS : ({0, 0, b} : Finset ℕ) = {0, b} := by ext; simp
    have hs0 : symT 0 b e₁ e₂ e₃ 0 = ⟨2, if e₁ * e₂ = 1 then Sign.plus else Sign.minus⟩ := by
      simp [symT, hb0]
    have hsb : symT 0 b e₁ e₂ e₃ b = ⟨1, if e₃ = 1 then Sign.plus else Sign.minus⟩ := by
      simp [symT, hb0, Ne.symm hb0]
    rw [hS, Finset.prod_pair (Ne.symm hb0), hs0, hsb, diagFactor_two hodd, diagFactor_one]
    have := alg2 ((pv v : ℕ) : ℝ) (((pv v : ℕ) : ℝ) ^ b) hqR (pow_pos (by linarith) _)
      (((negOneChar (pv v) * (e₁ * e₂) : ℤˣ) : ℤ) : ℝ) (chi_real _)
    refine Eq.trans (Eq.trans ?_ this) ?_
    · push_cast; ring
    · push_cast; ring
  · -- shape (1,2): 0 < a = b
    subst hb
    have ha0 : a ≠ 0 := by omega
    rw [normDensity_case3 hq _ _ _ _ ha0]
    have hS : ({0, a, a} : Finset ℕ) = {0, a} := by ext; simp
    have hs0 : symT a a e₁ e₂ e₃ 0 = ⟨1, if e₁ = 1 then Sign.plus else Sign.minus⟩ := by
      simp [symT, ha0, Ne.symm ha0]
    have hsa : symT a a e₁ e₂ e₃ a = ⟨2, if e₂ * e₃ = 1 then Sign.plus else Sign.minus⟩ := by
      simp [symT, ha0, Ne.symm ha0]
    rw [hS, Finset.prod_pair (Ne.symm ha0), hs0, hsa, diagFactor_two hodd, diagFactor_one]
    have := alg3 ((pv v : ℕ) : ℝ) (((pv v : ℕ) : ℝ) ^ a) hqR (pow_pos (by linarith) _)
      (((negOneChar (pv v) * (e₂ * e₃) : ℤˣ) : ℤ) : ℝ) (chi_real _)
    refine Eq.trans (Eq.trans ?_ this) ?_
    · push_cast; ring
    · push_cast; ring
  · -- shape (1,1,1): 0 < a < b
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have hab' : a ≠ b := by omega
    rw [normDensity_case4 hq _ _ _ _ ha0 (by omega)]
    have hs0 : symT a b e₁ e₂ e₃ 0 = ⟨1, if e₁ = 1 then Sign.plus else Sign.minus⟩ := by
      simp [symT, ha0, hb0, Ne.symm ha0, Ne.symm hb0]
    have hsa : symT a b e₁ e₂ e₃ a = ⟨1, if e₂ = 1 then Sign.plus else Sign.minus⟩ := by
      simp [symT, ha0, hab', Ne.symm ha0, Ne.symm hab']
    have hsb : symT a b e₁ e₂ e₃ b = ⟨1, if e₃ = 1 then Sign.plus else Sign.minus⟩ := by
      simp [symT, hb0, hab', Ne.symm hb0, Ne.symm hab']
    rw [Finset.prod_insert (by simp [Ne.symm ha0, Ne.symm hb0]), Finset.prod_pair hab', hs0, hsa, hsb,
      diagFactor_one, diagFactor_one, diagFactor_one]
    have := alg4 ((pv v : ℕ) : ℝ) (((pv v : ℕ) : ℝ) ^ a) (((pv v : ℕ) : ℝ) ^ b) hqR (pow_pos (by linarith) _)
      (pow_pos (by linarith) _)
    refine Eq.trans (Eq.trans ?_ this) ?_
    · push_cast; ring
    · push_cast; ring

end AtV

end

end QuadFormsKB.Odd7
