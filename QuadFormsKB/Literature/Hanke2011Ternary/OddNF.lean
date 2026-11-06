/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.Hanke2011Structure.RationalityNondyadicFamilyGlobal
import QuadFormsKB.Literature.Hanke2011Ternary.GlobalNF
import QuadFormsKB.Literature.Hanke2011Ternary.OddPrimes

/-!
# Paper 7 at odd primes of a number field: the true local mass sums are $A^*_{\mathfrak p}$ and $B^*_{\mathfrak p}$

J. Hanke, *Explicit formulas for masses of ternary quadratic lattices of varying determinant over number fields*,
arXiv:1109.1054 (`hanke2011ternary`), §2, Lemmas 2.1–2.3, Thm. 2.4, Tables 1–2, pp. 4–7.

This is the number-field version of `Odd7.odd_finite`, `odd_A`, `odd_B`, `odd_unimodular`.  Let $F$ be a number field,
$\mathfrak p$ (`v`) a finite prime with $2 \notin \mathfrak p$, $q = N\mathfrak p$ (`qv v`) and
$\varepsilon' = \left(\frac{-1}{\mathfrak p}\right)$ (`epsOdd v`).  For a tuple $(a, b; u_1, u_2, u_3)$ of Lemma 2.1
(`IsJordanTuple`) let `tupNF v c a b e₁ e₂ e₃` be the local genus of the diagonal form
$\operatorname{diag}(\operatorname{rep}(u_1), \pi^a\operatorname{rep}(u_2), \pi^b\operatorname{rep}(u_3))$, i.e. `RatND.genND`
at the exponents $(0, a, b)$ (here $\operatorname{rep}(\pm1)$ is $1$, resp. a fixed unit $c$ with nonsquare residue).
We prove, for every number field and every such $\mathfrak p$:

* `beta_tupNF`: $(1 - q^{-2})/\beta(G) = $ paper 7's `normDensity` (Table 1), from `RatND.beta_genND` and the weight of
  the four shapes of the symbol (Jordan types $(3)$, $(2,1)$, $(1,2)$, $(1,1,1)$);
* `hasse_tupNF`: the Hasse invariant is `oddHasse` (Lemma 2.2), from `RatND.hasse_genND`;
* `det_tupNF_iff`: the determinant class (from `RatND.det_genND_iff`);
* `exists_tupNF`, `tupNF_inj`: every nondegenerate primitive ternary genus is the genus of exactly one Jordan tuple
  (Lemma 2.1);
* `oddNF_finite`, `oddNF_A`, `oddNF_B`, `oddNF_unimod`: the four odd fields of the named input
  `TernaryLocalTablesNF` of `Hanke2011Structure.TernaryNF`.

All unconditional.  Indices are 0-based.
-/

open Finset Matrix IsDedekindDomain NumberField

namespace QuadFormsKB.Hanke2011Ternary.OddNF

open QuadFormsKB QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.Hanke2011Structure
  QuadFormsKB.Hanke2011Structure.RatOdd QuadFormsKB.Hanke2011Structure.RatND QuadFormsKB.ConwaySloane
  QuadFormsKB.Odd7 QuadFormsKB.Hanke2011Ternary QuadFormsKB.Hanke2011Ternary.NF

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

/-! ### Symbols with gaps -/

/-- The sign $+$ or $-$ of a unit $\pm1$. -/
def sg (P : ℤˣ) : Sign := if P = 1 then Sign.plus else Sign.minus

theorem signU_sg (P : ℤˣ) : signU (sg P) = P := by
  rcases Int.units_eq_one_or P with rfl | rfl <;> simp [sg, signU]

/-- The symbol $\sigma$ shifted up by $m$ scales, with trivial factors at the scales $0, \dots, m-1$. -/
def padS (m : ℕ) (σ : OddSymbol) : OddSymbol := fun k => if k < m then OddFactor.trivial else σ (k - m)

theorem consS_apply (f : OddFactor) (σ : OddSymbol) (k : ℕ) : consS f σ k = if k = 0 then f else σ (k - 1) := by
  cases k <;> simp

theorem padS_zero (σ : OddSymbol) : padS 0 σ = σ := by
  funext k; simp [padS]

theorem padS_succ (m : ℕ) (σ : OddSymbol) : padS (m + 1) σ = consS OddFactor.trivial (padS m σ) := by
  funext k
  cases k with
  | zero => simp [padS, consS]
  | succ k => simp [padS, consS]

theorem finSupp_triv : FinSupp triv := ⟨0, triv_trivFrom⟩

theorem finSupp_padS (m : ℕ) {σ : OddSymbol} (h : FinSupp σ) : FinSupp (padS m σ) := by
  induction m with
  | zero => rwa [padS_zero]
  | succ m ih => rw [padS_succ, finSupp_cons]; exact ih

theorem rkC_triv : rkC triv = 0 := by
  unfold rkC
  rw [stable_rk.cut_eq triv_trivFrom]
  simp [rk]

theorem rkC_single (f : OddFactor) : rkC (consS f triv) = f.dim := by
  rw [rkC_cons finSupp_triv, rkC_triv, add_zero]

theorem rkC_padS (m : ℕ) {σ : OddSymbol} (h : FinSupp σ) : rkC (padS m σ) = rkC σ := by
  induction m with
  | zero => rw [padS_zero]
  | succ m ih => rw [padS_succ, rkC_cons (finSupp_padS m h), ih]; exact Nat.zero_add _

section Weights

variable (M : ℕ → Sign → ℝ) (A : ℕ → ℝ) (hM : M 0 Sign.plus = 1) (ha : A 0 = 1)
include hM ha

theorem wtC_triv' : wtC M A triv = 1 := wtC_triv_from_zero M A hM ha triv_trivFrom

theorem wtC_single (f : OddFactor) : wtC M A (consS f triv) = M f.dim f.sign := by
  rw [wtC_cons M A hM ha finSupp_triv, rkC_triv, ha, wtC_triv' M A hM ha]
  ring

theorem wtC_padS (m : ℕ) {σ : OddSymbol} (h : FinSupp σ) :
    wtC M A (padS m σ) = A (rkC σ) ^ m * wtC M A σ := by
  induction m with
  | zero => rw [padS_zero]; simp
  | succ m ih =>
    rw [padS_succ, wtC_cons M A hM ha (finSupp_padS m h), rkC_padS m h, ih]
    have : M (OddFactor.trivial).dim (OddFactor.trivial).sign = 1 := hM
    rw [this]
    ring

end Weights

/-! ### The four shapes of the symbol of a tuple -/

theorem symT_1 (x y z : ℤˣ) : symT 0 0 x y z = consS ⟨3, sg (x * y * z)⟩ triv := by
  funext k
  cases k with
  | zero => simp [symT, consS, sg]
  | succ k => simp [symT, consS, triv, OddFactor.trivial]

theorem symT_2 (m : ℕ) (x y z : ℤˣ) :
    symT 0 (m + 1) x y z = consS ⟨2, sg (x * y)⟩ (padS m (consS ⟨1, sg z⟩ triv)) := by
  funext k
  simp only [symT, consS_apply, padS, triv, OddFactor.trivial, sg]
  split_ifs <;> simp_all <;> omega

theorem symT_3 (m : ℕ) (x y z : ℤˣ) :
    symT (m + 1) (m + 1) x y z = consS ⟨1, sg x⟩ (padS m (consS ⟨2, sg (y * z)⟩ triv)) := by
  funext k
  simp only [symT, consS_apply, padS, triv, OddFactor.trivial, sg]
  split_ifs <;> simp_all <;> omega

theorem symT_4 (i j : ℕ) (x y z : ℤˣ) :
    symT (i + 1) (i + j + 2) x y z =
      consS ⟨1, sg x⟩ (padS i (consS ⟨1, sg y⟩ (padS j (consS ⟨1, sg z⟩ triv)))) := by
  funext k
  simp only [symT, consS_apply, padS, triv, OddFactor.trivial, sg]
  split_ifs <;> simp_all <;> omega

section WeightShapes

variable (M : ℕ → Sign → ℝ) (A : ℕ → ℝ) (hM : M 0 Sign.plus = 1) (ha : A 0 = 1)
include hM ha

theorem wtC_s1 (x y z : ℤˣ) : wtC M A (symT 0 0 x y z) = M 3 (sg (x * y * z)) := by
  rw [symT_1, wtC_single M A hM ha]

theorem wtC_s2 (m : ℕ) (x y z : ℤˣ) :
    wtC M A (symT 0 (m + 1) x y z) = M 2 (sg (x * y)) * M 1 (sg z) * A 1 ^ (m + 1) := by
  have h1 : FinSupp (consS (⟨1, sg z⟩ : OddFactor) triv) := (finSupp_cons _).2 finSupp_triv
  rw [symT_2, wtC_cons M A hM ha (finSupp_padS m h1), rkC_padS m h1, rkC_single, wtC_padS M A hM ha m h1,
    rkC_single, wtC_single M A hM ha]
  dsimp only
  ring

theorem wtC_s3 (m : ℕ) (x y z : ℤˣ) :
    wtC M A (symT (m + 1) (m + 1) x y z) = M 1 (sg x) * M 2 (sg (y * z)) * A 2 ^ (m + 1) := by
  have h1 : FinSupp (consS (⟨2, sg (y * z)⟩ : OddFactor) triv) := (finSupp_cons _).2 finSupp_triv
  rw [symT_3, wtC_cons M A hM ha (finSupp_padS m h1), rkC_padS m h1, rkC_single, wtC_padS M A hM ha m h1,
    rkC_single, wtC_single M A hM ha]
  dsimp only
  ring

theorem wtC_s4 (i j : ℕ) (x y z : ℤˣ) :
    wtC M A (symT (i + 1) (i + j + 2) x y z) =
      M 1 (sg x) * M 1 (sg y) * M 1 (sg z) * A 2 ^ (i + 1) * A 1 ^ (j + 1) := by
  have h3 : FinSupp (consS (⟨1, sg z⟩ : OddFactor) triv) := (finSupp_cons _).2 finSupp_triv
  have hQ : FinSupp (padS j (consS (⟨1, sg z⟩ : OddFactor) triv)) := finSupp_padS j h3
  have h2 : FinSupp (consS (⟨1, sg y⟩ : OddFactor) (padS j (consS (⟨1, sg z⟩ : OddFactor) triv))) :=
    (finSupp_cons _).2 hQ
  have hR : FinSupp (padS i (consS (⟨1, sg y⟩ : OddFactor) (padS j (consS (⟨1, sg z⟩ : OddFactor) triv)))) :=
    finSupp_padS i h2
  have rQ : rkC (padS j (consS (⟨1, sg z⟩ : OddFactor) triv)) = 1 := by rw [rkC_padS j h3, rkC_single]
  have r2 : rkC (consS (⟨1, sg y⟩ : OddFactor) (padS j (consS (⟨1, sg z⟩ : OddFactor) triv))) = 2 := by
    rw [rkC_cons hQ, rQ]
  rw [symT_4, wtC_cons M A hM ha hR, rkC_padS i h2, r2, wtC_padS M A hM ha i h2, r2,
    wtC_cons M A hM ha hQ, rQ, wtC_padS M A hM ha j h3, rkC_single, wtC_single M A hM ha]
  dsimp only
  ring

end WeightShapes

/-! ### The weights at the four shapes -/

theorem Mq_three (q : ℕ) (e : ℤˣ) (s : Sign) : Mq q e 3 s = (2 * (1 - ((q : ℝ) ^ 2)⁻¹))⁻¹ := by
  simp [Mq, Pq]

theorem Mq_one (q : ℕ) (e : ℤˣ) (s : Sign) : Mq q e 1 s = 2⁻¹ := by
  simp [Mq, Pq]

theorem Mq_two (q : ℕ) (e : ℤˣ) (s : Sign) :
    Mq q e 2 s = (2 * (1 - (((e * signU s : ℤˣ) : ℤ) : ℝ) * (q : ℝ)⁻¹))⁻¹ := by
  simp [Mq, Pq]

theorem aq_one (q : ℕ) : aq q 1 = (q : ℝ)⁻¹ := by
  simp [aq]

theorem aq_two (q : ℕ) : aq q 2 = ((q : ℝ) ^ 3)⁻¹ := by
  simp [aq]

theorem chi_real (e : ℤˣ) : (((e : ℤ) : ℝ) = 1 ∨ ((e : ℤ) : ℝ) = -1) := by
  rcases Int.units_eq_one_or e with rfl | rfl <;> simp

theorem alg1 (t : ℝ) (ht : 1 < t) : (1 - (t ^ 2)⁻¹) * (2 * (2 * (1 - (t ^ 2)⁻¹))⁻¹) = 1 := by
  have h : 1 - (t ^ 2)⁻¹ ≠ 0 := by
    have : (t ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ ht (by norm_num))
    linarith
  have h' : t ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp

theorem alg2 (t χ r : ℝ) (ht : 1 < t) (hχ : χ = 1 ∨ χ = -1) :
    (1 - (t ^ 2)⁻¹) * (2 * ((2 * (1 - χ * t⁻¹))⁻¹ * 2⁻¹ * r)) = (1 + χ * t⁻¹) * r / 2 := by
  have t0 : t ≠ 0 := by positivity
  have h1 : t - 1 ≠ 0 := by linarith
  have h2 : t + 1 ≠ 0 := by linarith
  have h3 : 1 + t ≠ 0 := by linarith
  have e : (t ^ 2 - 1) * (1 + t)⁻¹ = t - 1 := by
    rw [show t ^ 2 - 1 = (t - 1) * (1 + t) by ring, mul_assoc, mul_inv_cancel₀ h3, mul_one]
  rcases hχ with rfl | rfl <;> field_simp <;> first | ring1 | linear_combination r * e

theorem alg4 (t r : ℝ) (ht : 1 < t) :
    (1 - (t ^ 2)⁻¹) * (2 * (2⁻¹ * 2⁻¹ * 2⁻¹ * r)) = (1 - t⁻¹ ^ 2) * r / 4 := by
  have t0 : t ≠ 0 := by positivity
  field_simp
  ring

/-- **Table 1 in terms of weights**: for every Jordan tuple, $(1 - q^{-2})\cdot 2\,\mathrm{wt}(\operatorname{symT})$
is paper 7's `normDensity` (generic in the residue field size $q$ and $\varepsilon'$). -/
theorem dens_eq {q : ℕ} (hq : 1 < (q : ℚ)) (e : ℤˣ) {a b : ℕ} {x y z : ℤˣ} (h : IsJordanTuple a b x y z) :
    (1 - ((q : ℝ) ^ 2)⁻¹) * (2 * wtC (Mq q e) (aq q) (symT a b x y z)) =
      ((normDensity (q : ℚ) e a b x y z : ℚ) : ℝ) := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hM : Mq q e 0 Sign.plus = 1 := Mq_zero _ _
  have ha : aq q 0 = 1 := aq_zero _
  obtain ⟨hab, h1, h2, h3⟩ := h
  rcases jordan_shape hab with ⟨ha0, hb0⟩ | ⟨ha0, hb0⟩ | ⟨ha0, hb0⟩ | ⟨ha0, hb0⟩
  · subst ha0 hb0
    rw [wtC_s1 _ _ hM ha, normDensity_case1 hq, Mq_three]
    simpa using alg1 _ hqR
  · subst ha0
    obtain ⟨m, rfl⟩ : ∃ m, b = m + 1 := ⟨b - 1, by omega⟩
    rw [wtC_s2 _ _ hM ha, normDensity_case2 hq _ _ _ _ (by omega), Mq_two, Mq_one, aq_one, signU_sg]
    have := alg2 (q : ℝ) (((e * x * y : ℤˣ) : ℤ) : ℝ) (((q : ℝ)⁻¹) ^ (m + 1)) hqR (chi_real _)
    push_cast at this ⊢
    linear_combination this
  · subst hb0
    obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
    rw [wtC_s3 _ _ hM ha, normDensity_case3 hq _ _ _ _ (by omega), Mq_two, Mq_one, aq_two, signU_sg]
    have hr : (((q : ℝ) ^ 3)⁻¹) ^ (m + 1) = ((q : ℝ)⁻¹) ^ (3 * (m + 1)) := by
      rw [pow_mul, ← inv_pow (q : ℝ) 3]
    have := alg2 (q : ℝ) (((e * y * z : ℤˣ) : ℤ) : ℝ) ((((q : ℝ) ^ 3)⁻¹) ^ (m + 1)) hqR (chi_real _)
    push_cast at this ⊢
    rw [← hr]
    linear_combination this
  · obtain ⟨i, rfl⟩ : ∃ i, a = i + 1 := ⟨a - 1, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ j, b = i + j + 2 := ⟨b - i - 2, by omega⟩
    rw [wtC_s4 _ _ hM ha, normDensity_case4 hq _ _ _ _ (by omega) (by omega), aq_one, aq_two]
    simp only [Mq_one]
    have hr : (((q : ℝ) ^ 3)⁻¹) ^ (i + 1) * ((q : ℝ)⁻¹) ^ (j + 1) =
        ((q : ℝ)⁻¹) ^ (2 * (i + 1) + (i + j + 2)) := by
      rw [← inv_pow (q : ℝ) 3, ← pow_mul, ← pow_add]
      congr 1
      ring
    have := alg4 (q : ℝ) ((((q : ℝ) ^ 3)⁻¹) ^ (i + 1) * ((q : ℝ)⁻¹) ^ (j + 1)) hqR
    push_cast at this ⊢
    rw [← hr]
    linear_combination this

/-! ### The genus of a tuple -/

section NF

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "ordS" w => SqCl.ordZ (localOrd w) (localUnits_le_ker w)

variable (v) in
/-- **The local genus of the tuple** $(a, b; u_1, u_2, u_3)$: the genus of
$\operatorname{diag}(\operatorname{rep}(u_1), \pi^a\operatorname{rep}(u_2), \pi^b\operatorname{rep}(u_3))$ over
$\mathcal O_{\mathfrak p}$, where $\operatorname{rep}(1) = 1$ and $\operatorname{rep}(-1) = c$ (a unit with nonsquare residue). -/
def tupNF (c : 𝔬) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) : LocGenus v 3 := genND v c ![0, a, b] ![e₁, e₂, e₃]

/-- **$\chi(-1) = \left(\frac{-1}{\mathfrak p}\right)$**: the sign of $-1$ in the residue field of $\mathcal O_{\mathfrak p}$ is
`epsOdd v` (it is $+1$ iff $N\mathfrak p \equiv 1 \pmod 4$). -/
theorem sgn_neg_one_eq (hv : (2 : 𝓞 F) ∉ v.asIdeal) : sgn 𝔬 (-1 : 𝔬) = epsOdd v := by
  have h2' := not_dvd_two_nf v hv
  have hch := DVR.ringChar_residueField_ne_two (LocalDensity.NF.irreducible_π v) h2'
  have hcard : Fintype.card (IsLocalRing.ResidueField 𝔬) = qv v := by
    have := LocalDensity.NF.q_completion (v := v)
    unfold DVR.q at this
    rw [← Nat.card_eq_fintype_card]
    exact this
  have hodd := FiniteField.odd_card_of_char_ne_two hch
  rw [hcard] at hodd
  have hodd' : qv v % 2 = 1 := hodd
  apply Units.ext
  rw [sgn_neg_one_val]
  by_cases h4 : qv v % 4 = 1
  · have hsq : IsSquare (-1 : IsLocalRing.ResidueField 𝔬) :=
      FiniteField.isSquare_neg_one_iff.2 (by rw [hcard]; omega)
    rw [(quadraticChar_one_iff_isSquare (neg_ne_zero.2 one_ne_zero)).2 hsq]
    simp [epsOdd, negOneChar, h4]
  · have h3 : qv v % 4 = 3 := by omega
    have hsq : ¬ IsSquare (-1 : IsLocalRing.ResidueField 𝔬) := by
      rw [FiniteField.isSquare_neg_one_iff, hcard]; omega
    rw [quadraticChar_neg_one_iff_not_isSquare.2 hsq]
    simp [epsOdd, negOneChar, h4]

/-- **Paper 7, Table 1 for the true local genera over $F$** (Lemma 2.3).  For $\mathfrak p \nmid 2$ and a Jordan tuple
$(a, b; u_1, u_2, u_3)$ the normalized density $(1 - q^{-2})/\beta(G)$ of the genus of
$u_1x^2 + \pi^au_2y^2 + \pi^bu_3z^2$ is paper 7's `normDensity` with $q = N\mathfrak p$, $\varepsilon' =
\left(\frac{-1}{\mathfrak p}\right)$.  Unconditional (every number field). -/
@[kb "hanke2011ternary" "§2, Lemma 2.3 and Thm. 2.4, Table 1, p. 6 (true local genera over F_p, p ∤ 2)"]
theorem beta_tupNF (c : 𝔬) (hcU : IsUnit c) (hc : chiR c = -1) (hv : (2 : 𝓞 F) ∉ v.asIdeal) {a b : ℕ} {e₁ e₂ e₃ : ℤˣ} (h : IsJordanTuple a b e₁ e₂ e₃) :
    (1 - ((qv v : ℝ) ^ 2)⁻¹) / (tupNF v c a b e₁ e₂ e₃).beta =
      ((normDensity (qv v : ℚ) (epsOdd v) a b e₁ e₂ e₃ : ℚ) : ℝ) := by
  unfold tupNF
  rw [beta_genND hv hcU hc, div_inv_eq_mul, symC_three, LocalDensity.NF.q_completion (v := v),
    sgn_neg_one_eq hv]
  exact dens_eq (q := qv v) (one_lt_qv_rat v) (epsOdd v) h

/-- **Lemma 2.2 for the true local genera over $F$**: the Hasse invariant of the genus of the tuple is
`oddHasse`. -/
@[kb "hanke2011ternary" "§2, Lemma 2.2, p. 5 (true local genera over F_p, p ∤ 2)"]
theorem hasse_tupNF (c : 𝔬) (hcU : IsUnit c) (hc : chiR c = -1) (hv : (2 : 𝓞 F) ∉ v.asIdeal) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) :
    (tupNF v c a b e₁ e₂ e₃).hasse = ((oddHasse (epsOdd v) a b e₁ e₂ e₃ : ℤˣ) : ℤ) := by
  unfold tupNF
  rw [hasse_genND hv hcU hc, sgn_neg_one_eq hv]
  congr 1
  simp only [hasseZ, hp, oddHasse, Fin.prod_univ_three]
  simp [pow_add]
  ac_rfl

theorem nondeg_tupNF (c : 𝔬) (hcU : IsUnit c) (hv : (2 : 𝓞 F) ∉ v.asIdeal) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) :
    (tupNF v c a b e₁ e₂ e₃).Nondeg := nondeg_genND hv hcU _ _

theorem prim_tupNF (c : 𝔬) (hcU : IsUnit c) (hv : (2 : 𝓞 F) ∉ v.asIdeal) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) :
    (tupNF v c a b e₁ e₂ e₃).Prim := (prim_genND_iff hv hcU _ _).2 ⟨0, rfl⟩

theorem det_tupNF_iff (c : 𝔬) (hcU : IsUnit c) (hc : chiR c = -1) (hv : (2 : 𝓞 F) ∉ v.asIdeal) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) {w : 𝔬} (hw : IsUnit w) (ν : ℕ) :
    (tupNF v c a b e₁ e₂ e₃).det = sqNF (LocalDensity.NF.π v ^ ν * w) ↔
      a + b = ν ∧ e₁ * e₂ * e₃ = sgn 𝔬 (2 : 𝔬) ^ 3 * sgn 𝔬 w := by
  unfold tupNF
  rw [det_genND_iff hv hcU hc _ _ hw]
  simp [Fin.sum_univ_three, Fin.prod_univ_three]

/-- **Lemma 2.1 (existence), for the true local genera over $F$**: every nondegenerate primitive ternary local genus at
$\mathfrak p \nmid 2$ is the genus of a Jordan tuple. -/
@[kb "hanke2011ternary" "§2, Lemma 2.1, pp. 4–5 (genera as tuples, over F_p, p ∤ 2)"]
theorem exists_tupNF (c : 𝔬) (hcU : IsUnit c) (hc : chiR c = -1) (hv : (2 : 𝓞 F) ∉ v.asIdeal) (G : LocGenus v 3) (hN : G.Nondeg) (hP : G.Prim) :
    ∃ a b e₁ e₂ e₃, IsJordanTuple a b e₁ e₂ e₃ ∧ G = tupNF v c a b e₁ e₂ e₃ := by
  obtain ⟨z, x, rfl⟩ := exists_genND hv hcU hc G hN
  obtain ⟨i0, hi0⟩ := (prim_genND_iff hv hcU z x).1 hP
  set s : Equiv.Perm (Fin 3) := Tuple.sort z with hs
  have hmono : Monotone (fun i => z (s i)) := Tuple.monotone_sort z
  have hz0 : z (s 0) = 0 := by
    have h1 : z (s 0) ≤ z (s (s.symm i0)) := hmono (Fin.zero_le _)
    rw [Equiv.apply_symm_apply, hi0] at h1
    omega
  set a : ℕ := z (s 1) with ha
  set b : ℕ := z (s 2) with hb
  have hab : a ≤ b := hmono (by decide : (1 : Fin 3) ≤ 2)
  have hzfun : (fun i => z (s i)) = ![0, a, b] := by
    funext i
    fin_cases i <;> simp [ha, hb, hz0]
  set x0 : ℤˣ := x (s 0) with hx0
  set x1 : ℤˣ := x (s 1) with hx1
  set x2 : ℤˣ := x (s 2) with hx2
  have e1 : (fun i => x (s i)) = ![x0, x1, x2] := by
    funext i
    fin_cases i <;> rfl
  have hperm : symC (fun i => z (s i)) (fun i => x (s i)) = symC z x := symC_perm z x s
  rw [hzfun, e1, symC_three] at hperm
  refine ⟨a, b, (normT a b x0 x1 x2).1, (normT a b x0 x1 x2).2.1, (normT a b x0 x1 x2).2.2,
    isJordanTuple_normT hab _ _ _, ?_⟩
  unfold tupNF
  rw [genND_eq_iff hv hcU hc, symC_three, ← hperm]
  exact symT_normT a b x0 x1 x2

/-- **Lemma 2.1 (uniqueness), for the true local genera over $F$**: distinct Jordan tuples give distinct genera. -/
@[kb "hanke2011ternary" "§2, Lemma 2.1, pp. 4–5 (distinct tuples, distinct genera, over F_p, p ∤ 2)"]
theorem tupNF_inj (c : 𝔬) (hcU : IsUnit c) (hc : chiR c = -1) (hv : (2 : 𝓞 F) ∉ v.asIdeal) {a b a' b' : ℕ} {e₁ e₂ e₃ e₁' e₂' e₃' : ℤˣ}
    (h : IsJordanTuple a b e₁ e₂ e₃) (h' : IsJordanTuple a' b' e₁' e₂' e₃')
    (hg : tupNF v c a b e₁ e₂ e₃ = tupNF v c a' b' e₁' e₂' e₃') :
    a = a' ∧ b = b' ∧ e₁ = e₁' ∧ e₂ = e₂' ∧ e₃ = e₃' := by
  unfold tupNF at hg
  rw [genND_eq_iff hv hcU hc, symC_three, symC_three] at hg
  exact symT_inj h h' hg

/-- A squareclass of valuation $n \in \mathbb N$ is $[\pi^nw]$ for a unit $w$. -/
theorem exists_sqNF_of_ordS (S : LocalSqCl v) (n : ℕ) (hS : (ordS v) S = n) :
    ∃ w : 𝔬, IsUnit w ∧ S = sqNF (LocalDensity.NF.π v ^ n * w) := by
  have hπ := LocalDensity.NF.irreducible_π v
  have ht : SqCl.ordZ (localOrd v) (localUnits_le_ker v)
      (S * (sqNF (LocalDensity.NF.π v) : LocalSqCl v) ^ (-(n : ℤ))) = 0 := by
    rw [SqCl.ordZ_mul, SqCl.ordZ_zpow, hS, ordZ_sqNF_pi]
    ring
  obtain ⟨w, hw, hut⟩ := exists_unit_of_ordZ_zero ht
  refine ⟨w, hw, ?_⟩
  have h1 : S = sqNF w * (sqNF (LocalDensity.NF.π v) : LocalSqCl v) ^ (n : ℤ) := by
    rw [← hut]; group
  rw [sqNF_mul (pow_ne_zero _ hπ.ne_zero) hw.ne_zero, sqNF_pow hπ.ne_zero, h1, zpow_natCast, mul_comm]

/-- Equal determinant classes force equal exponent sums. -/
theorem sum_eq_of_det_eq (c : 𝔬) (hcU : IsUnit c) (hv : (2 : 𝓞 F) ∉ v.asIdeal) {n : ℕ} (z z' : Fin n → ℕ) (x x' : Fin n → ℤˣ)
    (h : (genND v c z x).det = (genND v c z' x').det) : ∑ i, z i = ∑ i, z' i := by
  have hπ := LocalDensity.NF.irreducible_π v
  have hU := isUnit_detUnitND hv hcU x
  have hU' := isUnit_detUnitND hv hcU x'
  rw [det_genND_eq hv hcU, det_genND_eq hv hcU] at h
  have hA : LocalDensity.NF.π v ^ (∑ i, z i) * detUnitND v c x ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hπ.ne_zero) hU.ne_zero
  have hB : LocalDensity.NF.π v ^ (∑ i, z' i) * detUnitND v c x' ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hπ.ne_zero) hU'.ne_zero
  obtain ⟨t, ht⟩ := (sqNF_eq_iff hA hB).1 h
  have ht' : LocalDensity.NF.π v ^ (∑ i, z i) * ((t : 𝔬) ^ 2 * detUnitND v c x) =
      LocalDensity.NF.π v ^ (∑ i, z' i) * detUnitND v c x' := by rw [← ht]; ring
  exact (pow_mul_unit_eq hπ ((t.isUnit.pow 2).mul hU) hU' ht').1

/-- The genus map on tuples. -/
def gTupNF (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletionIntegers F) (t : (ℕ × ℕ) × ℤˣ × ℤˣ × ℤˣ) :
    LocGenus v 3 :=
  tupNF v c t.1.1 t.1.2 t.2.1 t.2.2.1 t.2.2.2

theorem gTupNF_injOn (c : 𝔬) (hcU : IsUnit c) (hc : chiR c = -1) (hv : (2 : 𝓞 F) ∉ v.asIdeal) (ν : ℕ) (u : ℤˣ) :
    Set.InjOn (gTupNF v c) (↑(oddGenera ν u) : Set ((ℕ × ℕ) × ℤˣ × ℤˣ × ℤˣ)) := by
  rintro ⟨⟨a, b⟩, e₁, e₂, e₃⟩ ht ⟨⟨a', b'⟩, e₁', e₂', e₃'⟩ ht' h
  simp only [Finset.mem_coe, oddGenera, Finset.mem_filter] at ht ht'
  obtain ⟨h1, h2, h3, h4, h5⟩ := tupNF_inj c hcU hc hv ht.2.1 ht'.2.1 h
  subst h1 h2 h3 h4 h5
  rfl

/-- **Finiteness of $\mathrm{Gen}^*_{\mathfrak p}(S, \varepsilon; 3)$** at $\mathfrak p \nmid 2$, every number field. -/
@[kb "hanke2011ternary" "§2, Lemma 2.1, pp. 4–5 (finiteness of the genera of given determinant, over F_p, p ∤ 2)"]
theorem oddNF_finite (hv : (2 : 𝓞 F) ∉ v.asIdeal) (S : LocalSqCl v) (c : ℤ) :
    {G : LocGenus v 3 | G.IsGenStar S c}.Finite := by
  obtain ⟨c₀, hcU, hc⟩ := exists_nonres_nf hv
  by_cases hne : ∃ G₀ : LocGenus v 3, G₀.IsGenStar S c
  · obtain ⟨G₀, hN0, hP0, hd0, -⟩ := hne
    obtain ⟨a0, b0, f1, f2, f3, hJ0, rfl⟩ := exists_tupNF c₀ hcU hc hv G₀ hN0 hP0
    refine ((Finset.finite_toSet ((antidiagonal (a0 + b0)) ×ˢ (Finset.univ : Finset (ℤˣ × ℤˣ × ℤˣ)))).image
      (gTupNF v c₀)).subset ?_
    rintro G ⟨hN, hP, hd, -⟩
    obtain ⟨a, b, g1, g2, g3, hJ, rfl⟩ := exists_tupNF c₀ hcU hc hv G hN hP
    refine ⟨((a, b), g1, g2, g3), ?_, rfl⟩
    have hs := sum_eq_of_det_eq c₀ hcU hv _ _ _ _ (hd.trans hd0.symm)
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at hs
    simp only [Finset.mem_coe, Finset.mem_product, Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_univ,
      and_true]
    omega
  · push Not at hne
    convert Set.finite_empty
    ext G
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact hne G

/-- **The sets $\mathrm{Gen}^*(S, \varepsilon)$ as images of the tuples of Lemma 2.1.** For $\operatorname{ord}S = \nu$
there is $u = \pm1$ such that for $\varepsilon = \pm1$ the set `{G | G.IsGenStar S ε}` is the image under `gTupNF` of the
tuples of `oddGenera ν u` with Hasse invariant $\varepsilon$. -/
theorem genStar_set (c : 𝔬) (hcU : IsUnit c) (hc : chiR c = -1) (hv : (2 : 𝓞 F) ∉ v.asIdeal) (S : LocalSqCl v) (ν : ℕ) (hS : (ordS v) S = ν) :
    ∃ u : ℤˣ, ∀ cu : ℤˣ, {G : LocGenus v 3 | G.IsGenStar S (cu : ℤ)} =
      gTupNF v c '' ↑((oddGenera ν u).filter fun t =>
        oddHasse (epsOdd v) t.1.1 t.1.2 t.2.1 t.2.2.1 t.2.2.2 = cu) := by
  obtain ⟨w, hw, rfl⟩ := exists_sqNF_of_ordS S ν hS
  refine ⟨sgn 𝔬 (2 : 𝔬) ^ 3 * sgn 𝔬 w, fun cu => ?_⟩
  ext G
  constructor
  · rintro ⟨hN, hP, hd, hh⟩
    obtain ⟨a, b, e₁, e₂, e₃, hJ, rfl⟩ := exists_tupNF c hcU hc hv G hN hP
    have hd' := (det_tupNF_iff c hcU hc hv a b e₁ e₂ e₃ hw ν).1 hd
    have hh' := hasse_tupNF c hcU hc hv a b e₁ e₂ e₃
    rw [hh] at hh'
    have hcu : oddHasse (epsOdd v) a b e₁ e₂ e₃ = cu := Units.ext hh'.symm
    refine ⟨((a, b), e₁, e₂, e₃), ?_, rfl⟩
    simp only [Finset.mem_coe, oddGenera, Finset.mem_filter, Finset.mem_product,
      Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_univ, and_true]
    exact ⟨⟨hd'.1, hJ, hd'.2⟩, hcu⟩
  · rintro ⟨⟨⟨a, b⟩, e₁, e₂, e₃⟩, ht, rfl⟩
    simp only [Finset.mem_coe, oddGenera, Finset.mem_filter, Finset.mem_product,
      Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_univ, and_true] at ht
    obtain ⟨⟨hab, hJ, hprod⟩, hcu⟩ := ht
    refine ⟨nondeg_tupNF c hcU hv a b e₁ e₂ e₃, prim_tupNF c hcU hv a b e₁ e₂ e₃,
      (det_tupNF_iff c hcU hc hv a b e₁ e₂ e₃ hw ν).2 ⟨hab, hprod⟩, ?_⟩
    show (tupNF v c a b e₁ e₂ e₃).hasse = _
    rw [hasse_tupNF c hcU hc hv, hcu]

/-- **The mass sum over $\mathrm{Gen}^*(S, \varepsilon)$ is $\widetilde M^{*,\varepsilon}_{\mathfrak p}$** of paper 7
(`Hanke2011Ternary.Mstar`), at the unit $u$ of `genStar_set`. -/
theorem sum_genStar (c : 𝔬) (hcU : IsUnit c) (hc : chiR c = -1) (hv : (2 : 𝓞 F) ∉ v.asIdeal) (S : LocalSqCl v) (ν : ℕ) (hS : (ordS v) S = ν) :
    ∃ u : ℤˣ, ∀ cu : ℤˣ,
      (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S (cu : ℤ)}, (1 - ((qv v : ℝ) ^ 2)⁻¹) / G.beta) =
        ((Mstar (qv v : ℚ) (epsOdd v) ν u cu : ℚ) : ℝ) := by
  obtain ⟨u, hu⟩ := genStar_set c hcU hc hv S ν hS
  refine ⟨u, fun cu => ?_⟩
  rw [hu cu, finsum_mem_image ((gTupNF_injOn c hcU hc hv ν u).mono
    (by intro t ht; exact (Finset.mem_filter.1 ht).1)), finsum_mem_coe_finset, Mstar, Rat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  obtain ⟨⟨a, b⟩, e₁, e₂, e₃⟩ := t
  have hJ := (Finset.mem_filter.1 (Finset.mem_filter.1 ht).1).2.1
  exact beta_tupNF c hcU hc hv hJ

/-- **Paper 7, Theorem 2.4 (Table 2, $A^*$ column) for the true local genera over $F$.** For $\mathfrak p \nmid 2$ and $S$
of valuation $\nu \ge 0$,
$$\sum_{G\in\mathrm{Gen}^*_{\mathfrak p}(S,1;3)}\frac{1-q^{-2}}{\beta(G)} + \sum_{G\in\mathrm{Gen}^*_{\mathfrak p}(S,-1;3)}\frac{1-q^{-2}}{\beta(G)}
= A^*_{\mathfrak p}(\nu)$$
with $A^*$ = `Hanke2011Ternary.Astar` at $q = N\mathfrak p$, $\varepsilon' = \left(\frac{-1}{\mathfrak p}\right)$. Unconditional. -/
@[kb "hanke2011ternary" "§2, Thm. 2.4, Table 2, p. 7 (A* column, true local genera over F_p, p ∤ 2)"]
theorem oddNF_A (hv : (2 : 𝓞 F) ∉ v.asIdeal) (S : LocalSqCl v) (hS : 0 ≤ (ordS v) S) :
    (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S 1}, (1 - ((qv v : ℝ) ^ 2)⁻¹) / G.beta) +
      (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S (-1)}, (1 - ((qv v : ℝ) ^ 2)⁻¹) / G.beta) =
      ((Astar (qv v) (epsOdd v) ((ordS v) S).toNat 1 : ℚ) : ℝ) := by
  obtain ⟨c, hcU, hc⟩ := exists_nonres_nf hv
  have hS' : (ordS v) S = (((ordS v) S).toNat : ℤ) := (Int.toNat_of_nonneg hS).symm
  obtain ⟨u, hu⟩ := sum_genStar c hcU hc hv S _ hS'
  have h1 := hu 1
  have h2 := hu (-1)
  simp only [Units.val_one, Units.val_neg] at h1 h2
  rw [h1, h2, ← Rat.cast_add]
  congr 1
  have hq := one_lt_qv_rat v
  have e : Mstar (qv v : ℚ) (epsOdd v) ((ordS v) S).toNat u 1 +
      Mstar (qv v : ℚ) (epsOdd v) ((ordS v) S).toNat u (-1) =
      Astar (qv v : ℚ) (epsOdd v) ((ordS v) S).toNat u := rfl
  rw [e]
  exact (Astar_eq_sum hq (epsOdd v) _ u).trans (Astar_eq_sum hq (epsOdd v) _ 1).symm

/-- **Paper 7, Theorem 2.4 (Table 2, $B^*$ column) for the true local genera over $F$.**  The same with a minus sign,
equal to $B^*_{\mathfrak p}(\nu)$ (`Hanke2011Ternary.Bstar`). Unconditional. -/
@[kb "hanke2011ternary" "§2, Thm. 2.4, Table 2, p. 7 (B* column, true local genera over F_p, p ∤ 2)"]
theorem oddNF_B (hv : (2 : 𝓞 F) ∉ v.asIdeal) (S : LocalSqCl v) (hS : 0 ≤ (ordS v) S) :
    (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S 1}, (1 - ((qv v : ℝ) ^ 2)⁻¹) / G.beta) -
      (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S (-1)}, (1 - ((qv v : ℝ) ^ 2)⁻¹) / G.beta) =
      ((Bstar (qv v) (epsOdd v) ((ordS v) S).toNat 1 : ℚ) : ℝ) := by
  obtain ⟨c, hcU, hc⟩ := exists_nonres_nf hv
  have hS' : (ordS v) S = (((ordS v) S).toNat : ℤ) := (Int.toNat_of_nonneg hS).symm
  obtain ⟨u, hu⟩ := sum_genStar c hcU hc hv S _ hS'
  have h1 := hu 1
  have h2 := hu (-1)
  simp only [Units.val_one, Units.val_neg] at h1 h2
  rw [h1, h2, ← Rat.cast_sub]
  congr 1
  have hq := one_lt_qv_rat v
  have e : Mstar (qv v : ℚ) (epsOdd v) ((ordS v) S).toNat u 1 -
      Mstar (qv v : ℚ) (epsOdd v) ((ordS v) S).toNat u (-1) =
      Bstar (qv v : ℚ) (epsOdd v) ((ordS v) S).toNat u := rfl
  rw [e]
  exact (Bstar_eq_sum hq (epsOdd v) _ u).trans (Bstar_eq_sum hq (epsOdd v) _ 1).symm

/-- **The unimodular case over $F$.** For $\mathfrak p \nmid 2$ and $\operatorname{ord}S = 0$ there is exactly one
nondegenerate primitive ternary local genus $G_0$ of Hessian determinant class $S$: it has Hasse invariant $+1$ and
$\beta(G_0) = 1 - q^{-2}$. Unconditional. -/
@[kb "hanke2011ternary" "§2, Thm. 2.4, Table 1, case 1, p. 6 (unimodular genus, true local genera over F_p, p ∤ 2)"]
theorem oddNF_unimod (hv : (2 : 𝓞 F) ∉ v.asIdeal) (S : LocalSqCl v) (hS : (ordS v) S = 0) :
    {G : LocGenus v 3 | G.IsGenStar S (-1)} = ∅ ∧
      ∃ G₀ : LocGenus v 3, {G : LocGenus v 3 | G.IsGenStar S 1} = {G₀} ∧
        G₀.beta = 1 - ((qv v : ℝ) ^ 2)⁻¹ := by
  obtain ⟨c, hcU, hc⟩ := exists_nonres_nf hv
  have hS' : (ordS v) S = ((0 : ℕ) : ℤ) := by rw [hS]; rfl
  obtain ⟨u, hu⟩ := genStar_set c hcU hc hv S 0 hS'
  have hF : oddGenera 0 u = {((0, 0), 1, 1, u)} := by
    ext ⟨⟨a, b⟩, e₁, e₂, e₃⟩
    simp only [oddGenera, Finset.mem_filter, Finset.mem_product, Finset.HasAntidiagonal.mem_antidiagonal,
      Finset.mem_univ, and_true, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨hab, ⟨-, h1, -, -⟩, hprod⟩
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha hb
      obtain ⟨rfl, rfl⟩ := h1 rfl rfl
      simpa using hprod
    · rintro ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩
      simp [IsJordanTuple]
  have hJ : IsJordanTuple 0 0 1 1 u := by simp [IsJordanTuple]
  have hH : oddHasse (epsOdd v) 0 0 1 1 u = 1 := oddHasse_case1 _ _ _ _
  have hq := one_lt_qv_rat v
  have hbeta : (1 - ((qv v : ℝ) ^ 2)⁻¹) / (tupNF v c 0 0 1 1 u).beta = 1 := by
    rw [beta_tupNF c hcU hc hv hJ, normDensity_case1 hq]
    simp
  have hbeta0 : (tupNF v c 0 0 1 1 u).beta ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hbeta
    exact zero_ne_one hbeta
  refine ⟨?_, tupNF v c 0 0 1 1 u, ?_, ?_⟩
  · have := hu (-1)
    simp only [Units.val_neg, Units.val_one] at this
    rw [this, hF]
    ext G
    simp [hH]
  · have := hu 1
    simp only [Units.val_one] at this
    rw [this, hF]
    ext G
    simp [hH, gTupNF]
    exact eq_comm
  · exact ((div_eq_one_iff_eq hbeta0).1 hbeta).symm

end NF

end

end QuadFormsKB.Hanke2011Ternary.OddNF

#print axioms QuadFormsKB.Hanke2011Ternary.OddNF.oddNF_finite
#print axioms QuadFormsKB.Hanke2011Ternary.OddNF.oddNF_A
#print axioms QuadFormsKB.Hanke2011Ternary.OddNF.oddNF_B
#print axioms QuadFormsKB.Hanke2011Ternary.OddNF.oddNF_unimod
