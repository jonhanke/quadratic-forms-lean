/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.Hanke2011Ternary.TablesNF
import QuadFormsKB.Literature.Hanke2011Structure.NonPrimLemma37
import QuadFormsKB.Literature.Hanke2011Structure.Remark418

/-!
# Paper 7, Theorem 8.1 over a number field: the non-primitive formula

J. Hanke, *Explicit formulas for masses of ternary quadratic lattices of varying determinant over number fields*,
arXiv:1109.1054 (`hanke2011ternary`), §8, Theorem 8.1 and its proof, p. 27.

The paper's total mass Dirichlet series $D_{\mathrm{Mass},\lambda,\vec\sigma_\infty;3}(s)$ has as coefficient of
$N(\mathfrak a)^{-s}$ the total mass of **all** (not necessarily primitive) $\mathcal O_F$-valued ternary lattices of
Hessian determinant squareclass $\lambda(\mathfrak a)$ (`GenAll`, `massOfTupleAll`, `NonPrimLemma37.lean`), and Theorem 8.1
states
$$D_{\mathrm{Mass},\lambda,\vec\sigma_\infty;3}(s) = \frac{|\Delta_F|^{3/2}\zeta_F(2)}{2(\pi^2 2^{s+2})^{[F:\mathbb Q]}}
\bigl[\zeta_F(s-1)\zeta_F(2s-1) + \varepsilon\,\zeta_F(2s-2)\zeta_F(s)\bigr],\qquad \varepsilon = (-1)^{[F:\mathbb Q]}.$$
The paper's proof: "summing over all possible scaled locally primitive $\mathcal O_{\mathfrak p}$-valued lattices at
$\mathfrak p$ has the effect of multiplying the primitive Dirichlet series by the local factor $(1 - q^{-3s})^{-1}$".

**Formalization.** Following that proof, purely locally:

1. Paper 6's Corollary 6.3 for all lattices (`sum_massOfTupleAll_eq`): the total mass is
   $C(S)\sum_{t\in\mathrm{Gen}_f(S)}\prod_{\mathfrak p}\beta(t_{\mathfrak p})^{-1}$, and by the sign-sum argument of paper 6's
   Theorem 4.8 (`finsum_tuple_sign`) this is $C(S)\cdot4^{[F:\mathbb Q]}\zeta_F(2)\cdot\frac12(\prod_{\mathfrak p}A_{\mathfrak p} +
   \prod_{\mathfrak p}B_{\mathfrak p})$ with the local sums $A_{\mathfrak p}$, $B_{\mathfrak p}$ over **all** nondegenerate local genera
   (`totalAll_eq_half`).
2. Locally (paper 6, Remark 4.18, `remark_4_18_A`, `remark_4_18_B_odd`): every local genus is $\varpi^jG'$ with $G'$
   primitive, $\beta(\varpi^jG') = q^{6j}\beta(G')$, $c(\varpi^jG') = (\varpi,\varpi)^jc(G')$, $\det(\varpi^jG') = [\varpi]^{3j}\det G'$.
   With paper 7's Tables 2 and 5.3 for the primitive sums (`ternaryLocalTablesNF_of_twoSplits`):
   $A_{\mathfrak p}(\nu) = \sum_j q^{-6j}A^*_{\mathfrak p}(\nu - 3j)$, i.e. the local factor of $D_{A^*}$ times
   $(1 - q^{-6}X^3)^{-1}$ (`allA`); for $B_{\mathfrak p}$ the twist $(\varpi,\varpi)^j_{\mathfrak p} = (-1,\varpi)^j_{\mathfrak p}$ of
   Remark 4.18 is cancelled at $\mathfrak p \nmid 2$ by the sign $\left(\frac{-1}{\mathfrak p}\right)^{\nu - 3j}$ of Table 2 and at
   $\mathfrak p \mid 2$ by the change $(-1,x\varpi^{-3j}) = (-1,x)(-1,\varpi)^{j}$ of the sign of Table 5.3 (`allB_odd`, `allB_dy`).
3. The signs are assembled by Hilbert reciprocity exactly as for Theorem 7.1 (`prod_sgnAt_eq`).

Result (`theorem_8_1_all`): coefficientwise,
$$\sum_{L}\frac1{|\mathrm{Aut}(L)|} = \frac{|\Delta_F|^{3/2}}{(64\pi^2)^{[F:\mathbb Q]}}N(\mathfrak a)^2\cdot\frac{4^{[F:\mathbb Q]}\zeta_F(2)}2
\Bigl([\mathfrak a^{-s}]\frac{\zeta_F(s+1)\zeta_F(2s+3)}{N(2\mathcal O_F)^s} + (-1)^{[F:\mathbb Q]}[\mathfrak a^{-s}]
\frac{\zeta_F(2s+2)\zeta_F(s+2)}{N(2\mathcal O_F)^s}\Bigr),$$
the right side as Euler products (`EAall`, `EBall`); the shift $s \mapsto s - 2$ turns this into the paper's formula
($N(\mathfrak a)^2$, $N(2\mathcal O_F)^2 = 4^{[F:\mathbb Q]}$).  In particular the paper's non-primitive formula is right for
ternary lattices: although Remark 4.18 of paper 6 shows a twist of the $B$ part by $(-1,\varpi)^j$, it cancels.
-/

open IsDedekindDomain NumberField Finset PowerSeries
open scoped nonZeroDivisors

namespace QuadFormsKB.Hanke2011Structure

open QuadFormsKB.NFEuler QuadFormsKB.Hanke2011Ternary QuadFormsKB.Hanke2011Ternary.NF QuadFormsKB.LocalDensity Rem418

open Classical

noncomputable section

local notation "ordS" v => SqCl.ordZ (localOrd v) (localUnits_le_ker v)

/-! ### The Euler factors without $\zeta_F(3s+6)^{-1}$ -/

/-- The local factor of $\zeta_F(s+1)\zeta_F(2s+3)$ at a prime of norm $q$: $(1-q^{-1}X)^{-1}(1-q^{-3}X^2)^{-1}$. -/
def EAall (q : ℚ) : PowerSeries ℚ := geom 1 q⁻¹ * geom 2 (q⁻¹ ^ 3)

/-- The local factor of $\zeta_F(2s+2)\zeta_F(s+2)$ at a prime of norm $q$: $(1-q^{-2}X^2)^{-1}(1-q^{-2}X)^{-1}$. -/
def EBall (q : ℚ) : PowerSeries ℚ := geom 2 (q⁻¹ ^ 2) * geom 1 (q⁻¹ ^ 2)

theorem EA_mul_geom (q : ℚ) : geom 3 (q⁻¹ ^ 6) * EA q = EAall q := by
  have h := geom_mul 3 (by norm_num) (q⁻¹ ^ 6)
  calc geom 3 (q⁻¹ ^ 6) * EA q = geom 1 q⁻¹ * geom 2 (q⁻¹ ^ 3) * (geom 3 (q⁻¹ ^ 6) * (1 - C (q⁻¹ ^ 6) * X ^ 3)) := by
        unfold EA; ring
    _ = EAall q := by rw [h, mul_one]; rfl

theorem EB_mul_geom (q : ℚ) : geom 3 (q⁻¹ ^ 6) * EB q = EBall q := by
  have h := geom_mul 3 (by norm_num) (q⁻¹ ^ 6)
  calc geom 3 (q⁻¹ ^ 6) * EB q = geom 2 (q⁻¹ ^ 2) * geom 1 (q⁻¹ ^ 2) * (geom 3 (q⁻¹ ^ 6) * (1 - C (q⁻¹ ^ 6) * X ^ 3)) := by
        unfold EB; ring
    _ = EBall q := by rw [h, mul_one]; rfl

theorem constantCoeff_EAall (q : ℚ) : constantCoeff (EAall q) = 1 := by simp [EAall, constantCoeff_geom]
theorem constantCoeff_EBall (q : ℚ) : constantCoeff (EBall q) = 1 := by simp [EBall, constantCoeff_geom]

/-- $[X^\nu]\bigl(\sum_jc^jX^{3j}\bigr)P = \sum_{3j\le\nu}c^j[X^{\nu-3j}]P$. -/
theorem coeff_geom3_mul (c : ℚ) (P : PowerSeries ℚ) (ν : ℕ) :
    coeff ν (geom 3 c * P) = ∑ a ∈ (range (ν + 1)).filter (fun a => 3 * a ≤ ν), c ^ a * coeff (ν - 3 * a) P := by
  have hP : P = PowerSeries.mk fun m => coeff m P := by ext; simp
  conv_lhs => rw [hP]
  rw [geom, spread_mul_mk 3 (by norm_num), coeff_mk]

/-! ### Local facts -/

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem ordS_piSq : (ordS v) (piSq v) = 1 := by
  unfold piSq
  rw [SqCl.ordZ_mk]
  change -WithZero.log (Valued.v (((NF.π v : 𝔬) : Fv))) = 1
  rw [NF.valued_π, WithZero.log_exp]
  rfl

/-- The shifted class $S[\varpi]^{-3j}$. -/
def shiftS (j : ℕ) (S : LocalSqCl v) : LocalSqCl v := S * (piSq v ^ (j * 3))⁻¹

theorem ordS_shiftS (j : ℕ) (S : LocalSqCl v) : (ordS v) (shiftS v j S) = (ordS v) S - 3 * j := by
  unfold shiftS
  rw [show (piSq v ^ (j * 3))⁻¹ = piSq v ^ (-((j * 3 : ℕ) : ℤ)) by rw [zpow_neg, zpow_natCast],
    SqCl.ordZ_mul, SqCl.ordZ_zpow, ordS_piSq]
  push_cast
  ring

/-- The Hessian determinant of an $\mathcal O_{\mathfrak p}$-valued form has nonnegative valuation. -/
theorem ordS_det_nonneg {G : LocGenus v 3} (hG : G.Nondeg) : 0 ≤ (ordS v) G.det := by
  induction G using Quotient.inductionOn with
  | h T =>
    have hT : algebraMap 𝔬 Fv T.hessian.det ≠ 0 := (algebraMap_ne_zero_iff (v := v)).2 hG
    change 0 ≤ (ordS v) (detSqForm T)
    rw [detSqForm_of_ne hT, SqCl.ordZ_mk]
    change 0 ≤ -WithZero.log (Valued.v (algebraMap 𝔬 Fv T.hessian.det))
    have h1 : Valued.v (algebraMap 𝔬 Fv T.hessian.det) ≤ 1 := (T.hessian.det).2
    have h0 : Valued.v (algebraMap 𝔬 Fv T.hessian.det) ≠ 0 := by simpa using hT
    have := (WithZero.log_le_iff_le_exp h0).2 (by rw [WithZero.exp_zero]; exact h1)
    omega

theorem primShift_eq_union (j : ℕ) (S : LocalSqCl v) :
    primShift v 3 j S = {G : LocGenus v 3 | G.IsGenStar (shiftS v j S) 1} ∪
      {G : LocGenus v 3 | G.IsGenStar (shiftS v j S) (-1)} := by
  rw [primShift_eq]
  ext G
  simp only [LocGenus.IsGenStar, shiftS, Set.mem_ofPred_eq, Set.mem_union]
  rcases LocGenus.hasse_pm_nf v G with h | h <;> simp [h]

theorem primShift_empty (j : ℕ) (S : LocalSqCl v) (h : (ordS v) S < 3 * j) : primShift v 3 j S = ∅ := by
  rw [primShift_eq]
  ext G
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hn, -, hd⟩
  have h1 := ordS_det_nonneg v hn
  rw [hd, show (piSq v ^ (j * 3))⁻¹ = piSq v ^ (-((j * 3 : ℕ) : ℤ)) by rw [zpow_neg, zpow_natCast],
    SqCl.ordZ_mul, SqCl.ordZ_zpow, ordS_piSq] at h1
  push_cast at h1
  omega

variable {v}

theorem finsum_primShift (H : TernaryLocalTablesNF F) (j : ℕ) (S : LocalSqCl v) (f : LocGenus v 3 → ℝ) :
    ∑ᶠ G ∈ primShift v 3 j S, f G = (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar (shiftS v j S) 1}, f G) +
      ∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar (shiftS v j S) (-1)}, f G := by
  have hD : Disjoint {G : LocGenus v 3 | G.IsGenStar (shiftS v j S) 1}
      {G : LocGenus v 3 | G.IsGenStar (shiftS v j S) (-1)} := by
    rw [Set.disjoint_left]
    rintro G ⟨-, -, -, h1⟩ ⟨-, -, -, h2⟩
    rw [h1] at h2; exact absurd h2 (by decide)
  rw [primShift_eq_union]
  exact finsum_mem_union hD (H.fin v _ 1) (H.fin v _ (-1))

theorem finsum_primShift_hasse (H : TernaryLocalTablesNF F) (j : ℕ) (S : LocalSqCl v) (f : LocGenus v 3 → ℝ) :
    ∑ᶠ G ∈ primShift v 3 j S, ((G.hasse : ℤ) : ℝ) * f G =
      (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar (shiftS v j S) 1}, f G) -
        ∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar (shiftS v j S) (-1)}, f G := by
  rw [finsum_primShift H, sub_eq_add_neg, ← finsum_mem_neg_distrib _ (H.fin v _ (-1))]
  congr 1
  · refine finsum_mem_congr rfl fun G hG => ?_
    rw [hG.2.2.2]; simp
  · refine finsum_mem_congr rfl fun G hG => ?_
    rw [hG.2.2.2]; simp

theorem allGen_finite (H : TernaryLocalTablesNF F) (S : LocalSqCl v) : (allGen v 3 S).Finite := by
  have hsub : allGen v 3 S ⊆ ⋃ j ∈ range (((ordS v) S).toNat + 1), smulPow v j '' primShift v 3 j S := by
    intro G hG
    obtain ⟨j, hj⟩ := exists_mem_image_of_allGen v (by norm_num) hG
    simp only [Set.mem_iUnion, Finset.mem_range, exists_prop]
    refine ⟨j, ?_, hj⟩
    by_contra hlt
    rw [primShift_empty v j S (by omega), Set.image_empty] at hj
    exact hj
  refine Set.Finite.subset (Set.Finite.biUnion (Finset.finite_toSet _) fun j _ => ?_) hsub
  rw [primShift_eq_union]
  exact ((H.fin v _ 1).union (H.fin v _ (-1))).image _

theorem q_eq_qv : (DVR.q 𝔬 : ℝ) = (qv v : ℝ) := by
  rw [NF.q_completion]; rfl

/-- The sum over $j$ of Remark 4.18 as a finite sum over $3j \le \nu$. -/
theorem finsum_shift_eq_sum (ν : ℕ) (S : LocalSqCl v) (hS : (ordS v) S = ν) (g : ℕ → ℝ) (M : ℕ → ℝ)
    (hM : ∀ j, primShift v 3 j S = ∅ → M j = 0) :
    ∑ᶠ j : ℕ, g j * M j = ∑ j ∈ (range (ν + 1)).filter (fun a => 3 * a ≤ ν), g j * M j := by
  refine finsum_eq_sum_of_support_subset _ fun j hj => ?_
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
  by_contra hn
  have hj' : ¬ 3 * j ≤ ν := fun h => hn ⟨by omega, h⟩
  apply hj
  simp only
  rw [hM j (primShift_empty v j S (by omega)), mul_zero]

end Local

/-! ### The local factors over all local genera -/

section Factors

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem cast_six (j : ℕ) :
    (((DVR.q 𝔬 : ℝ) ^ (3 * (3 + 1) / 2)) ^ j)⁻¹ = ((((qv v : ℚ)⁻¹ ^ 6) ^ j : ℚ) : ℝ) := by
  rw [q_eq_qv]
  push_cast
  rw [inv_pow, inv_pow]

/-- **The $A$ part of the local factor over all local genera** (paper 7, proof of Thm. 8.1; paper 6, Rem. 4.18): for
$S$ of valuation $\nu \ge 0$, $\sum_{G}\frac{w_{\mathfrak p}}{\beta(G)}$ over all nondegenerate ternary local genera of
$\det_H = S$ is $[X^\nu]\,\mathrm{twoShift}_{\mathfrak p}\cdot(1-q^{-1}X)^{-1}(1-q^{-3}X^2)^{-1}$
($w_{\mathfrak p}$ = `wbase`). -/
@[kb "hanke2011ternary" "§8, proof of Thm. 8.1, p. 27 (local factor over all lattices, A part)"]
theorem allA (H : TernaryLocalTablesNF F) (hs : TwoSplitsCompletely F) (S : LocalSqCl v) (ν : ℕ)
    (hS : (ordS v) S = ν) :
    ∑ᶠ G ∈ allGen v 3 S, wbase v / G.beta = ((coeff ν (twoShift v * EAall (qv v)) : ℚ) : ℝ) := by
  have hfin := allGen_finite H S
  have e1 : ∑ᶠ G ∈ allGen v 3 S, wbase v / G.beta = wbase v * massAll v 3 S := by
    unfold massAll
    simp only [div_eq_mul_inv]
    rw [mul_finsum_mem]
  rw [e1, remark_4_18_A v (by norm_num) hfin,
    finsum_shift_eq_sum ν S hS _ _ (fun j h => by unfold massPrimShift; rw [h, finsum_mem_empty]),
    Finset.mul_sum]
  -- each term
  have key : ∀ j ∈ (range (ν + 1)).filter (fun a => 3 * a ≤ ν),
      wbase v * ((((DVR.q 𝔬 : ℝ) ^ (3 * (3 + 1) / 2)) ^ j)⁻¹ * massPrimShift v 3 j S) =
        ((((qv v : ℚ)⁻¹ ^ 6) ^ j * locA v (ν - 3 * j) : ℚ) : ℝ) := by
    intro j hj
    have hj3 : 3 * j ≤ ν := (Finset.mem_filter.1 hj).2
    have hord : (ordS v) (shiftS v j S) = ((ν - 3 * j : ℕ) : ℤ) := by
      rw [ordS_shiftS, hS]; push_cast [hj3]; ring
    have hloc : wbase v * massPrimShift v 3 j S = ((locA v (ν - 3 * j) : ℚ) : ℝ) := by
      unfold massPrimShift
      rw [finsum_primShift H, mul_add, mul_finsum_mem, mul_finsum_mem]
      simp only [← div_eq_mul_inv]
      by_cases h2 : (2 : 𝓞 F) ∈ v.asIdeal
      · simp only [wbase, if_pos h2, locA]
        by_cases h0 : ν - 3 * j = 0
        · rw [H.dy_zero hs v h2 _ (by rw [hord, h0]; rfl) 1, H.dy_zero hs v h2 _ (by rw [hord, h0]; rfl) (-1), h0,
            dyadicA_zero']
          simp
        · rw [H.dy_A hs v h2 _ (by rw [hord]; omega), hord, Int.toNat_natCast]
      · simp only [wbase, if_neg h2, locA]
        rw [H.odd_A v h2 _ (by rw [hord]; positivity), hord, Int.toNat_natCast]
    rw [cast_six, ← mul_assoc, mul_comm (wbase v), mul_assoc, hloc]
    push_cast
    ring
  rw [Finset.sum_congr rfl key, ← Rat.cast_sum]
  congr 1
  rw [← EA_mul_geom, show twoShift v * (geom 3 ((qv v : ℚ)⁻¹ ^ 6) * EA (qv v)) =
    geom 3 ((qv v : ℚ)⁻¹ ^ 6) * (twoShift v * EA (qv v)) by ring, coeff_geom3_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [locA_eq hs.qv_eq_two]

/-- $(x^j, x^j) = (x, x)^j$ for the Hilbert symbol of $F_{\mathfrak p}$. -/
theorem hilb_pow_pow {x : Fv} (hx : x ≠ 0) (j : ℕ) :
    hilbertSymbol Fv (x ^ j) (x ^ j) = hilbertSymbol Fv x x ^ j := by
  have hpm : ∀ a b : Fv, hilbertSymbol Fv a b = 1 ∨ hilbertSymbol Fv a b = -1 := fun a b => by
    unfold hilbertSymbol; split_ifs <;> simp
  induction j with
  | zero => simp [hilbertSymbol_one_right]
  | succ j ih =>
    have hxj : x ^ j ≠ 0 := pow_ne_zero _ hx
    rw [pow_succ, OMeara.hilbertSymbol_mul_right_finite v (mul_ne_zero hxj hx) hxj hx,
      hilbertSymbol_comm Fv (x ^ j * x) (x ^ j), hilbertSymbol_comm Fv (x ^ j * x) x,
      OMeara.hilbertSymbol_mul_right_finite v hxj hxj hx, OMeara.hilbertSymbol_mul_right_finite v hx hxj hx, ih,
      hilbertSymbol_comm Fv x (x ^ j)]
    rcases hpm (x ^ j) x with h | h <;> rcases hpm x x with h' | h' <;> simp [h, h', pow_succ]

/-- $(\varpi^j,\varpi^j)^3 = (-1,\varpi)^j$ for the Hilbert symbol of $F_{\mathfrak p}$. -/
theorem hilb_pi_pow_cube (j : ℕ) :
    hilbertSymbol Fv (algebraMap 𝔬 Fv (NF.π v ^ j)) (algebraMap 𝔬 Fv (NF.π v ^ j)) ^ (3 * (3 - 1) / 2) =
      hilbertSymbol Fv (-1) (algebraMap 𝔬 Fv (NF.π v)) ^ j := by
  have hπ : algebraMap 𝔬 Fv (NF.π v) ≠ 0 := algebraMap_pi_ne_zero v
  have hK := HasseIsoNF.localHilbertField_adicCompletion v
  have hpm : ∀ a b : Fv, hilbertSymbol Fv a b = 1 ∨ hilbertSymbol Fv a b = -1 := fun a b => by
    unfold hilbertSymbol; split_ifs <;> simp
  rw [map_pow, hilb_pow_pow hπ, PadicClass.LocalHilbertField.self hK hπ, hilbertSymbol_comm,
    show 3 * (3 - 1) / 2 = 3 by norm_num, ← pow_mul]
  rcases hpm (-1) (algebraMap 𝔬 Fv (NF.π v)) with h | h <;> rw [h]
  · simp
  · rw [pow_mul]; rcases neg_one_pow_eq_or ℤ j with h' | h' <;> rw [h'] <;> norm_num

theorem hilb_pm (a b : Fv) : hilbertSymbol Fv a b = 1 ∨ hilbertSymbol Fv a b = -1 := by
  unfold hilbertSymbol; split_ifs <;> simp

theorem hilb_pow_right {a y : Fv} (ha : a ≠ 0) (hy : y ≠ 0) (k : ℕ) :
    hilbertSymbol Fv a (y ^ k) = hilbertSymbol Fv a y ^ k := by
  induction k with
  | zero => simp [hilbertSymbol_one_right]
  | succ k ih =>
    rw [pow_succ, OMeara.hilbertSymbol_mul_right_finite v ha (pow_ne_zero _ hy) hy, ih, pow_succ]

/-- At $\mathfrak p \nmid 2$: $(-1,\varpi)_{\mathfrak p} = \left(\frac{-1}{\mathfrak p}\right)$. -/
theorem hilb_neg_one_pi_odd (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    hilbertSymbol Fv (-1) (algebraMap 𝔬 Fv (NF.π v)) = ((epsOdd v : ℤˣ) : ℤ) := by
  have hu : IsUnit (-1 : 𝔬) := isUnit_one.neg
  have h := RatND.hilb_pi_unit h2 hu
  rw [hilbertSymbol_comm]
  have e : (((-1 : 𝔬) : 𝔬) : Fv) = -1 := by simp
  rw [e] at h
  rw [show algebraMap 𝔬 Fv (NF.π v) = (((NF.π v : 𝔬)) : Fv) from rfl, h, ← RatND.sgn_val hu,
    OddNF.sgn_neg_one_eq h2]

theorem unit_pow_sub_mul (e : ℤˣ) {j ν : ℕ} (hj : 3 * j ≤ ν) :
    ((e : ℤ) : ℚ) ^ j * ((e : ℤ) : ℚ) ^ (ν - 3 * j) = ((e : ℤ) : ℚ) ^ ν := by
  have hν : ν = (ν - 3 * j) + 3 * j := by omega
  conv_rhs => rw [hν]
  rw [pow_add, pow_mul]
  rcases Int.units_eq_one_or e with h | h <;> subst h
  · simp
  · rw [mul_comm]
    congr 1

/-- **The $B$ part of the local factor over all local genera at $\mathfrak p \nmid 2$**: the Hasse-weighted sum is
$\left(\frac{-1}{\mathfrak p}\right)^\nu[X^\nu](1-q^{-2}X^2)^{-1}(1-q^{-2}X)^{-1}$ (the twist of Remark 4.18 cancels). -/
@[kb "hanke2011ternary" "§8, proof of Thm. 8.1, p. 27 (local factor over all lattices, B part, p ∤ 2)"]
theorem allB_odd (H : TernaryLocalTablesNF F) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (S : LocalSqCl v) (ν : ℕ)
    (hS : (ordS v) S = ν) :
    ∑ᶠ G ∈ allGen v 3 S, ((G.hasse : ℤ) : ℝ) * (wbase v / G.beta) =
      ((((epsOdd v : ℤ) : ℚ) ^ ν * coeff ν (EBall (qv v)) : ℚ) : ℝ) := by
  have hfin := allGen_finite H S
  have e1 : ∑ᶠ G ∈ allGen v 3 S, ((G.hasse : ℤ) : ℝ) * (wbase v / G.beta) = wbase v * massAllB v 3 S := by
    unfold massAllB
    rw [mul_finsum_mem]
    refine finsum_mem_congr rfl fun G _ => ?_
    rw [div_eq_mul_inv]; ring
  rw [e1, remark_4_18_B_odd v (by decide) hfin,
    finsum_shift_eq_sum ν S hS _ _ (fun j h => by unfold massPrimShiftB; rw [h, finsum_mem_empty]),
    Finset.mul_sum]
  have key : ∀ j ∈ (range (ν + 1)).filter (fun a => 3 * a ≤ ν),
      wbase v * (((hilbertSymbol Fv (algebraMap 𝔬 Fv (NF.π v ^ j)) (algebraMap 𝔬 Fv (NF.π v ^ j)) ^
        (3 * (3 - 1) / 2) : ℤ) : ℝ) * (((DVR.q 𝔬 : ℝ) ^ (3 * (3 + 1) / 2)) ^ j)⁻¹ * massPrimShiftB v 3 j S) =
        ((((qv v : ℚ)⁻¹ ^ 6) ^ j * (((epsOdd v : ℤ) : ℚ) ^ ν * coeff (ν - 3 * j) (EB (qv v))) : ℚ) : ℝ) := by
    intro j hj
    have hj3 : 3 * j ≤ ν := (Finset.mem_filter.1 hj).2
    have hord : (ordS v) (shiftS v j S) = ((ν - 3 * j : ℕ) : ℤ) := by
      rw [ordS_shiftS, hS]; push_cast [hj3]; ring
    have hloc : wbase v * massPrimShiftB v 3 j S = ((Bstar (qv v) (epsOdd v) (ν - 3 * j) 1 : ℚ) : ℝ) := by
      unfold massPrimShiftB
      rw [finsum_primShift_hasse H, mul_sub, mul_finsum_mem, mul_finsum_mem]
      simp only [← div_eq_mul_inv, wbase, if_neg h2]
      rw [H.odd_B v h2 _ (by rw [hord]; positivity), hord, Int.toNat_natCast]
    have hB := Bstar_eq_coeff_EB (one_lt_qv_rat v) (epsOdd v) (ν - 3 * j)
    have hBs : Bstar (qv v) (epsOdd v) (ν - 3 * j) 1 =
        ((epsOdd v : ℤ) : ℚ) ^ (ν - 3 * j) * coeff (ν - 3 * j) (EB (qv v)) := by
      rw [← hB, ← mul_assoc, ← mul_pow]
      rcases Int.units_eq_one_or (epsOdd v) with h | h <;> simp [h]
    rw [hilb_pi_pow_cube, hilb_neg_one_pi_odd h2, cast_six, mul_comm (wbase v), mul_assoc, mul_assoc,
      mul_comm _ (wbase v), hloc, hBs, ← unit_pow_sub_mul (epsOdd v) hj3]
    push_cast
    ring
  rw [Finset.sum_congr rfl key, ← Rat.cast_sum]
  congr 1
  rw [← EB_mul_geom, coeff_geom3_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The $B$ part of the local factor over all local genera at $\mathfrak p \mid 2$** ($F_{\mathfrak p} \cong \mathbb Q_2$): for $x$
in the rational squareclass of $S$, the Hasse-weighted sum is $-(-1,x)_{\mathfrak p}[X^\nu]\,X(1-\frac14X^2)^{-1}(1-\frac14X)^{-1}$
(the twist of Remark 4.18 cancels against the change of $(-1, x\varpi^{-3j})$). -/
@[kb "hanke2011ternary" "§8, proof of Thm. 8.1, p. 27 (local factor over all lattices, B part, p | 2)"]
theorem allB_dy (H : TernaryLocalTablesNF F) (hs : TwoSplitsCompletely F) (h2 : (2 : 𝓞 F) ∈ v.asIdeal)
    (S : LocalSqCl v) (ν : ℕ) (hS : (ordS v) S = ν) (x : Fvˣ) (hx : rhoLocal v S = SqCl.mk x) :
    ∑ᶠ G ∈ allGen v 3 S, ((G.hasse : ℤ) : ℝ) * (wbase v / G.beta) =
      ((-((hilbertSymbol Fv (-1) (x : Fv) : ℤ) : ℚ) * coeff ν (twoShift v * EBall (qv v)) : ℚ) : ℝ) := by
  have hfin := allGen_finite H S
  have hπ : algebraMap 𝔬 Fv (NF.π v) ≠ 0 := algebraMap_pi_ne_zero v
  set u : Fvˣ := Units.mk0 _ hπ with hu
  have e1 : ∑ᶠ G ∈ allGen v 3 S, ((G.hasse : ℤ) : ℝ) * (wbase v / G.beta) = wbase v * massAllB v 3 S := by
    unfold massAllB
    rw [mul_finsum_mem]
    refine finsum_mem_congr rfl fun G _ => ?_
    rw [div_eq_mul_inv]; ring
  rw [e1, remark_4_18_B_odd v (by decide) hfin,
    finsum_shift_eq_sum ν S hS _ _ (fun j h => by unfold massPrimShiftB; rw [h, finsum_mem_empty]),
    Finset.mul_sum]
  set h1 : ℤ := hilbertSymbol Fv (-1) (x : Fv) with hh1
  set hp : ℤ := hilbertSymbol Fv (-1) (algebraMap 𝔬 Fv (NF.π v)) with hhp
  have key : ∀ j ∈ (range (ν + 1)).filter (fun a => 3 * a ≤ ν),
      wbase v * (((hilbertSymbol Fv (algebraMap 𝔬 Fv (NF.π v ^ j)) (algebraMap 𝔬 Fv (NF.π v ^ j)) ^
        (3 * (3 - 1) / 2) : ℤ) : ℝ) * (((DVR.q 𝔬 : ℝ) ^ (3 * (3 + 1) / 2)) ^ j)⁻¹ * massPrimShiftB v 3 j S) =
        ((((qv v : ℚ)⁻¹ ^ 6) ^ j * (-(h1 : ℚ) * coeff (ν - 3 * j) (X * EB (qv v))) : ℚ) : ℝ) := by
    intro j hj
    have hj3 : 3 * j ≤ ν := (Finset.mem_filter.1 hj).2
    have hord : (ordS v) (shiftS v j S) = ((ν - 3 * j : ℕ) : ℤ) := by
      rw [ordS_shiftS, hS]; push_cast [hj3]; ring
    -- the rational class of the shifted squareclass
    set xj : Fvˣ := x * (u ^ (j * 3))⁻¹ with hxj
    have hrho : rhoLocal v (shiftS v j S) = SqCl.mk xj := by
      unfold shiftS piSq
      rw [map_mul, map_inv, map_pow, hx, rhoLocal_mk, hxj, map_mul, map_inv, map_pow]
    have hhj : hilbertSymbol Fv (-1) (xj : Fv) = h1 * hp ^ (j * 3) := by
      have hxv : (xj : Fv) = ((x : Fv) * (algebraMap 𝔬 Fv (NF.π v)) ^ (j * 3)) *
          (((algebraMap 𝔬 Fv (NF.π v)) ^ (j * 3))⁻¹) ^ 2 := by
        rw [hxj, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, hu, Units.val_mk0]
        field_simp
      rw [hxv, SqDual.hilbertSymbol_mul_sq_right _ _ _ _ (inv_ne_zero (pow_ne_zero _ hπ)),
        OMeara.hilbertSymbol_mul_right_finite v (by norm_num) x.ne_zero (pow_ne_zero _ hπ),
        hilb_pow_right (by norm_num) hπ]
    have hloc : wbase v * massPrimShiftB v 3 j S =
        ((dyadicB (toSign (hilbertSymbol Fv (-1) (xj : Fv))) (ν - 3 * j) : ℚ) : ℝ) := by
      unfold massPrimShiftB
      rw [finsum_primShift_hasse H, mul_sub, mul_finsum_mem, mul_finsum_mem]
      simp only [← div_eq_mul_inv, wbase, if_pos h2]
      by_cases h0 : ν - 3 * j = 0
      · rw [H.dy_zero hs v h2 _ (by rw [hord, h0]; rfl) 1, H.dy_zero hs v h2 _ (by rw [hord, h0]; rfl) (-1), h0,
          dyadicB_zero']
        simp
      · rw [H.dy_B hs v h2 _ (by rw [hord]; omega) xj hrho, hord, Int.toNat_natCast]
    have hpm1 : h1 = 1 ∨ h1 = -1 := hilb_pm _ _
    have hpmp : hp = 1 ∨ hp = -1 := hilb_pm _ _
    have hts : ((toSign (hilbertSymbol Fv (-1) (xj : Fv)) : ℤˣ) : ℤ) = h1 * hp ^ (j * 3) := by
      rw [toSign_val (hilb_pm _ _), hhj]
    rw [hilb_pi_pow_cube, cast_six, mul_comm (wbase v), mul_assoc, mul_assoc, mul_comm _ (wbase v), hloc,
      dyadicB_eq_coeff, hts, hs.qv_eq_two v h2]
    rw [← hhp]
    push_cast
    rcases hpmp with h | h <;> rw [h]
    · push_cast; ring
    · push_cast
      have k2 : ((-1 : ℝ)) ^ j * (-1) ^ (j * 3) = 1 := by
        rw [← pow_add, show j + j * 3 = 2 * (2 * j) by ring, pow_mul]; norm_num
      linear_combination (-((h1 : ℤ) : ℝ) * ((2 : ℝ)⁻¹ ^ 6) ^ j *
        ((coeff (ν - 3 * j) (X * EB ((2 : ℕ) : ℚ)) : ℚ) : ℝ)) * k2
  rw [Finset.sum_congr rfl key, ← Rat.cast_sum]
  congr 1
  have htw : twoShift v = X := by unfold twoShift; rw [if_pos h2]
  rw [htw, ← EB_mul_geom, show (X : PowerSeries ℚ) * (geom 3 ((qv v : ℚ)⁻¹ ^ 6) * EB (qv v)) =
    geom 3 ((qv v : ℚ)⁻¹ ^ 6) * (X * EB (qv v)) by ring, coeff_geom3_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end Factors

/-! ### The global assembly -/

section Global

variable {F : Type} [Field F] [NumberField F]

/-- The admissible local genera at $\mathfrak p$ for all lattices of Hessian determinant squareclass $S$: all
nondegenerate ternary local genera of $\det_H = S_{\mathfrak p}$. -/
def admAll (S : AdelicSqCl F) (v : HeightOneSpectrum (𝓞 F)) : Set (LocGenus v 3) := allGen v 3 (AdelicSqCl.comp v S)

/-- **Paper 6's Theorem 4.8 (sign-sum form) for all lattices**, $n = 3$: as `totalMassM_eq_half_nf`, with the local
genera not required to be primitive. -/
theorem totalAll_eq_half (S : AdelicSqCl F) (P : Finset (HeightOneSpectrum (𝓞 F))) (b : LocTuple F 3)
    (w : HeightOneSpectrum (𝓞 F) → ℝ) (C : ℝ)
    (hout : ∀ v ∉ P, admAll S v = {b v}) (hb1 : ∀ v ∉ P, (b v).hasse = 1)
    (hw : ∀ v ∉ P, w v = (b v).beta) (hw0 : ∀ v, w v ≠ 0)
    (hfin : ∀ v ∈ P, (admAll S v).Finite) (hprod : HasProd (fun v => (w v)⁻¹) C) :
    ∑ᶠ t ∈ (GenAllF S 1 : Set (LocTuple F 3)), invDensityTuple t = C * ((∏ v ∈ P, ∑ᶠ G ∈ admAll S v, w v / G.beta) +
      ∏ v ∈ P, ∑ᶠ G ∈ admAll S v, ((G.hasse : ℤ) : ℝ) * (w v / G.beta)) / 2 := by
  have hgen : (GenAllF S 1 : Set (LocTuple F 3)) =
      {t | (∀ v, t v ∈ admAll S v) ∧ (Function.mulSupport fun v => (t v).hasse).Finite ∧
        ∏ᶠ v, (t v).hasse = 1} := by
    ext t; simp [GenAllF, admAll, allGen]
  rw [hgen]
  have hT : ∀ t ∈ {t : LocTuple F 3 | (∀ v, t v ∈ admAll S v) ∧
      (Function.mulSupport fun v => (t v).hasse).Finite ∧ ∏ᶠ v, (t v).hasse = 1},
      invDensityTuple t = C * ∏ v ∈ P, w v / (t v).beta := by
    rintro t ⟨hA, -⟩
    have hout' : ∀ v ∉ P, (t v).beta = w v := fun v hv => by
      have h := hA v
      rw [hout v hv] at h
      rw [Set.mem_singleton_iff.mp h, hw v hv]
    obtain ⟨hm, he⟩ := invDensity_factor P w (fun v => (t v).beta) hout' hw0
      (fun v => (LocGenus.beta_pos_nf v _ (hA v).1).ne') hprod.multipliable
    unfold invDensityTuple
    rw [if_pos hm, he, hprod.tprod_eq]
  rw [finsum_mem_congr rfl hT, ← mul_finsum_mem,
    finsum_tuple_sign P b (admAll S) (fun v G => G.hasse) (fun v G => w v / G.beta) hout hb1 hfin
      (fun v G => LocGenus.hasse_pm_nf v G)]
  ring

theorem smulPow_zero (v : HeightOneSpectrum (𝓞 F)) (G : LocGenus v 3) : smulPow v 0 G = G := by
  induction G using Quotient.inductionOn with
  | h T =>
    change smulPow v 0 (LocGenus.mk T) = LocGenus.mk T
    rw [smulPow_mk]
    congr 1
    ext i j
    simp

/-- At a prime where $S_{\mathfrak p}$ is a unit class, every nondegenerate local genus of $\det_H = S_{\mathfrak p}$ is
primitive. -/
theorem allGen_eq_of_ord_zero (v : HeightOneSpectrum (𝓞 F)) (S : LocalSqCl v) (hS : (ordS v) S = 0) :
    allGen v 3 S = {G : LocGenus v 3 | G.IsGenStar S 1} ∪ {G : LocGenus v 3 | G.IsGenStar S (-1)} := by
  have h0 : shiftS v 0 S = S := by simp [shiftS]
  ext G
  constructor
  · intro hG
    obtain ⟨j, G', hG', rfl⟩ := exists_mem_image_of_allGen v (by norm_num) hG
    have hj : j = 0 := by
      by_contra hj
      rw [primShift_empty v j S (by omega)] at hG'
      exact hG'
    subst hj
    rw [smulPow_zero]
    rw [primShift_eq_union, h0] at hG'
    exact hG'
  · rintro (⟨hn, -, hd, -⟩ | ⟨hn, -, hd, -⟩) <;> exact ⟨hn, hd⟩

/-- **Theorem 8.1, non-primitive formula, coefficientwise** (Hanke 2011, ternary paper, p. 27; the paper's
$D_{\mathrm{Mass},\lambda,\vec\sigma_\infty;3}$), for a totally real number field $F$ in which $2$ splits completely, the totally
positive definite signature, and $\lambda(\mathfrak a)$ globally rational with a totally positive representative $\alpha$: the
total mass of **all** $\mathcal O_F$-valued ternary lattices of Hessian determinant squareclass $\lambda(\mathfrak a)$ is
$$\sum_{L}\frac1{|\mathrm{Aut}(L)|} = \frac{|\Delta_F|^{3/2}}{(64\pi^2)^{[F:\mathbb Q]}}\,N(\mathfrak a)^2\cdot
\frac{4^{[F:\mathbb Q]}\zeta_F(2)}{2}\Bigl([\mathfrak a^{-s}]\frac{\zeta_F(s+1)\zeta_F(2s+3)}{N(2\mathcal O_F)^s} +
(-1)^{[F:\mathbb Q]}[\mathfrak a^{-s}]\frac{\zeta_F(2s+2)\zeta_F(s+2)}{N(2\mathcal O_F)^s}\Bigr),$$
the right side as Euler products (`eulerCoeff EAall`, `eulerCoeff EBall`).  This is the coefficient of $N(\mathfrak a)^{-s}$ in
the paper's $\frac{|\Delta_F|^{3/2}\zeta_F(2)}{2(\pi^22^{s+2})^{[F:\mathbb Q]}}[\zeta_F(s-1)\zeta_F(2s-1) +
\varepsilon\zeta_F(2s-2)\zeta_F(s)]$, $\varepsilon = (-1)^{[F:\mathbb Q]}$ (shift $s \mapsto s - 2$).  Unconditional.
*Scope:* the paper allows any totally definite signature vector; this statement is for the totally positive definite one,
as `theorem_8_1_primitive`. -/
@[kb "hanke2011ternary" "§8, Thm. 8.1, p. 27 (non-primitive formula, coefficientwise; F totally real, 2 split)"]
theorem theorem_8_1_all [IsTotallyReal F] (hs : TwoSplitsCompletely F)
    (lam : DistinguishedFamily F) (a : (Ideal (𝓞 F))⁰) (α : Fˣ)
    (hα : ∀ v, rhoLocal v (AdelicSqCl.comp v (lam.toHom a)) = SqCl.mk (unitsToLocal v α))
    (hsign : ∀ w : {w : InfinitePlace F // w.IsReal}, IsSquare (algebraMap F w.1.Completion (α : F))) :
    ∑ᶠ t ∈ GenAll (lam.toHom a) (totPosSig F 3), massOfTupleAll (lam.toHom a) (totPosSig F 3) t =
      |(discr F : ℝ)| ^ ((3 : ℝ) / 2) / (64 * Real.pi ^ 2) ^ Module.finrank ℚ F *
        (Ideal.absNorm (a : Ideal (𝓞 F)) : ℝ) ^ 2 *
        (4 ^ Module.finrank ℚ F * dedekindZetaR F 2 / 2) *
        ((eulerCoeff EAall a + (-1) ^ Module.finrank ℚ F * eulerCoeff EBall a : ℚ) : ℝ) := by
  have H := ternaryLocalTablesNF_of_twoSplits hs
  rw [sum_massOfTupleAll_eq (by norm_num) _ α hα hsign]
  set S := lam.toHom a with hS
  set P := (finite_bad a).toFinset with hP
  have hmemP : ∀ v, v ∉ P → (2 : 𝓞 F) ∉ v.asIdeal ∧ ordI v a = 0 := fun v hv => by
    rw [Set.Finite.mem_toFinset] at hv
    simp only [Set.mem_ofPred_eq, not_or, not_not] at hv
    exact hv
  have hord := ordS_comp_lam lam a
  -- the base tuple
  have hbase : ∀ v, ∃ G : LocGenus v 3, v ∉ P → admAll S v = {G} ∧ G.hasse = 1 ∧ G.beta = wbase v := by
    intro v
    by_cases hv : v ∈ P
    · exact ⟨LocGenus.mk ⟨0, fun _ _ _ => rfl⟩, fun h => absurd hv h⟩
    · obtain ⟨h2, h0⟩ := hmemP v hv
      have h0' : (ordS v) (AdelicSqCl.comp v S) = 0 := by rw [hord, h0]; rfl
      obtain ⟨he, G₀, hs1, hb⟩ := H.odd_unimod v h2 _ h0'
      have hmem : G₀ ∈ {G : LocGenus v 3 | G.IsGenStar (AdelicSqCl.comp v S) 1} := by rw [hs1]; rfl
      refine ⟨G₀, fun _ => ⟨?_, hmem.2.2.2, by rw [hb, wbase, if_neg h2]⟩⟩
      rw [admAll, allGen_eq_of_ord_zero v _ h0', hs1, he, Set.union_empty]
  choose b hb using hbase
  have hfin : ∀ v ∈ P, (admAll S v).Finite := fun v _ => allGen_finite H _
  rw [totalAll_eq_half S P b wbase _ (fun v hv => (hb v hv).1) (fun v hv => (hb v hv).2.1)
    (fun v hv => (hb v hv).2.2.symm) wbase_ne_zero hfin (hasProd_baseNF hs.qv_eq_two)]
  -- the local factors
  have hloc : ∀ v ∈ P, (∑ᶠ G ∈ admAll S v, wbase v / G.beta) =
        ((coeff (ordI v a) (twoShift v * EAall (qv v)) : ℚ) : ℝ) ∧
      (∑ᶠ G ∈ admAll S v, ((G.hasse : ℤ) : ℝ) * (wbase v / G.beta)) =
        ((((sgnAt (epsAlpha α) a v : ℤˣ) : ℤ) : ℚ) * coeff (ordI v a) (twoShift v * EBall (qv v)) : ℚ) := by
    intro v _
    have hν : (ordS v) (AdelicSqCl.comp v S) = (ordI v a : ℤ) := hord v
    refine ⟨allA H hs _ _ hν, ?_⟩
    by_cases h2 : (2 : 𝓞 F) ∈ v.asIdeal
    · rw [admAll, allB_dy H hs h2 _ _ hν (unitsToLocal v α) (hα v)]
      simp only [sgnAt, if_pos h2, epsAlpha, Units.val_neg]
      rw [toSign_val (NFPlace.hilbert_eq_one_or _ _ _)]
      simp only [NFPlace.hilbert, map_neg, map_one]
      push_cast
      rfl
    · rw [admAll, allB_odd H h2 _ _ hν]
      simp only [sgnAt, if_neg h2, twoShift, one_mul]
      push_cast
      ring
  rw [Finset.prod_congr rfl fun v hv => (hloc v hv).1, Finset.prod_congr rfl fun v hv => (hloc v hv).2]
  -- the Euler coefficients
  have hA : eulerCoeff EAall a = ∏ v ∈ P, coeff (ordI v a) (twoShift v * EAall (qv v)) := by
    unfold eulerCoeff
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hn
    obtain ⟨h2, h0⟩ := hmemP v hn
    exact hv (by simp only; rw [h0]; exact coeff_zero_shift_E EAall constantCoeff_EAall v h2)
  have hBc : eulerCoeff EBall a = ∏ v ∈ P, coeff (ordI v a) (twoShift v * EBall (qv v)) := by
    unfold eulerCoeff
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hn
    obtain ⟨h2, h0⟩ := hmemP v hn
    exact hv (by simp only; rw [h0]; exact coeff_zero_shift_E EBall constantCoeff_EBall v h2)
  -- the sign
  have hodd : ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∉ v.asIdeal →
      (NFPlace.finite v).hilbert (-1 : F) (α : F) = ((epsOdd v ^ ordI v a : ℤˣ) : ℤ) := fun v h2 => by
    rw [hilbert_neg_one_nondyadic v h2 α, unit_zpow_eq_pow_of_even _ _ _ (even_ordL_add_ordI lam a α v (hα v))]
  have hdy : ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal →
      ((epsAlpha α a v : ℤˣ) : ℤ) = (NFPlace.finite v).hilbert (-1 : F) (α : F) := fun v _ =>
    toSign_val (NFPlace.hilbert_eq_one_or _ _ _)
  have hsg := prod_sgnAt_eq (epsAlpha α) a α hodd hdy
  have hinf : ∏ w : InfinitePlace F, (NFPlace.infinite w).hilbert (-1 : F) (α : F) = 1 :=
    Finset.prod_eq_one fun w _ => hilbertSymbol_of_isSquare_right _ _ _ (hsign ⟨w, IsTotallyReal.isReal w⟩)
  rw [hinf, mul_one, hs.numDyadic_eq] at hsg
  have hsP : ∏ v ∈ P, (((sgnAt (epsAlpha α) a v : ℤˣ) : ℤ) : ℚ) = (-1) ^ Module.finrank ℚ F := by
    have hf : Function.mulSupport (fun v => ((sgnAt (epsAlpha α) a v : ℤˣ) : ℤ)) ⊆ P := fun v hv => by
      by_contra hn
      obtain ⟨h2, h0⟩ := hmemP v hn
      exact hv (by simp [sgnAt, h2, h0])
    rw [finprod_eq_prod_of_mulSupport_subset _ hf] at hsg
    rw [← Int.cast_prod, hsg]
    push_cast
    rfl
  simp only [← Rat.cast_prod]
  rw [Finset.prod_mul_distrib, hsP, ← hA, ← hBc]
  -- the constant
  have hC : massConst F 3 S = |(discr F : ℝ)| ^ ((3 : ℝ) / 2) / (64 * Real.pi ^ 2) ^ Module.finrank ℚ F *
      (Ideal.absNorm (a : Ideal (𝓞 F)) : ℝ) ^ 2 := by
    unfold massConst
    rw [hS, normAssoc_toHom, volV_three]
    have e1 : (3 : ℝ) * (3 - 1) / 4 = 3 / 2 := by norm_num
    have e2 : ((2 : ℝ) ^ Module.finrank ℚ F) ^ ((3 : ℝ) * (3 + 1) / 2) = 64 ^ Module.finrank ℚ F := by
      rw [show (3 : ℝ) * (3 + 1) / 2 = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← pow_mul, mul_comm,
        pow_mul]
      norm_num
    have e3 : (Ideal.absNorm (a : Ideal (𝓞 F)) : ℝ) ^ (((3 : ℝ) + 1) / 2) =
        (Ideal.absNorm (a : Ideal (𝓞 F)) : ℝ) ^ 2 := by
      rw [show ((3 : ℝ) + 1) / 2 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    push_cast at e1 e2 e3 ⊢
    rw [e1, e2, e3, mul_pow]
    have h64 : (0 : ℝ) < 64 ^ Module.finrank ℚ F := by positivity
    have hpi : (0 : ℝ) < (Real.pi ^ 2) ^ Module.finrank ℚ F := by positivity
    field_simp
  rw [hC, hs.numDyadic_eq]
  push_cast
  ring

end Global

end

end QuadFormsKB.Hanke2011Structure

#print axioms QuadFormsKB.Hanke2011Structure.allA
#print axioms QuadFormsKB.Hanke2011Structure.allB_odd
#print axioms QuadFormsKB.Hanke2011Structure.allB_dy
#print axioms QuadFormsKB.Hanke2011Structure.theorem_8_1_all
