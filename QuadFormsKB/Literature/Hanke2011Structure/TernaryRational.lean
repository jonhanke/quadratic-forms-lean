/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.Hanke2011Structure.TernaryFinal

/-!
# Paper 6, Theorem 5.4 and Corollary 5.5 for $n = 3$ over $\mathbb Q$, for the true local genera

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Thm. 5.4, p. 23, and Cor. 5.5, p. 24.

Theorem 5.4: for $\mathfrak p \nmid 2$ (or $F_{\mathfrak p} = \mathbb Q_2$) the "fixed unit" local series
$\sum_{\widetilde S_{\mathfrak p}\ \mathrm{fixed}} A^*_{\mathfrak p;n}(S_{\mathfrak p})X^{\operatorname{ord}S_{\mathfrak p}}$ and the same with
$B^*$ are rational functions of $X = q^{-s}$. Here, for $n = 3$ and $F = \mathbb Q$, $A^*_p$, $B^*_p$ are the normalized local
mass sums of the **true** local genera (Def. 4.6: $\sum_G \beta(G_0)/\beta(G)$ over the nondegenerate primitive
$\mathbb Z_p$-genera $G$ of $\det_H G = S$, with or without the Hasse invariant as a sign), and the series are identified
with explicit rational functions:

* $p$ odd (`theorem_5_4_odd_A`, `theorem_5_4_odd_B`), unconditional: paper 7's Lemmas 3.1–3.2 for the true genera
  (through `Odd7.odd_A`, `Odd7.odd_B`);
* $p = 2$ (`theorem_5_4_two_A`, `theorem_5_4_two_B`), from Table 5.3 for the true genera
  (`Dyadic7.DyadicTernaryLocalMassTable`): paper 7's Lemmas 6.1–6.2.

The unit class is fixed by an integer representative $w$ prime to $p$ ($S = [p^\nu w]$); every unit class of
$\mathbb Z_p^\times$ has one. Theorem 5.4 for general $n$ is not formalized (see the coverage table).

Cor. 5.5 (the Euler factors $\sum_i A^*_p(\lambda(p^i))p^{-is}$ for a distinguished family) is, over $\mathbb Q$ with
$\lambda(p^i) = p^i$ ($w = 1$), the case $w = 1$ of these identities.
-/

open IsDedekindDomain NumberField PowerSeries

namespace QuadFormsKB.Hanke2011Structure

open QuadFormsKB.Dyadic7 QuadFormsKB.Hanke2011Ternary QuadFormsKB.ConwaySloane Cassels

noncomputable section

local notation "pv" => ConwaySloane.Mass.pv

/-- The rational-to-real image of a power-series identity. -/
theorem map_mk_rat (f : ℕ → ℚ) :
    PowerSeries.map (Rat.castHom ℝ) (PowerSeries.mk f) = PowerSeries.mk fun n => ((f n : ℚ) : ℝ) := by
  ext n; simp

/-- **The normalized local mass sum $A^*_p(S)$ for the true ternary genera at an odd prime** (Def. 4.6, $n = 3$):
$\beta_{3,p}(\widetilde S) = 1 - p^{-2}$ is the density of the unimodular genus. -/
def trueAodd (v : HeightOneSpectrum (𝓞 ℚ)) (S : LocalSqCl v) : ℝ :=
  (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S 1}, (1 - (((pv v : ℕ) : ℝ) ^ 2)⁻¹) / G.beta) +
    ∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S (-1)}, (1 - (((pv v : ℕ) : ℝ) ^ 2)⁻¹) / G.beta

/-- **The normalized local mass sum $B^*_p(S)$ for the true ternary genera at an odd prime.** -/
def trueBodd (v : HeightOneSpectrum (𝓞 ℚ)) (S : LocalSqCl v) : ℝ :=
  (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S 1}, (1 - (((pv v : ℕ) : ℝ) ^ 2)⁻¹) / G.beta) -
    ∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S (-1)}, (1 - (((pv v : ℕ) : ℝ) ^ 2)⁻¹) / G.beta

theorem ordZ_zSqCl_pow_mul (v : HeightOneSpectrum (𝓞 ℚ)) {w : ℤ} (hw : ¬ (pv v : ℤ) ∣ w) (ν : ℕ) :
    SqCl.ordZ (localOrd v) (localUnits_le_ker v) (zSqCl v ((pv v : ℤ) ^ ν * w)) = ν := by
  have hp := pv_prime' v
  haveI := Fact.mk hp
  have hw0 : w ≠ 0 := by rintro rfl; exact hw (dvd_zero _)
  rw [ordZ_zSqCl_eq v (mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.ne_zero)) hw0),
    padicValInt.mul (pow_ne_zero _ (by exact_mod_cast hp.ne_zero)) hw0, padicValInt.eq_zero_of_not_dvd hw]
  simp [padicValInt]

/-- **Theorem 5.4 for $A^*$, $n = 3$, $p$ odd, true local genera** (unconditional): with $q = p$, $X = p^{-s}$,
$$\Bigl(\sum_\nu A^*_p(p^\nu w)X^\nu\Bigr)(1 - q^{-1}X)(1 - q^{-3}X^2) = 1 - q^{-6}X^3.$$ -/
@[kb "hanke2011structure" "Thm. 5.4, p. 23 (n = 3, F = Q, p odd); hanke2011ternary Lemma 3.1, p. 7"]
theorem theorem_5_4_odd_A (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal) {w : ℤ}
    (hw : ¬ (pv v : ℤ) ∣ w) :
    PowerSeries.mk (fun ν => trueAodd v (zSqCl v ((pv v : ℤ) ^ ν * w))) *
        ((1 - C ((pv v : ℝ))⁻¹ * X) * (1 - C (((pv v : ℝ))⁻¹ ^ 3) * X ^ 2)) =
      1 - C (((pv v : ℝ))⁻¹ ^ 6) * X ^ 3 := by
  have hq : (1 : ℚ) < (pv v : ℚ) := by exact_mod_cast (pv_prime' v).one_lt
  have h := congrArg (PowerSeries.map (Rat.castHom ℝ)) (lemma_3_1 hq (negOneChar (pv v)) 1)
  simp only [map_mul, map_sub, map_one, map_pow, PowerSeries.map_C, PowerSeries.map_X, map_mk_rat,
    eq_ratCast, Rat.cast_inv, Rat.cast_natCast] at h
  simp only [← map_pow (C (R := ℝ)), ← map_mul (C (R := ℝ))] at h
  convert h using 3
  funext ν
  unfold trueAodd
  have hS := ordZ_zSqCl_pow_mul v hw ν
  rw [Odd7.odd_A hv _ (by rw [hS]; positivity), hS, Int.toNat_natCast]

/-- **Theorem 5.4 for $B^*$, $n = 3$, $p$ odd, true local genera** (unconditional): with $\varepsilon' = (-1/p)$,
$$\Bigl(\sum_\nu B^*_p(p^\nu w)X^\nu\Bigr)(1 - q^{-2}X^2) = 1 + \varepsilon'q^{-2}X + q^{-4}X^2.$$ -/
@[kb "hanke2011structure" "Thm. 5.4, p. 23 (n = 3, F = Q, p odd); hanke2011ternary Lemma 3.2, p. 8"]
theorem theorem_5_4_odd_B (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal) {w : ℤ}
    (hw : ¬ (pv v : ℤ) ∣ w) :
    PowerSeries.mk (fun ν => trueBodd v (zSqCl v ((pv v : ℤ) ^ ν * w))) *
        (1 - C (((pv v : ℝ))⁻¹ ^ 2) * X ^ 2) =
      1 + C (((negOneChar (pv v) : ℤ) : ℝ) * ((pv v : ℝ))⁻¹ ^ 2) * X + C (((pv v : ℝ))⁻¹ ^ 4) * X ^ 2 := by
  have hq : (1 : ℚ) < (pv v : ℚ) := by exact_mod_cast (pv_prime' v).one_lt
  have h := congrArg (PowerSeries.map (Rat.castHom ℝ)) (lemma_3_2 hq (negOneChar (pv v)) 1)
  simp only [map_mul, map_sub, map_add, map_one, map_pow, PowerSeries.map_C, PowerSeries.map_X, map_mk_rat,
    eq_ratCast, Rat.cast_inv, Rat.cast_natCast, Rat.cast_mul, Rat.cast_pow, Rat.cast_intCast] at h
  simp only [← map_pow (C (R := ℝ)), ← map_mul (C (R := ℝ))] at h
  convert h using 3
  funext ν
  unfold trueBodd
  have hS := ordZ_zSqCl_pow_mul v hw ν
  rw [Odd7.odd_B hv _ (by rw [hS]; positivity), hS, Int.toNat_natCast]

/-- At $v \mid 2$ no nondegenerate primitive ternary genus has a determinant class of valuation $0$ (Lemma 2.5). -/
theorem genStar_two_empty {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (T : LocalSqCl v)
    (hT : SqCl.ordZ (localOrd v) (localUnits_le_ker v) T = 0) (c : ℤ) :
    {G : LocGenus v 3 | G.IsGenStar T c} = ∅ := by
  ext G
  simp only [LocGenus.IsGenStar, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hn, -, hd, -⟩
  obtain ⟨D, hD, h0, hdim, hev, rfl⟩ := exists_genusOf v h2 G hn
  have hpo : Odd (ConwaySloane.unitProd D) :=
    Int.not_even_iff_odd.mp (fun he => odd_unitProd _ hD (even_iff_two_dvd.mp he))
  rw [det_genusOf v hD h0 hdim hev] at hd
  have hval : ConwaySloane.valSum D = 0 := by
    have := congrArg (SqCl.ordZ (localOrd v) (localUnits_le_ker v)) hd
    rw [ordZ_zSqCl v h2 _ hpo, hT] at this
    exact_mod_cast this
  have h2d := hessian_det_mem_span_two_of_odd (R := ℤ) (n := 3) (by decide) (formZ 3 D)
  rw [hessian_formZ hdim h0 hev, det_hessZ hdim h0, hval, pow_zero, one_mul, Ideal.mem_span_singleton] at h2d
  exact (Int.not_even_iff_odd.mpr hpo) (even_iff_two_dvd.mpr h2d)

/-- **The normalized local mass sums at $p = 2$ for the true ternary genera** (Def. 4.6, $n = 3$), normalized by the base
genus $G_0$ of $\det_H = 2u$: $A^*_2(S) = \sum_G\beta(G_0)/\beta(G)$, $B^*_2(S) = \sum_Gc_2(G)\beta(G_0)/\beta(G)$. -/
def trueA2 (v : HeightOneSpectrum (𝓞 ℚ)) (u : ℤ) (S : LocalSqCl v) : ℝ :=
  (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S 1}, (genusOf v 3 (baseList u)).beta / G.beta) +
    ∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S (-1)}, (genusOf v 3 (baseList u)).beta / G.beta

/-- See `trueA2`. -/
def trueB2 (v : HeightOneSpectrum (𝓞 ℚ)) (u : ℤ) (S : LocalSqCl v) : ℝ :=
  (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S 1}, (genusOf v 3 (baseList u)).beta / G.beta) -
    ∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S (-1)}, (genusOf v 3 (baseList u)).beta / G.beta

theorem trueAB2_eq (H2 : DyadicTernaryLocalMassTable) {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    {u : ℤ} (hu : u ∈ sqUnits) (h : ℕ) :
    trueA2 v u (zSqCl v (2 ^ h * u)) = ((dyadicA h : ℚ) : ℝ) ∧
      trueB2 v u (zSqCl v (2 ^ h * u)) = ((dyadicB (negOneChar u.toNat) h : ℚ) : ℝ) := by
  have huo : Odd u := by simp [sqUnits] at hu; rcases hu with rfl | rfl | rfl | rfl <;> decide
  have hS := ordZ_zSqCl v h2 h huo
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · rw [trueA2, trueB2, genStar_two_empty h2 _ hS 1, genStar_two_empty h2 _ hS (-1), dyadicA_zero, dyadicB,
      dyadicBmag_zero]
    simp
  · have hd := base_det_two h2 hu h
    have h1 : 1 ≤ SqCl.ordZ (localOrd v) (localUnits_le_ker v) (zSqCl v (2 ^ h * u)) := by rw [hS]; omega
    refine ⟨?_, ?_⟩
    · rw [trueA2, H2.A_eq v h2 _ _ h1 hd.1 hd.2.1 hd.2.2, hS, Int.toNat_natCast]
    · rw [trueB2, H2.B_eq v h2 _ _ h1 hd.1 hd.2.1 hd.2.2, hS, Int.toNat_natCast]
      obtain ⟨hvl, h0, hn, hev, -⟩ := baseList_props hu
      rw [hasse_genusOf v h2 hvl h0 hn hev, hasseQ_baseList hu, dyadicB]
      push_cast
      ring

/-- **Theorem 5.4 for $A^*$, $n = 3$, $F_{\mathfrak p} = \mathbb Q_2$, true local genera**, from Table 5.3
(`DyadicTernaryLocalMassTable`): with $X = 2^{-s}$ and $S = [2^hu]$,
$$\Bigl(\sum_h A^*_2(2^hu)X^h\Bigr)(1 - X/2)(1 - X^2/8) = X(1 - X^3/64).$$ -/
@[kb "hanke2011structure" "Thm. 5.4, p. 23 (n = 3, F_p = Q_2); hanke2011ternary Lemma 6.1, p. 22"]
theorem theorem_5_4_two_A (H2 : DyadicTernaryLocalMassTable) {v : HeightOneSpectrum (𝓞 ℚ)}
    (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {u : ℤ} (hu : u ∈ sqUnits) :
    PowerSeries.mk (fun h => trueA2 v u (zSqCl v (2 ^ h * u))) *
        ((1 - C (1 / 2 : ℝ) * X) * (1 - C (1 / 8 : ℝ) * X ^ 2)) = X * (1 - C (1 / 64 : ℝ) * X ^ 3) := by
  have h := congrArg (PowerSeries.map (Rat.castHom ℝ)) lemma_6_1
  simp only [map_mul, map_sub, map_one, map_pow, PowerSeries.map_C, PowerSeries.map_X, map_mk_rat,
    eq_ratCast] at h
  push_cast at h
  convert h using 3
  funext k
  exact (trueAB2_eq H2 h2 hu k).1

/-- **Theorem 5.4 for $B^*$, $n = 3$, $F_{\mathfrak p} = \mathbb Q_2$, true local genera**, from Table 5.3: with
$\varepsilon_u = (-1,u)_2$,
$$\Bigl(\sum_h B^*_2(2^hu)X^h\Bigr)(1 - X^2/4) = -\varepsilon_uX(1 + X/4 + X^2/16).$$ -/
@[kb "hanke2011structure" "Thm. 5.4, p. 23 (n = 3, F_p = Q_2); hanke2011ternary Lemma 6.2, p. 23"]
theorem theorem_5_4_two_B (H2 : DyadicTernaryLocalMassTable) {v : HeightOneSpectrum (𝓞 ℚ)}
    (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {u : ℤ} (hu : u ∈ sqUnits) :
    PowerSeries.mk (fun h => trueB2 v u (zSqCl v (2 ^ h * u))) * (1 - C (1 / 4 : ℝ) * X ^ 2) =
      -(C (((negOneChar u.toNat : ℤˣ) : ℤ) : ℝ) * X * (1 + C (1 / 4 : ℝ) * X + C (1 / 16 : ℝ) * X ^ 2)) := by
  have h := congrArg (PowerSeries.map (Rat.castHom ℝ)) (lemma_6_2 (negOneChar u.toNat))
  simp only [map_mul, map_sub, map_add, map_neg, map_one, map_pow, PowerSeries.map_C, PowerSeries.map_X,
    map_mk_rat, eq_ratCast] at h
  push_cast at h
  convert h using 3
  funext k
  exact (trueAB2_eq H2 h2 hu k).2

end

end QuadFormsKB.Hanke2011Structure

#print axioms QuadFormsKB.Hanke2011Structure.theorem_5_4_odd_A
#print axioms QuadFormsKB.Hanke2011Structure.theorem_5_4_odd_B
#print axioms QuadFormsKB.Hanke2011Structure.theorem_5_4_two_A
#print axioms QuadFormsKB.Hanke2011Structure.theorem_5_4_two_B
