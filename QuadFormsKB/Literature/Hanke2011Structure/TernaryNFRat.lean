/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.Hanke2011Structure.TernaryNF
import QuadFormsKB.Literature.Hanke2011Structure.TernaryFinal
import QuadFormsKB.Tamagawa.Dyadic7CountMain
import QuadFormsKB.Literature.OMeara.Sec73Two
import QuadFormsKB.Literature.OMeara.Sec72Local
import QuadFormsKB.Equiv.NumberFieldRat

/-!
# The number-field local input `TernaryLocalTablesNF` holds for $F = \mathbb Q$

Sanity check of the named input `TernaryLocalTablesNF` (`TernaryNF.lean`): for $F = \mathbb Q$ every field is already
proved in the library (`oddTernaryLocalData_holds`, `Dyadic7.dyadicTernaryLocalMassTable_holds`, `beta_baseList`), and
this file only matches the formulations:

* $N\mathfrak p = p$ (`qv_eq_pv`), so `qv`/`epsOdd` of the input are `pv`/`negOneChar (pv _)`;
* a primitive nondegenerate ternary $\mathbb Z_2$-genus has Hessian determinant of valuation $\ge 1$
  (`one_le_ord_of_genus`), giving `fin` and `dy_zero` at $\mathfrak p \mid 2$;
* for $x \in \mathbb Q_2^\times$ in the rational square class of $2^a u$ ($u$ odd), $(-1,x)_2 = (-1,u)_2$ is
  `negOneChar u`
  (`hilbert_neg_one_dyadic`), which matches the sign `dyadicB` of Table 5.3 (`dy_B`).

Indices are 0-based.
-/

open IsDedekindDomain NumberField Finset

namespace QuadFormsKB.Hanke2011Structure

open QuadFormsKB.Dyadic7 QuadFormsKB.Hanke2011Ternary QuadFormsKB.Hanke2011Ternary.NF Cassels QuadFormsKB.ConwaySloane

open Classical

noncomputable section

local notation "pv" => ConwaySloane.Mass.pv
local notation "ordS" v => SqCl.ordZ (localOrd v) (localUnits_le_ker v)

/-- $N\mathfrak p = p$ for a prime $\mathfrak p$ of $\mathcal O_{\mathbb Q}$. -/
theorem qv_eq_pv (v : HeightOneSpectrum (𝓞 ℚ)) : qv v = pv v :=
  QuadFormsKB.LocalDensity.NF.absNorm_rat v

/-- A nondegenerate ternary $\mathbb Z_2$-genus has Hessian determinant of valuation $\ge 1$. -/
theorem one_le_ord_of_genus {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (S : LocalSqCl v)
    (G : LocGenus v 3) (hn : G.Nondeg) (hd : G.det = S) : 1 ≤ (ordS v) S := by
  obtain ⟨D, hD, h0, hdim, hev, rfl⟩ := exists_genusOf v h2 G hn
  have hpo : Odd (unitProd D) :=
    Int.not_even_iff_odd.mp (fun he => odd_unitProd _ hD (even_iff_two_dvd.mp he))
  rw [det_genusOf v hD h0 hdim hev] at hd
  have hval : (ordS v) S = (valSum D : ℤ) := by rw [← hd, ordZ_zSqCl v h2 _ hpo]
  by_contra hlt
  have hv0 : valSum D = 0 := by omega
  have h2d := hessian_det_mem_span_two_of_odd (R := ℤ) (n := 3) (by decide) (formZ 3 D)
  rw [hessian_formZ hdim h0 hev, det_hessZ hdim h0, hv0, pow_zero, one_mul, Ideal.mem_span_singleton] at h2d
  exact (Int.not_even_iff_odd.mpr hpo) (even_iff_two_dvd.mpr h2d)

/-- The Hilbert symbol of rationals at a prime $v \mid 2$ of $\mathbb Q$ is the one over $\mathbb Q_2$. -/
theorem hilb_rat_two {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (a b : ℚ) :
    hilbertSymbol (v.adicCompletion ℚ) (algebraMap ℚ (v.adicCompletion ℚ) a)
        (algebraMap ℚ (v.adicCompletion ℚ) b) = hilbertSymbol ℚ_[2] (a : ℚ_[2]) (b : ℚ_[2]) := by
  have h := NFPlace.toRatPlace_hilbert (NFPlace.finite v) a b
  have hp : Rat.HeightOneSpectrum.primesEquiv v = ⟨2, Nat.prime_two⟩ :=
    Subtype.ext ((two_mem_iff_pv v).mp h2)
  simp only [NFPlace.toRatPlace, hp] at h
  simpa [NFPlace.hilbert, RatPlace.hilbert] using h.symm

/-- $(-1, 2)_{\mathbb Q_2} = 1$, in the completion of $\mathbb Q$ at $v \mid 2$. -/
theorem hilb_neg_one_two {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) :
    hilbertSymbol (v.adicCompletion ℚ) (algebraMap ℚ (v.adicCompletion ℚ) (-1))
        (algebraMap ℚ (v.adicCompletion ℚ) 2) = 1 := by
  rw [hilb_rat_two h2, hilbertSymbol_comm]
  have := (OMeara.hilbertSymbol_two_adic_of_odd (-1) (-1) (by decide) (by decide)).2
  simp only [Int.cast_neg, Int.cast_one] at this
  rw [show ((2 : ℚ) : ℚ_[2]) = (2 : ℚ_[2]) by norm_num, show (((-1 : ℚ)) : ℚ_[2]) = -1 by norm_num, this]
  decide

/-- $(-1, 2^k) = 1$. -/
theorem hilb_neg_one_two_pow {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (k : ℕ) :
    hilbertSymbol (v.adicCompletion ℚ) (algebraMap ℚ (v.adicCompletion ℚ) (-1))
        (algebraMap ℚ (v.adicCompletion ℚ) (2 ^ k)) = 1 := by
  induction k with
  | zero => simp [hilbertSymbol_one_right]
  | succ k ih =>
    rw [pow_succ, map_mul, OMeara.hilbertSymbol_mul_right_finite v (by simp) (by simp) (by simp), ih,
      hilb_neg_one_two h2, one_mul]

/-- $(-1, u)_2$ for odd $u \in \{1,3,5,7\}$ is `negOneChar u`. -/
theorem hilb_neg_one_unit {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {u : ℤ} (hu : u ∈ sqUnits) :
    hilbertSymbol (v.adicCompletion ℚ) (algebraMap ℚ (v.adicCompletion ℚ) (-1))
        (algebraMap ℚ (v.adicCompletion ℚ) (u : ℚ)) = ((negOneChar u.toNat : ℤˣ) : ℤ) := by
  rw [hilb_rat_two h2]
  have huo : Odd u := by simp [sqUnits] at hu; rcases hu with rfl | rfl | rfl | rfl <;> decide
  have := (OMeara.hilbertSymbol_two_adic_of_odd (-1) u (by decide) huo).1
  simp only [Int.cast_neg, Int.cast_one] at this
  rw [show (((-1 : ℚ)) : ℚ_[2]) = -1 by norm_num, show ((u : ℚ) : ℚ_[2]) = (u : ℚ_[2]) by norm_num, this]
  simp only [sqUnits, Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl <;> decide

/-- **The Hilbert symbol $(-1,x)$ at $v \mid 2$, for $x$ in the rational square class of $2^a u$**, is
`negOneChar u`. -/
theorem hilbert_neg_one_dyadic {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (a : ℕ) {u : ℤ}
    (hu : u ∈ sqUnits) (x : (v.adicCompletion ℚ)ˣ) (hx : rhoLocal v (zSqCl v (2 ^ a * u)) = SqCl.mk x) :
    hilbertSymbol (v.adicCompletion ℚ) (-1) (x : v.adicCompletion ℚ) = ((negOneChar u.toNat : ℤˣ) : ℤ) := by
  have huo : Odd u := by simp [sqUnits] at hu; rcases hu with rfl | rfl | rfl | rfl <;> decide
  have hu0 : u ≠ 0 := by rintro rfl; exact absurd huo (by decide)
  have hz : (2 : ℤ) ^ a * u ≠ 0 := mul_ne_zero (pow_ne_zero _ two_ne_zero) hu0
  rw [zSqCl_of_ne v hz, rhoLocal_mk] at hx
  obtain ⟨t, -, ht⟩ := QuotientGroup.eq.mp hx
  have hxt : (x : v.adicCompletion ℚ) = (((2 : ℚ) ^ a : ℚ) : v.adicCompletion ℚ) * (u : v.adicCompletion ℚ) *
      ((t : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ^ 2 := by
    have := congrArg (fun z : (v.adicCompletion ℚ)ˣ => ((Units.mk0 (((((2 : ℤ) ^ a * u : ℤ)) : ℚ) :
      v.adicCompletion ℚ) (by simpa using hz) * z : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) ht
    simp only [powMonoidHom_apply, mul_inv_cancel_left, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_mk0] at this
    rw [← this]
    push_cast
    ring
  rw [hxt, SqDual.hilbertSymbol_mul_sq_right _ _ _ _ t.ne_zero]
  have e1 : (-1 : v.adicCompletion ℚ) = algebraMap ℚ _ (-1) := by simp
  have e2 : (((2 : ℚ) ^ a : ℚ) : v.adicCompletion ℚ) = algebraMap ℚ _ (2 ^ a) := rfl
  have e3 : ((u : ℤ) : v.adicCompletion ℚ) = algebraMap ℚ _ (u : ℚ) := by simp
  rw [e1, e2, e3, OMeara.hilbertSymbol_mul_right_finite v (by simp) (by simp) (by simpa using hu0),
    hilb_neg_one_two_pow h2, hilb_neg_one_unit h2 hu, one_mul]

theorem toSign_units (e : ℤˣ) : toSign (e : ℤ) = e := by
  rcases Int.units_eq_one_or e with rfl | rfl <;> simp [toSign]

/-- **`TernaryLocalTablesNF` holds for $F = \mathbb Q$** (sanity check of the named number-field input): its odd part is
`oddTernaryLocalData_holds` (with $N\mathfrak p = p$), its dyadic part is
`Dyadic7.dyadicTernaryLocalMassTable_holds` with the generic density $\beta_2(G_0) = 3/16$ (`beta_baseList`), and the
sign of `dy_B` is $(-1, x)_2 = (-1, u)_2$ = `negOneChar u` for $x$ in the rational square class of $2^a u$
(`hilbert_neg_one_dyadic`). Unconditional.

Statement: $$\texttt{TernaryLocalTablesNF}\ \mathbb Q.$$ -/
@[kb "hanke2011ternary" "§§2-5, Tables 2 and 5.3 (F = Q)"]
theorem ternaryLocalTablesNF_rat : TernaryLocalTablesNF ℚ := by
  have HO := oddTernaryLocalData_holds
  have H2 := dyadicTernaryLocalMassTable_holds
  -- the dyadic setup for a class `S` of valuation `a ≥ 1`
  have setup : ∀ (v : HeightOneSpectrum (𝓞 ℚ)), (2 : 𝓞 ℚ) ∈ v.asIdeal → ∀ S : LocalSqCl v, 1 ≤ (ordS v) S →
      ∃ u ∈ sqUnits, S = zSqCl v (2 ^ ((ordS v) S).toNat * u) ∧
        (genusOf v 3 (baseList u)).Nondeg ∧ (genusOf v 3 (baseList u)).Prim ∧
        (genusOf v 3 (baseList u)).det = tildeTernary v S ∧ (genusOf v 3 (baseList u)).beta = 3 / 16 := by
    intro v h2 S h1
    obtain ⟨u, hu, hS⟩ := exists_zSqCl_eq v h2 S ((ordS v) S).toNat (by omega)
    have hd := base_det_two h2 hu ((ordS v) S).toNat
    rw [← hS] at hd
    exact ⟨u, hu, hS, hd.1, hd.2.1, hd.2.2, beta_baseList h2 hu⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v S c
    by_cases h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal
    · by_cases h1 : 1 ≤ (ordS v) S
      · obtain ⟨u, hu, hS, -⟩ := setup v h2 S h1
        rw [hS, genStar_eq_image h2 _ hu]
        exact Finset.finite_toSet _
      · have : {G : LocGenus v 3 | G.IsGenStar S c} = ∅ := by
          ext G
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨hn, -, hd, -⟩
          exact h1 (one_le_ord_of_genus h2 S G hn hd)
        rw [this]; exact Set.finite_empty
    · exact HO.fin v h2 S c
  · intro v h2 S hS
    have := HO.A_eq v h2 S hS
    simpa only [qv_eq_pv, epsOdd] using this
  · intro v h2 S hS
    have := HO.B_eq v h2 S hS
    simpa only [qv_eq_pv, epsOdd] using this
  · intro v h2 S hS
    have := HO.unimod v h2 S hS
    simpa only [qv_eq_pv] using this
  · intro _ v h2 S h0 c
    ext G
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hn, -, hd, -⟩
    have := one_le_ord_of_genus h2 S G hn hd
    omega
  · intro _ v h2 S h1
    obtain ⟨u, hu, hS, hn, hp, hd, hb⟩ := setup v h2 S h1
    have hA := H2.A_eq v h2 S _ h1 hn hp hd
    rw [hb] at hA
    exact hA
  · intro _ v h2 S h1 x hx
    obtain ⟨u, hu, hS, hn, hp, hd, hb⟩ := setup v h2 S h1
    have hB := H2.B_eq v h2 S _ h1 hn hp hd
    rw [hb] at hB
    rw [hB]
    obtain ⟨hvl, h0, hn3, hev, -⟩ := baseList_props hu
    rw [hS] at hx
    rw [hasse_genusOf v h2 hvl h0 hn3 hev, hasseQ_baseList hu]
    have hh := hilbert_neg_one_dyadic h2 _ hu x hx
    rw [hh, toSign_units, dyadicB]
    push_cast
    ring

end

end QuadFormsKB.Hanke2011Structure

#print axioms QuadFormsKB.Hanke2011Structure.ternaryLocalTablesNF_rat
