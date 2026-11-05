/-
# The 2-adic density of $U \oplus 2B$ when the first two constituents have type II

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), (3), p. 263, and §12, p. 281 (bibliography key `conwaysloane1988`).

**Proves** `alphaP_blk_two` (and `countN_blk_two`, `pMassDensity_blk_two`): for integral symmetric $U$ ($a \times a$, $\det U$ odd) and $B$ ($b \times b$,
$\det B \ne 0$), both with even diagonal,
$$\alpha_2(U \oplus 2B) = \alpha_2(U)\,\alpha_2(2B),$$
the 2-adic analogue of the odd-$p$ multiplicativity, from the exact count identity `Two.card_fromBlocks_even` at every
level $2^r$. Here $U \oplus 2B$ is `blk 2 U B`
(`blk 2 U B`, the variables of $U$ first). Indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicHensel
import QuadFormsKB.Literature.ConwaySloane.Mass.OddProof

set_option linter.unusedSectionVars false

namespace QuadFormsKB.ConwaySloane.Mass.Two

open Matrix Finset Filter

variable {a b : ℕ}

theorem isUnit_odd {r : ℕ} {z : ℤ} (hz : ¬ 2 ∣ z) : IsUnit (z : ZMod (2 ^ r)) := by
  obtain ⟨k, hk⟩ : ∃ k, z = 2 * k + 1 := ⟨z / 2, by omega⟩
  rw [hk]
  push_cast
  have : IsNilpotent ((2 : ZMod (2 ^ r)) * k) := (Commute.all _ _).isNilpotent_mul_right (two_nilpotent r)
  exact this.isUnit_add_one

/-- **The block count identity over $\mathbb Z/2^r$ for type II neighbours**: $N_r(U \perp 2B) = 2^{rab}N_r(U)N_r(2B)$
when $U$, $B$ have even diagonal and $\det U$ is odd. -/
@[kb "conwaysloane1988" "(18), p. 281 (splitting off a type II unimodular constituent, p = 2)"]
theorem countN_blk_two {U : Matrix (Fin a) (Fin a) ℤ} {B : Matrix (Fin b) (Fin b) ℤ} (hUs : U.IsSymm)
    (hUe : EvenDiag U) (hUd : ¬ 2 ∣ U.det) (hBs : B.IsSymm) (hBe : EvenDiag B) (r : ℕ) :
    countN 2 r (blk 2 U B) = (2 ^ r) ^ (b * a) * countN 2 r U * countN 2 r (((2 : ℕ) : ℤ) • B) := by
  have : NeZero (2 ^ r) := ⟨by positivity⟩
  have hsm : (((2 : ℕ) : ℤ) • B).map (Int.castRingHom (ZMod (2 ^ r))) = (2 : ZMod (2 ^ r)) • red r B := by
    rw [show (((2 : ℕ) : ℤ) • B).map (Int.castRingHom (ZMod (2 ^ r))) = red r (((2 : ℕ) : ℤ) • B) from rfl,
      red_smul]
    norm_num
  have hmap : (blk 2 U B).map (Int.castRingHom (ZMod (2 ^ r))) =
      (fromBlocks (red r U) 0 0 ((2 : ZMod (2 ^ r)) • red r B)).submatrix finSumFinEquiv.symm
        finSumFinEquiv.symm := by
    rw [blk, ← Matrix.submatrix_map, fromBlocks_map, Matrix.map_zero _ (map_zero _),
      Matrix.map_zero _ (map_zero _), hsm]
  have hU' : IsUnit (red r U).det := by
    rw [show (red r U).det = ((U.det : ℤ) : ZMod (2 ^ r)) from (RingHom.map_det _ _).symm]
    exact isUnit_odd hUd
  unfold countN
  rw [hmap, card_sol_submatrix, card_fromBlocks_even hUs.eq hUe hU' hBs.eq hBe, hsm]
  congr 2
  rw [Fintype.card_eq_nat_card, Matrix.card_matrix]
  simp [Nat.card_eq_fintype_card, ZMod.card, mul_comm]

/-- **$\alpha_2(U \perp 2B) = \alpha_2(U)\,\alpha_2(2B)$** when $U$ and $B$ have even diagonal and $\det U$ is odd
(the first two Jordan constituents of $U \perp 2B$ have type II). -/
@[kb "conwaysloane1988" "§12, p. 281 (splitting off a type II constituent next to type II, p = 2)"]
theorem alphaP_blk_two {U : Matrix (Fin a) (Fin a) ℤ} {B : Matrix (Fin b) (Fin b) ℤ} (hUs : U.IsSymm)
    (hUe : EvenDiag U) (hUd : ¬ 2 ∣ U.det) (hBs : B.IsSymm) (hBe : EvenDiag B) (hB : B.det ≠ 0) :
    alphaP 2 (blk 2 U B) = alphaP 2 U * alphaP 2 (((2 : ℕ) : ℤ) • B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU0 : U.det ≠ 0 := fun h => hUd (h ▸ dvd_zero _)
  have hblk0 : (blk 2 U B).det ≠ 0 := by
    rw [blk_det]; exact mul_ne_zero hU0 (mul_ne_zero (pow_ne_zero _ (by norm_num)) hB)
  obtain ⟨r1, h1⟩ := alphaP_stabilizes Nat.prime_two (blk_isSymm (p := 2) hUs hBs) hblk0
  obtain ⟨r2, h2⟩ := alphaP_stabilizes Nat.prime_two hUs hU0
  obtain ⟨r3, h3⟩ := alphaP_stabilizes Nat.prime_two (smul_isSymm (p := 2) hBs) (smul_det_ne (p := 2) hB)
  set r := max r1 (max r2 r3)
  rw [← h1 r (le_max_left _ _), ← h2 r (le_trans (le_max_left _ _) (le_max_right _ _)),
    ← h3 r (le_trans (le_max_right _ _) (le_max_right _ _)), countN_blk_two hUs hUe hUd hBs hBe, tri_add]
  push_cast
  rw [mul_add, mul_add, pow_add, pow_add, ← pow_mul, mul_comm (r : ℕ) (b * a)]
  field_simp

/-- **The 2-mass of $U \perp 2B$** for type II neighbours: $m_2(U \perp 2B) = m_2(U)\,m_2(B)\,2^{as/2}$,
$s = b + \operatorname{ord}_2\det B$. -/
@[kb "conwaysloane1988" "(3), p. 263 (one step of the induction over the constituents, p = 2, type II)"]
theorem pMassDensity_blk_two {U : Matrix (Fin a) (Fin a) ℤ} {B : Matrix (Fin b) (Fin b) ℤ} (hUs : U.IsSymm)
    (hUe : EvenDiag U) (hUd : ¬ 2 ∣ U.det) (hBs : B.IsSymm) (hBe : EvenDiag B) (hB : B.det ≠ 0) :
    pMassDensity 2 (blk 2 U B) = pMassDensity 2 U * pMassDensity 2 B *
      (2 : ℝ) ^ ((((b + padicValInt 2 B.det : ℕ) : ℝ) * a) / 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU0 : U.det ≠ 0 := fun h => hUd (h ▸ dvd_zero _)
  have hvU : padicValInt 2 U.det = 0 := padicValInt.eq_zero_of_not_dvd (by exact_mod_cast hUd)
  have hv : padicValInt 2 (blk 2 U B).det = b + padicValInt 2 B.det := by
    rw [blk_det, padicValInt.mul hU0 (mul_ne_zero (pow_ne_zero _ (by norm_num)) hB), hvU,
      zero_add, padicValInt.mul (pow_ne_zero _ (by norm_num)) hB]
    congr 1
    unfold padicValInt
    simp
  have hαB := alphaP_smul_prime Nat.prime_two hBs hB
  have hαU := (alphaP_pos Nat.prime_two hUs hU0).ne'
  have hαB0 := (alphaP_pos Nat.prime_two hBs hB).ne'
  unfold pMassDensity
  rw [alphaP_blk_two hUs hUe hUd hBs hBe hB, hαB, hv, hvU, ← Real.rpow_natCast ((2 : ℕ) : ℝ) (b * (b + 1) / 2),
    cast_half]
  simp only [Nat.cast_zero, zero_mul, zero_div, Real.rpow_zero]
  set s : ℝ := ((b + padicValInt 2 B.det : ℕ) : ℝ)
  have hs : s = (b : ℝ) + (padicValInt 2 B.det : ℝ) := by simp [s]
  have e : ((2 : ℕ) : ℝ) ^ (s * (((a + b : ℕ) : ℝ) + 1) / 2) = ((2 : ℕ) : ℝ) ^ ((b : ℝ) * ((b : ℝ) + 1) / 2) *
      ((2 : ℕ) : ℝ) ^ ((padicValInt 2 B.det : ℝ) * ((b : ℝ) + 1) / 2) * ((2 : ℕ) : ℝ) ^ (s * a / 2) := by
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1
    rw [hs]; push_cast; ring
  rw [e]
  have : (0 : ℝ) < ((2 : ℕ) : ℝ) ^ ((b : ℝ) * ((b : ℝ) + 1) / 2) := by positivity
  push_cast at this ⊢
  field_simp

end QuadFormsKB.ConwaySloane.Mass.Two
