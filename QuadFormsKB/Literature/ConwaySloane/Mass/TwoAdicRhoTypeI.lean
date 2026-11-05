/-
# The proportion $\rho$ next to an odd unimodular constituent

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), (3), p. 263, Table 1, p. 264, §5–6, pp. 265–266 (bibliography key `conwaysloane1988`).

Proves the former input `RhoValueTwoTypeI` (`rhoValueTwoTypeI_holds`), hence formula (3) at $p = 2$ and the mass
formula of Conway–Sloane unconditionally. For a decomposition $D$ with $f_1$ of type I, $U$ the blocks of exponent $0$
and $B$ the others lowered by one:
* $U$ is replaced by its normal form $O \perp E$, $O = \langle u\rangle$ or $\langle u, v\rangle$, $E$ even unimodular
  (`rho_low_congr`, by Theorem 10);
* $\rho(\langle u\rangle \perp E, B) = p_B\,\rho(E, B)$ (`rho_sq_cons`) and
  $\rho(\langle u, v\rangle \perp E, B)\,\rho_O(E) = \rho_O(E \perp 2B)\,\rho(E, B)$ (`rho_sq2_cons`), with
  $\rho_O(E)$, $\rho_O(E \perp 2B)$ from `rhoO_binary_E_intMat`, `rhoO_binary_blk_intMat`;
* $\rho(E, B) = P(E)$ if $f_2$ has type I (`rho_eq_rhoValue_typeII`) and $1$ otherwise (`rho_one_of_evenDiag`);
* $p_B$ from the symbol of $B$ (`pB_intMat`);
* the octane computations `rI_odd`, `rI_even` match the result with `rhoValue`.
Indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicPB
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicBinaryBlk

set_option linter.unusedSectionVars false

namespace QuadFormsKB.ConwaySloane.Mass.Two

open Matrix QuadFormsKB.Cassels QuadFormsKB.ConwaySloane

/-! ### $\rho(E, B) = 1$ when $B$ has even diagonal -/

theorem rho_one_of_evenDiag {a b : ℕ} {U : Matrix (Fin a) (Fin a) ℤ} (hUs : Uᵀ = U) (hUe : EvenDiag U)
    (hUd : ¬ 2 ∣ U.det) {B : Matrix (Fin b) (Fin b) ℤ} (hBs : Bᵀ = B) (hBe : EvenDiag B) : rho U B = 1 := by
  have hall : ∀ W : Matrix (Fin b) (Fin a) (ZMod (2 ^ 2)), Good U B (lift W) := by
    intro W
    unfold Good
    refine zpEquiv_of_even_congr hUs hUe hUd ?_ ?_ ?_
    · rw [transpose_add, transpose_smul, hUs, Matrix.transpose_mul, Matrix.transpose_mul, hBs,
        Matrix.transpose_transpose, Matrix.mul_assoc]
    · intro i j
      simp only [add_sub_cancel_left, Matrix.smul_apply, smul_eq_mul]
      exact dvd_mul_right _ _
    · intro i
      simp only [add_sub_cancel_left, Matrix.smul_apply, smul_eq_mul]
      rw [diag_quad hBs hBe (lift W) i]
      exact ⟨_, by ring⟩
  unfold rho
  have hc : Nat.card {W : Matrix (Fin b) (Fin a) (ZMod (2 ^ 2)) // Good U B (lift W)} =
      Nat.card (Matrix (Fin b) (Fin a) (ZMod (2 ^ 2))) := Nat.card_congr (Equiv.subtypeUnivEquiv hall)
  rw [hc]
  have hcardM : (Nat.card (Matrix (Fin b) (Fin a) (ZMod (2 ^ 2))) : ℝ) = 4 ^ (b * a) := by
    rw [Matrix.card_matrix]; simp [Nat.card_eq_fintype_card, ZMod.card, mul_comm]
  rw [hcardM, div_self (by positivity)]

/-! ### Two odd blocks -/

theorem rho_sq2_cons {u v : ℤ} (hu : u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) (hv : v = 1 ∨ v = 3 ∨ v = 5 ∨ v = 7)
    {L : List DyBlock} (hL : IsEvenList 0 L) {b : ℕ} {B : Matrix (Fin b) (Fin b) ℤ} (hBs : B.IsSymm)
    (hB : B.det ≠ 0) :
    rho (intMat (DyBlock.sq 0 u :: DyBlock.sq 0 v :: L)) B * rhoO (intMat [DyBlock.sq 0 u, DyBlock.sq 0 v]) (intMat L) =
      rhoO (intMat [DyBlock.sq 0 u, DyBlock.sq 0 v]) (blk 2 (intMat L) B) * rho (intMat L) B := by
  have hvL := isEvenList_valid hL
  have heL : ∀ c ∈ L, blockExp c = 0 := fun c hc => (hL c hc).1
  set E := intMat L
  have hEs : Eᵀ = E := (isSymm_intMat L).eq
  have hEe : EvenDiag E := isEvenList_evenDiag hL
  have hEd : ¬ 2 ∣ E.det := isEvenList_det hL
  set O := intMat [DyBlock.sq 0 u, DyBlock.sq 0 v]
  have hvO : ∀ c ∈ [DyBlock.sq 0 u, DyBlock.sq 0 v], c.Valid := by
    intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hu
    · exact hv
  have heO : ∀ c ∈ [DyBlock.sq 0 u, DyBlock.sq 0 v], blockExp c = 0 := by simp [blockExp]
  have hsO : ∀ c ∈ [DyBlock.sq 0 u, DyBlock.sq 0 v], IsSqBlock c := by simp [IsSqBlock]
  have hO2 := intMat_sq_mod_two [DyBlock.sq 0 u, DyBlock.sq 0 v] hvO heO hsO
  have hv : ∀ c ∈ DyBlock.sq 0 u :: DyBlock.sq 0 v :: L, c.Valid := by
    intro c hc; rcases List.mem_cons.mp hc with rfl | hc
    · exact hu
    · exact valid_cons_even hv hL c hc
  have he : ∀ c ∈ DyBlock.sq 0 u :: DyBlock.sq 0 v :: L, blockExp c = 0 := by
    intro c hc; rcases List.mem_cons.mp hc with rfl | hc
    · rfl
    · exact exp_cons_even hL c hc
  have hMs : (blk 2 E B).IsSymm := blk_isSymm (p := 2) (isSymm_intMat L) hBs
  have hMe : EvenDiag (blk 2 E B) := by
    intro i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · simp only [blk, submatrix_apply, finSumFinEquiv_symm_apply_castAdd, fromBlocks_apply₁₁]; exact hEe k
    · simp only [blk, submatrix_apply, finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₂₂, Matrix.smul_apply,
        smul_eq_mul]
      exact ⟨B k k, by push_cast; ring⟩
  have hM0 : (blk 2 E B).det ≠ 0 := by
    rw [blk_det]; exact mul_ne_zero (fun h => hEd (h ▸ dvd_zero _)) (mul_ne_zero (pow_ne_zero _ (by norm_num)) hB)
  have h1 := alphaP_blk_odd hvO heO (Or.inr rfl) hO2 hMs hMe hM0
  have h2 := alphaP_blk_two_rho hvL heL hBs hB
  have h3 := alphaP_blk_odd hvO heO (Or.inr rfl) hO2 (isSymm_intMat L) hEe (fun h => hEd (h ▸ dvd_zero _))
  have hU := alphaP_blk_two_rho hv he hBs hB
  have r1 : Reidx (blk 2 (intMat (DyBlock.sq 0 u :: DyBlock.sq 0 v :: L)) B) (blk 1 O (blk 2 E B)) := by
    rw [blk_eq_orthSum, blk_eq_orthSum 1, one_smul_int, blk_eq_orthSum]
    exact (reidx_orthSum_left _ (reidx_append [DyBlock.sq 0 u, DyBlock.sq 0 v] L)).trans
      (reidx_orthSum_assoc _ _ _).symm
  have r2 : Reidx (intMat (DyBlock.sq 0 u :: DyBlock.sq 0 v :: L)) (blk 1 O E) := by
    rw [blk_eq_orthSum 1, one_smul_int]
    exact reidx_append [DyBlock.sq 0 u, DyBlock.sq 0 v] L
  rw [alphaP_reidx r1, h1, h2] at hU
  rw [alphaP_reidx r2, h3] at hU
  have hpos2 := alphaP_pos Nat.prime_two (isSymm_intMat [DyBlock.sq 0 u, DyBlock.sq 0 v]) (det_intMat_ne _ hvO)
  have hpos3 := alphaP_pos Nat.prime_two (isSymm_intMat L) (fun h => hEd (h ▸ dvd_zero _))
  have hpos4 := alphaP_pos Nat.prime_two (smul_isSymm (p := 2) hBs) (smul_det_ne (p := 2) hB)
  have hne : alphaP 2 O * alphaP 2 E * alphaP 2 (((2 : ℕ) : ℤ) • B) ≠ 0 := by positivity
  apply mul_right_cancel₀ hne
  linear_combination hU.symm

/-! ### Replacing the unimodular part by a normal form -/

/-- The decomposition with the blocks of exponent $0$ replaced by `L`. -/
def replLow (D L : List DyBlock) : List DyBlock := L ++ D.filter fun b => ¬ (blockExp b = 0)

theorem low_replLow {D L : List DyBlock} (hL : ∀ c ∈ L, blockExp c = 0) : low (replLow D L) = L := by
  unfold low replLow
  rw [List.filter_append, List.filter_eq_self.mpr fun c hc => by simp [hL c hc]]
  rw [List.filter_filter]
  simp

theorem high_replLow {D L : List DyBlock} (hL : ∀ c ∈ L, blockExp c = 0) : high (replLow D L) = high D := by
  unfold high replLow
  rw [List.filter_append, List.filter_eq_nil_iff.mpr fun c hc => by simp [hL c hc], List.nil_append,
    List.filter_filter]
  congr 2
  funext c
  simp

theorem replLow_perm (D : List DyBlock) : D.Perm (replLow D (low D)) := by
  have := List.filter_append_perm (fun b => decide (blockExp b = 0)) D
  unfold replLow low
  simpa using this.symm

theorem blockSymbol_replLow {D L : List DyBlock} (hL : ∀ c ∈ L, blockExp c = 0)
    (hF : blockF (low D) = blockF L) : blockSymbol (replLow D L) = blockSymbol D := by
  rw [blockSymbol_perm (replLow_perm D)]
  unfold replLow
  exact (blockSymbol_congr_prefix hL exp_low hF.symm _)

theorem rho_eq_alpha {L : List DyBlock} (hv : ∀ c ∈ L, c.Valid) (he : ∀ c ∈ L, blockExp c = 0) {b : ℕ}
    {B : Matrix (Fin b) (Fin b) ℤ} (hBs : B.IsSymm) (hB : B.det ≠ 0) :
    rho (intMat L) B = alphaP 2 (blk 2 (intMat L) B) / (alphaP 2 (intMat L) * alphaP 2 (((2 : ℕ) : ℤ) • B)) := by
  rw [alphaP_blk_two_rho hv he hBs hB]
  have h1 := alphaP_pos Nat.prime_two (isSymm_intMat L) (det_intMat_ne _ hv)
  have h2 := alphaP_pos Nat.prime_two (smul_isSymm (p := 2) hBs) (smul_det_ne (p := 2) hB)
  field_simp

theorem rho_low_congr {D L : List DyBlock} (hD : ∀ c ∈ D, c.Valid) (hD0 : ∀ c ∈ D, 0 ≤ blockExp c)
    (hLv : ∀ c ∈ L, c.Valid) (hL : ∀ c ∈ L, blockExp c = 0) (hF : blockF (low D) = blockF L) :
    rho (intMat (low D)) (intMat (high D)) = rho (intMat L) (intMat (high D)) := by
  have hHv := valid_high hD
  have hBs := isSymm_intMat (high D)
  have hB := det_intMat_ne _ hHv
  set D' := replLow D L
  have hD'v : ∀ c ∈ D', c.Valid := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hLv c hc
    · exact hD c (List.mem_filter.mp hc).1
  have hD'0 : ∀ c ∈ D', 0 ≤ blockExp c := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact (hL c hc).ge
    · exact hD0 c (List.mem_filter.mp hc).1
  have hσ : blockSymbol D' = blockSymbol D := blockSymbol_replLow hL hF
  have hn : dyDim D = dyDim D' := by
    rw [dyDim_eq_sum, dyDim_eq_sum, ((replLow_perm D).map DyBlock.dim).sum_eq]
    have := congrArg TwoFactor.dim hF
    simp only [blockF] at this
    simp only [D', replLow, List.map_append, List.sum_append, this]
  -- the densities of the whole forms agree
  have hα : alphaP 2 (intMat D) = alphaP 2 (intMat D') :=
    alphaP_eq_of_blockSymbol_eq hD hD0 hD'v hD'0 hn.symm hσ.symm
  have hlowv := valid_low hD
  have hσL : blockSymbol (low D) = blockSymbol L := by
    have := blockSymbol_congr_prefix (e := 0) exp_low hL hF []
    simpa using this
  have hnL : dyDim L = dyDim (low D) := by
    rw [dyDim_eq_sum, dyDim_eq_sum]; exact (congrArg TwoFactor.dim hF).symm
  have hαL : alphaP 2 (intMat (low D)) = alphaP 2 (intMat L) :=
    alphaP_eq_of_blockSymbol_eq hlowv (fun c hc => (exp_low c hc).ge) hLv (fun c hc => (hL c hc).ge) hnL hσL
  have e1 : alphaP 2 (blk 2 (intMat (low D)) (intMat (high D))) =
      alphaP 2 (blk 2 (intMat L) (intMat (high D))) := by
    rw [← alphaP_reidx (reidx_split D hD0), hα, alphaP_reidx (reidx_split D' hD'0)]
    have hl : low D' = L := low_replLow hL
    have hh : high D' = high D := high_replLow hL
    rw [hl, hh]
  rw [rho_eq_alpha hlowv exp_low hBs hB, rho_eq_alpha hLv hL hBs hB, hαL, e1]

/-! ### The diagonal of $B$ and the type of $f_2$ -/

theorem exists_sq_of_typeI {H : List DyBlock} (h : (blockSymbol H 0).type = .I) :
    ∃ c ∈ H, IsSqBlock c ∧ blockExp c = 0 := by
  by_contra hn
  push Not at hn
  unfold blockSymbol at h
  simp only at h
  have : (H.filter fun c => blockExp c = ((0 : ℕ) : ℤ)).any (fun c => decide (IsSqBlock c)) = false := by
    rw [List.any_eq_false]
    intro c hc hsq
    have hc' := List.mem_filter.mp hc
    exact hn c hc'.1 (by simpa using hsq) (by simpa using hc'.2)
  rw [this] at h
  exact absurd h (by decide)

/-! ### The value of $\rho$ -/

theorem high_exp_nonneg {D : List DyBlock} (he : ∀ c ∈ D, 0 ≤ blockExp c) : ∀ c ∈ high D, 0 ≤ blockExp c := by
  intro c hc
  simp only [high, List.mem_map, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hc
  obtain ⟨c', ⟨hc', hc0⟩, rfl⟩ := hc
  rw [blockExp_lowerB]; have := he c' hc'; omega

theorem pII_even {E : List DyBlock} (hE : IsEvenList 0 E) :
    (pII (blockF E) : ℝ) = (1 + ((evenSign E).toInt : ℝ) * ((2 : ℝ) ^ E.length)⁻¹) / 2 := by
  rw [blockF_even hE]
  unfold pII
  simp only [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  push_cast; ring

/-- **The value of $\rho$ next to an odd unimodular constituent** (Conway–Sloane 1988, (3), p. 263, Table 1,
p. 264, §5–6, pp. 265–266; the paper does not prove (3) at $p = 2$): the former input `RhoValueTwoTypeI` holds. -/
@[kb "conwaysloane1988" "(3), p. 263; Table 1, p. 264; §5–6, pp. 265–266 (p = 2, rho next to an odd f_1)"]
theorem rhoValueTwoTypeI_holds : RhoValueTwoTypeI := by
  refine ⟨fun D hv he hI => ?_⟩
  obtain ⟨us, E, hus, hE, hlen, hne, hF⟩ := exists_normal 0 (low D) (valid_low hv) exp_low
  have hsq : ∃ c ∈ low D, IsSqBlock c := by
    have h' : (blockSymbol (low D) 0).type = .I := by rw [blockSymbol_low_zero]; exact hI
    obtain ⟨c, hc, hs, -⟩ := exists_sq_of_typeI h'
    exact ⟨c, hc, hs⟩
  have hus0 := hne hsq
  have hLv : ∀ c ∈ sqList 0 us ++ E, c.Valid := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hc; exact hus u hu
    · exact isEvenList_valid hE c hc
  have hL0 : ∀ c ∈ sqList 0 us ++ E, blockExp c = 0 := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hc; rfl
    · exact (hE c hc).1
  rw [rho_low_congr hv he hLv hL0 hF]
  have hHv := valid_high hv
  have hHe := high_exp_nonneg he
  have hBs := isSymm_intMat (high D)
  have hB := det_intMat_ne _ hHv
  have hσ1 : blockSymbol D 1 = blockSymbol (high D) 0 := by rw [blockSymbol_high]; rfl
  have hσ2 : blockSymbol D 2 = blockSymbol (high D) 1 := by rw [blockSymbol_high]; rfl
  have hσ0 : blockSymbol D 0 = blockF (sqList 0 us ++ E) := by
    rw [← blockSymbol_low_zero, blockSymbol_of_exp_zero exp_low, if_pos rfl, hF]
  have hpB := pB_intMat hHv hHe
  have hE0 : ∀ c ∈ E, blockExp c = 0 := fun c hc => (hE c hc).1
  -- `ρ(E, B)`
  have hρE : rho (intMat E) (intMat (high D)) =
      if (blockSymbol (high D) 0).type = .I then (pII (blockF E) : ℝ) else 1 := by
    split_ifs with h2
    · have hDEv : ∀ c ∈ replLow D E, c.Valid := by
        intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact isEvenList_valid hE c hc
        · exact hv c (List.mem_filter.mp hc).1
      have hDE0 : ∀ c ∈ replLow D E, 0 ≤ blockExp c := by
        intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact (hE0 c hc).ge
        · exact he c (List.mem_filter.mp hc).1
      have hS0 : blockSymbol (replLow D E) 0 = blockF E := by
        rw [← blockSymbol_low_zero, low_replLow hE0, blockSymbol_of_exp_zero hE0, if_pos rfl]
      have h0' : (blockSymbol (replLow D E) 0).type = .II := by rw [hS0, blockF_even hE]
      have h1' : (blockSymbol (replLow D E) 1).type = .I := by
        have : blockSymbol (replLow D E) 1 = blockSymbol (high (replLow D E)) 0 := by rw [blockSymbol_high]; rfl
        rw [this, high_replLow hE0]; exact h2
      have := rho_eq_rhoValue_typeII hDEv hDE0 h0' h1'
      rw [low_replLow hE0, high_replLow hE0] at this
      rw [this]
      unfold rhoValue
      rw [if_pos h0', if_neg (by rw [h1']; decide), hS0]
    · have h2' : (blockSymbol (high D) 0).type = .II := by
        cases h : (blockSymbol (high D) 0).type
        · exact absurd h h2
        · rfl
      exact rho_one_of_evenDiag (isSymm_intMat E).eq (isEvenList_evenDiag hE) (isEvenList_det hE) hBs.eq
        (evenDiag_intMat_of_typeII (high D) hHe h2')
  have hP := pII_even hE
  have hI0 : (blockSymbol D 0).type = .I := hI
  have hRV : ((rhoValue (blockSymbol D) : ℚ) : ℝ) =
      if (blockSymbol (high D) 0).type = .II then
        (if (blockSymbol (high D) 1).type = .I then 1 / 2 else (pII (blockSymbol (high D) 0) : ℝ))
      else ((rI (blockSymbol D 0) : ℝ) *
        (if (blockSymbol (high D) 1).type = .I then 1 else (rI (blockSymbol (high D) 0) : ℝ)) / 8) := by
    unfold rhoValue
    rw [if_neg (by rw [hI0]; decide), hσ1, hσ2]
    split_ifs <;> push_cast <;> ring
  match us, hlen, hus0, hus with
  | [u], _, _, hus =>
    have hu := hus u (by simp)
    have h := rho_sq_cons hu hE hBs hB
    rw [show rho (intMat (sqList 0 [u] ++ E)) (intMat (high D)) =
      rho (intMat (DyBlock.sq 0 u :: E)) (intMat (high D)) from rfl, h, hpB, hρE]
    have hb : blockF (sqList 0 [u] ++ E) = blockF (DyBlock.sq 0 u :: E) := rfl
    rw [hRV, hσ0, hb, rI_odd hu hE, hP]
    unfold pBsym
    rcases ht2 : (blockSymbol (high D) 0).type with _ | _ <;> rcases ht4 : (blockSymbol (high D) 1).type with _ | _ <;>
      simp only [reduceCtorEq, if_true, if_false] <;> push_cast <;> ring
  | [u, v], _, _, hus =>
    have hu := hus u (by simp)
    have hv' := hus v (by simp)
    have h := rho_sq2_cons hu hv' hE hBs hB
    have hO := rhoO_binary_E_intMat (isSymm_intMat E).eq (isEvenList_evenDiag hE) (isEvenList_det hE)
      (valid_odd hu) (valid_odd hv')
    have hOB := rhoO_binary_blk_intMat (isSymm_intMat E).eq (isEvenList_evenDiag hE) (isEvenList_det hE) hBs.eq
      (valid_odd hu) (valid_odd hv')
    have hc := card_four_dvd_even hE
    rw [show rho (intMat (sqList 0 [u, v] ++ E)) (intMat (high D)) =
      rho (intMat (DyBlock.sq 0 u :: DyBlock.sq 0 v :: E)) (intMat (high D)) from rfl]
    have hb : blockF (sqList 0 [u, v] ++ E) = blockF (DyBlock.sq 0 u :: DyBlock.sq 0 v :: E) := rfl
    have hdim : dyDim E = 2 * E.length := dyDim_even_list E fun c hc => (hE c hc).2
    -- `C`
    have hC : cBE (intMat E) (intMat (high D)) =
        if (blockSymbol (high D) 0).type = .I then 1 / 2
        else (1 + ((evenSign E).toInt : ℝ) * ((2 : ℝ) ^ E.length)⁻¹) / 2 := by
      split_ifs with h2
      · obtain ⟨c, hcm, hs, h0⟩ := exists_sq_of_typeI h2
        exact cBE_of_odd hBs.eq (exists_odd_diag (high D) hHv hHe ⟨c, hcm, hs, h0⟩)
      · have h2' : (blockSymbol (high D) 0).type = .II := by
          cases h : (blockSymbol (high D) 0).type
          · exact absurd h h2
          · rfl
        rw [cBE_of_evenDiag hBs.eq (evenDiag_intMat_of_typeII (high D) hHe h2'), hc]
        have : (8 : ℝ) ^ dyDim E ≠ 0 := by positivity
        field_simp
    have hx : (1 + ((evenSign E).toInt : ℝ) * ((2 : ℝ) ^ E.length)⁻¹) ≠ 0 := by
      have h1 := rI_ne_zero (f := blockF (DyBlock.sq 0 u :: E))
        (by
          have := blockSymbol_exists (DyBlock.sq 0 u :: E) (valid_cons_even hu hE) 0
          rwa [blockSymbol_of_exp_zero (exp_cons_even hE), if_pos rfl] at this)
        (by rw [blockF_cons_sq])
      rw [rI_odd hu hE] at h1
      intro h0; apply h1
      have : ((1 + ((evenSign E).toInt : ℚ) * ((2 : ℚ) ^ E.length)⁻¹ : ℚ) : ℝ) = 0 := by push_cast; exact h0
      exact_mod_cast this
    have h8 : (8 : ℝ) ^ dyDim E ≠ 0 := by positivity
    have hc' : (Nat.card {x : Matrix (Fin (dyDim E)) (Fin 1) (ZMod (2 ^ 3)) //
        (4 : ℤ) ∣ ((lift x)ᵀ * intMat E * lift x) 0 0} : ℝ) / 8 ^ dyDim E =
        (1 + ((evenSign E).toInt : ℝ) * ((2 : ℝ) ^ E.length)⁻¹) / 2 := by
      rw [hc]; field_simp
    rw [hO, hc', hOB, hC, hρE, hpB, hP] at h
    have hA : ((1 : ℝ) / 2) ^ dyDim E * (if (4 : ℤ) ∣ u + v then 1
        else (1 + ((evenSign E).toInt : ℝ) * ((2 : ℝ) ^ E.length)⁻¹) / 2) ≠ 0 := by
      split_ifs
      · positivity
      · exact mul_ne_zero (by positivity) (div_ne_zero hx two_ne_zero)
    have hρU := eq_div_of_mul_eq hA h
    rw [hρU, hRV, hσ0, hb, rI_even hu hv' hE]
    unfold pBsym
    have h2e : ((1 : ℝ) / 2) ^ dyDim E ≠ 0 := by positivity
    have hx2 : ((evenSign E).toInt : ℝ) + 2 ^ E.length ≠ 0 := by
      intro h0; apply hx; field_simp; linarith
    have hx3 : (2 : ℝ) ^ E.length + ((evenSign E).toInt : ℝ) ≠ 0 := by rwa [add_comm]
    by_cases h4 : (4 : ℤ) ∣ u + v <;>
    rcases ht2 : (blockSymbol (high D) 0).type with _ | _ <;> rcases ht4 : (blockSymbol (high D) 1).type with _ | _ <;>
      simp only [h4, reduceCtorEq, if_true, if_false] <;> push_cast <;> field_simp <;> ring

end QuadFormsKB.ConwaySloane.Mass.Two
