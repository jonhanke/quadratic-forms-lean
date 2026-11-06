/-
# The symbol, determinant and parity of an integral block model

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), (3), p. 263 (bibliography key `conwaysloane1988`); *Sphere Packings, Lattices and Groups* Ch. 15, §7.3–7.4 for the symbols.

For a list $D$ of Cassels' blocks with nonnegative exponents: the symbol of `high D` (the blocks of positive exponent,
lowered) is the shifted symbol (`blockSymbol_high`); `low D` (the blocks of exponent $0$) has the constituent of scale
$1$ of $D$ (`blockSymbol_low_zero`); `intMat D` has the 2-adic symbol `blockSymbol D` (`isTwoSymbolOf_intMat`), its
determinant has 2-adic valuation $\sum_b e_b\dim b$ (`padicValInt_det_intMat`), and its diagonal is even when the
constituent of scale $1$ has type II (`evenDiag_intMat`). Indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicBlocks

set_option linter.unusedSectionVars false

namespace QuadFormsKB.ConwaySloane.Mass.Two

open Matrix QuadFormsKB.Cassels QuadFormsKB.ConwaySloane

/-- The 2-adic symbol shifted down by one scale. -/
def shiftT (σ : TwoSymbol) : TwoSymbol := fun k => σ (k + 1)

theorem blockExp_lowerB (b : DyBlock) : blockExp (lowerB b) = blockExp b - 1 := by cases b <;> rfl
theorem dim_lowerB (b : DyBlock) : (lowerB b).dim = b.dim := by cases b <;> rfl
theorem sign_lowerB (b : DyBlock) : blockSign (lowerB b) = blockSign b := by cases b <;> rfl
theorem oddity_lowerB (b : DyBlock) : blockOddity (lowerB b) = blockOddity b := by cases b <;> rfl
theorem isSq_lowerB (b : DyBlock) : decide (IsSqBlock (lowerB b)) = decide (IsSqBlock b) := by cases b <;> rfl

theorem blockSymbol_of_filter {L₁ L₂ : List DyBlock} {k k' : ℕ}
    (h : L₁.filter (fun b => blockExp b = k) = (L₂.filter fun b => blockExp b = k').map lowerB) :
    blockSymbol L₁ k = blockSymbol L₂ k' := by
  unfold blockSymbol
  simp only
  rw [h]
  simp only [List.map_map, Function.comp_def, dim_lowerB, sign_lowerB, oddity_lowerB, List.any_map, isSq_lowerB]

/-- **The symbol of the lowered blocks of positive exponent is the shifted symbol.** -/
theorem blockSymbol_high (D : List DyBlock) : blockSymbol (high D) = shiftT (blockSymbol D) := by
  funext k
  refine blockSymbol_of_filter ?_
  simp only [high, List.filter_map, List.filter_filter]
  congr 1
  refine List.filter_congr fun b _ => ?_
  simp only [Function.comp_apply, blockExp_lowerB]
  by_cases h : blockExp b = 0 <;> simp [h] <;> omega

theorem blockSymbol_low_zero (D : List DyBlock) : blockSymbol (low D) 0 = blockSymbol D 0 := by
  have : blockSymbol (low D) 0 = blockSymbol (D.map id) 0 := by
    unfold blockSymbol low
    simp [List.filter_filter]
  rw [this, List.map_id]

theorem blockSymbol_low_pos (D : List DyBlock) {k : ℕ} (hk : k ≠ 0) : blockSymbol (low D) k = TwoFactor.trivial := by
  unfold blockSymbol low
  have : (D.filter fun b => blockExp b = 0).filter (fun b => blockExp b = (k : ℤ)) = [] := by
    rw [List.filter_filter, List.filter_eq_nil_iff]
    intro b _
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    intro h; rw [h]; exact_mod_cast hk
  simp only [this]
  rfl

/-- `intMat D` has the 2-adic symbol `blockSymbol D`. -/
theorem isTwoSymbolOf_intMat (D : List DyBlock) (hv : ∀ b ∈ D, b.Valid) (he : ∀ b ∈ D, 0 ≤ blockExp b) :
    IsTwoSymbolOf ((intMat D).map (Int.cast : ℤ → ℚ_[2])) (blockSymbol D) := by
  refine ⟨D, hv, he, rfl, ?_, rfl⟩
  rw [intMat_map D he]
  have : (dyMat D).submatrix (Fin.cast rfl) (Fin.cast rfl) = dyMat D := by ext; simp
  rw [this]
  exact ZpEquiv.refl _

/-! ### Determinant -/

theorem det_orthSumMat {a b : ℕ} (F : Matrix (Fin a) (Fin a) ℤ) (G : Matrix (Fin b) (Fin b) ℤ) :
    (orthSumMat F G).det = F.det * G.det := by
  rw [dyadic_orthSumMat_eq, det_submatrix_equiv_self, det_fromBlocks_zero₂₁]

/-- The 2-adic valuation of a block: $e\dim b$. -/
def bVal (b : DyBlock) : ℕ := (blockExp b).toNat * b.dim

theorem det_bInt (b : DyBlock) (hv : b.Valid) : ∃ u : ℤ, ¬ 2 ∣ u ∧ (bInt b).det = 2 ^ bVal b * u := by
  cases b with
  | sq e u =>
    refine ⟨u, ?_, ?_⟩
    · simp only [DyBlock.Valid] at hv; rcases hv with rfl | rfl | rfl | rfl <;> decide
    · show (!![2 ^ e.toNat * u] : Matrix (Fin 1) (Fin 1) ℤ).det = 2 ^ (e.toNat * 1) * u
      simp
  | hyp e =>
    refine ⟨-1, by decide, ?_⟩
    show ((2 ^ e.toNat : ℤ) • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ)).det = 2 ^ (e.toNat * 2) * (-1)
    rw [det_smul, det_fin_two_of]; simp [pow_mul]
  | ell e =>
    refine ⟨3, by decide, ?_⟩
    show ((2 ^ e.toNat : ℤ) • (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ)).det = 2 ^ (e.toNat * 2) * 3
    rw [det_smul, det_fin_two_of]; simp [pow_mul]; try ring

theorem det_intMat : ∀ (D : List DyBlock), (∀ b ∈ D, b.Valid) →
    ∃ u : ℤ, ¬ 2 ∣ u ∧ (intMat D).det = 2 ^ (D.map bVal).sum * u
  | [], _ => ⟨1, by decide, by show Matrix.det (0 : Matrix (Fin 0) (Fin 0) ℤ) = 2 ^ 0 * 1; simp⟩
  | b :: D, hv => by
    obtain ⟨u, hu, hb⟩ := det_bInt b (hv b (by simp))
    obtain ⟨w, hw, hD⟩ := det_intMat D fun c hc => hv c (by simp [hc])
    refine ⟨u * w, ?_, ?_⟩
    · intro h
      rcases (Int.prime_two.dvd_mul).mp h with h | h
      · exact hu h
      · exact hw h
    · have e1 := det_orthSumMat (bInt b) (intMat D)
      rw [hb, hD] at e1
      rw [List.map_cons, List.sum_cons, pow_add]
      refine e1.trans ?_
      ring

theorem det_intMat_ne (D : List DyBlock) (hv : ∀ b ∈ D, b.Valid) : (intMat D).det ≠ 0 := by
  obtain ⟨u, hu, h⟩ := det_intMat D hv
  rw [h]
  exact mul_ne_zero (pow_ne_zero _ two_ne_zero) fun h0 => hu (h0 ▸ dvd_zero 2)

theorem padicValInt_det_intMat (D : List DyBlock) (hv : ∀ b ∈ D, b.Valid) :
    padicValInt 2 (intMat D).det = (D.map bVal).sum := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu, h⟩ := det_intMat D hv
  have hu0 : u ≠ 0 := fun h0 => hu (h0 ▸ dvd_zero 2)
  rw [h, padicValInt.mul (pow_ne_zero _ two_ne_zero) hu0, padicValInt.eq_zero_of_not_dvd hu]
  simp [padicValInt]

theorem dyDim_eq_sum (D : List DyBlock) : dyDim D = (D.map DyBlock.dim).sum := by
  induction D with
  | nil => rfl
  | cons b D ih => simp [dyDim, ih]

/-- Sums over the levels of the symbol are sums over the blocks. -/
theorem sum_levels (f : ℕ → ℕ) (N : ℕ) : ∀ (D : List DyBlock), (∀ b ∈ D, 0 ≤ blockExp b ∧ blockExp b < N) →
    ∑ k ∈ Finset.range N, f k * (blockSymbol D k).dim = (D.map fun b => f (blockExp b).toNat * b.dim).sum
  | [], _ => by simp [blockSymbol]
  | b :: D, h => by
    have ih := sum_levels f N D fun c hc => h c (by simp [hc])
    obtain ⟨h0, h1⟩ := h b (by simp)
    have hdim : ∀ k : ℕ, (blockSymbol (b :: D) k).dim =
        (if blockExp b = k then b.dim else 0) + (blockSymbol D k).dim := by
      intro k
      unfold blockSymbol
      simp only [List.filter_cons]
      split_ifs with hb <;> simp_all
    simp only [hdim, mul_add, Finset.sum_add_distrib, ih, List.map_cons, List.sum_cons]
    congr 1
    rw [Finset.sum_eq_single (blockExp b).toNat]
    · rw [if_pos (by omega)]
    · intro k _ hk
      rw [if_neg (by omega), mul_zero]
    · intro hk
      exact absurd (Finset.mem_range.mpr (by omega)) hk

/-! ### Parity of the diagonal -/

theorem evenDiag_orthSum {a b : ℕ} {F : Matrix (Fin a) (Fin a) ℤ} {G : Matrix (Fin b) (Fin b) ℤ} (hF : EvenDiag F)
    (hG : EvenDiag G) : EvenDiag (orthSumMat F G) := by
  intro i
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
  rw [orthSumMat_apply]
  rcases x with x | x
  · exact hF x
  · exact hG x

/-- A block has even diagonal unless it is $2^0ux^2$. -/
theorem evenDiag_bInt (b : DyBlock) (h : ¬ (IsSqBlock b ∧ blockExp b = 0)) (he : 0 ≤ blockExp b) :
    EvenDiag (bInt b) := by
  cases b with
  | sq e u =>
    simp only [IsSqBlock, blockExp, true_and] at h he
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, e = k + 1 := ⟨(e - 1).toNat, by omega⟩
    intro i; fin_cases i
    show (2 : ℤ) ∣ (!![2 ^ ((k : ℤ) + 1).toNat * u] : Matrix (Fin 1) (Fin 1) ℤ) 0 0
    rw [show ((k : ℤ) + 1).toNat = k + 1 by omega]
    simp only [pow_succ, mul_assoc]
    exact Dvd.dvd.mul_left (dvd_mul_right 2 u) _
  | hyp e =>
    show ∀ i : Fin 2, (2 : ℤ) ∣ ((2 ^ e.toNat : ℤ) • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ)) i i
    intro i
    have : ∀ i : Fin 2, (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) i i = 0 := by decide
    rw [Matrix.smul_apply, this]; simp
  | ell e =>
    show ∀ i : Fin 2, (2 : ℤ) ∣ ((2 ^ e.toNat : ℤ) • (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ)) i i
    intro i
    have : ∀ i : Fin 2, (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ) i i = 2 := by decide
    rw [Matrix.smul_apply, this, smul_eq_mul]; exact dvd_mul_left 2 _

theorem evenDiag_intMat : ∀ (D : List DyBlock), (∀ b ∈ D, 0 ≤ blockExp b) →
    (∀ b ∈ D, ¬ (IsSqBlock b ∧ blockExp b = 0)) → EvenDiag (intMat D)
  | [], _, _ => fun i => i.elim0
  | b :: D, he, h => evenDiag_orthSum (evenDiag_bInt b (h b (by simp)) (he b (by simp)))
      (evenDiag_intMat D (fun c hc => he c (by simp [hc])) fun c hc => h c (by simp [hc]))

/-- If the constituent of scale $1$ of `blockSymbol D` has type II, `intMat D` has even diagonal. -/
theorem evenDiag_intMat_of_typeII (D : List DyBlock) (he : ∀ b ∈ D, 0 ≤ blockExp b)
    (h : (blockSymbol D 0).type = .II) : EvenDiag (intMat D) := by
  refine evenDiag_intMat D he fun b hb ⟨hsq, h0⟩ => ?_
  unfold blockSymbol at h
  simp only at h
  have : (D.filter fun b => blockExp b = ((0 : ℕ) : ℤ)).any (fun b => decide (IsSqBlock b)) = true := by
    rw [List.any_eq_true]
    exact ⟨b, List.mem_filter.mpr ⟨hb, by simpa using h0⟩, by simpa using hsq⟩
  rw [this] at h
  exact absurd h (by decide)

end QuadFormsKB.ConwaySloane.Mass.Two
