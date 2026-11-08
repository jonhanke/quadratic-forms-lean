/-
# O'Meara §106F, toward 106.r38: the mass of the genus of $I_n$, $9 \le n \le 13$

The Conway–Sloane mass formula (`ConwaySloane.Mass.mass_eq_stdMass_mul_symbols_unconditional`) for the form $I_n$
(Gram matrix $1$, determinant $1$): its $2$-adic symbol is $1^{+n}_n$ (a single type I constituent of dimension $n$,
sign $+$, oddity $n$), certified by `ConwaySloane.Mass.isTwoSymbolOf_intMat` with $n$ blocks $x^2$; no odd prime divides
the determinant. With the standard masses (Table 3) and $\zeta_{-1}(5)/\pi^5 = 5/1536$, $\zeta(6)/\pi^6 = 1/960$
(Table 6) this gives
$$m(I_9) = \tfrac{17}{2786918400},\quad m(I_{10}) = \tfrac{1}{2229534720},\quad m(I_{11}) = \tfrac{31}{735746457600},$$
$$m(I_{12}) = \tfrac{31}{5885971660800},\quad m(I_{13}) = \tfrac{691}{765176315904000}$$
(`mass_sumSq_nine`, …, `mass_sumSq_thirteen`). Indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicFinal
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicSymbol
import QuadFormsKB.Literature.ConwaySloane.Mass.Table6
import QuadFormsKB.Literature.OMeara.Sec106Rank13Forms

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

open Siegel LocalDensity ConwaySloane ConwaySloane.Mass ConwaySloane.Mass.Two Cassels

/-- The blocks of the $2$-adic Jordan decomposition of $I_n$: $n$ blocks $x^2$. -/
def blocksI (n : ℕ) : List DyBlock := List.replicate n (DyBlock.sq 0 1)

theorem orthSumMat_one_one {a b : ℕ} :
    orthSumMat (1 : Matrix (Fin a) (Fin a) ℤ) (1 : Matrix (Fin b) (Fin b) ℤ) = 1 := by
  unfold orthSumMat
  rw [Matrix.fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

theorem intMat_blocksI (k : ℕ) : intMat (blocksI k) = 1 := by
  induction k with
  | zero => ext i; exact i.elim0
  | succ k ih =>
    unfold blocksI at ih ⊢
    rw [List.replicate_succ]
    show orthSumMat (bInt (DyBlock.sq 0 1)) (intMat _) = 1
    have hb : bInt (DyBlock.sq 0 1) = 1 := by
      ext i j; fin_cases i; fin_cases j; simp [bInt]; rfl
    rw [hb, ih, orthSumMat_one_one]

/-- **The $2$-adic symbol of $I_n$** is `blockSymbol (blocksI n)`. -/
theorem isTwoSymbolOf_one (n : ℕ) :
    IsTwoSymbolOf ((intMat (blocksI n)).map (Int.cast : ℤ → ℚ_[2])) (blockSymbol (blocksI n)) :=
  isTwoSymbolOf_intMat _ (fun b hb => by simp [blocksI, List.mem_replicate] at hb; rw [hb.2]; simp [DyBlock.Valid])
    (fun b hb => by simp [blocksI, List.mem_replicate] at hb; rw [hb.2]; simp [blockExp])


/-- The symbol of $I_n$ has only the constituent at scale $1$. -/
theorem blockSymbol_blocksI_pos (n : ℕ) {k : ℕ} (hk : k ≠ 0) :
    blockSymbol (blocksI n) k = TwoFactor.trivial := by
  unfold blockSymbol
  have : (blocksI n).filter (fun b => blockExp b = (k : ℤ)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro b hb
    simp [blocksI, List.mem_replicate] at hb
    rw [hb.2]; simp [blockExp, eq_comm, hk]
  simp only [this]
  rfl

theorem supported_blocksI (n : ℕ) : (blockSymbol (blocksI n)).SupportedBelow 1 :=
  fun k hk => blockSymbol_blocksI_pos n (by omega)

/-- The symbol $1^{+n}_n$ as an explicit function. -/
def symI (n : ℕ) : TwoSymbol := fun k => if k = 0 then ⟨n, .plus, .I, (n : ZMod 8)⟩ else TwoFactor.trivial

theorem posDef_ofMatrixZ_one (n : ℕ) : IntQF.PosDef (ofMatrixZ (1 : Matrix (Fin n) (Fin n) ℤ)) := by
  rw [← sumSq_eq_ofMatrixZ_one]; exact posDef_sumSq

/-- The mass formula for $I_n$ in the working form, given the symbol. -/
theorem mass_sumSq_of_symbol {n : ℕ} (hn : 3 ≤ n)
    (hτ : IsTwoSymbolOf ((1 : Matrix (Fin n) (Fin n) ℤ).map (Int.cast : ℤ → ℚ_[2])) (symI n)) :
    Siegel.mass (sumSq n) = stdMass n 1 * (pMassTwo (symI n) 1 / (stdP 2 n 1 : ℝ)) := by
  have hsupp : (symI n).SupportedBelow 1 := fun k hk => by simp [symI, show k ≠ 0 by omega]
  rw [sumSq_eq_ofMatrixZ_one, mass_eq_stdMass_mul_symbols_unconditional hn (by simp [Matrix.IsSymm])
    (posDef_ofMatrixZ_one n) (symI n) 1 hτ hsupp (fun _ _ => OddFactor.trivial) (fun _ => 0) ?_]
  · rw [Matrix.det_one]
    have hpf : (2 * (1 : ℤ)).natAbs.primeFactors = {2} := by
      rw [show (2 * (1 : ℤ)).natAbs = 2 by norm_num, Nat.Prime.primeFactors Nat.prime_two]
    rw [hpf, Finset.prod_singleton, if_pos rfl]
  · intro p hp hp2 hdvd
    rw [Matrix.det_one] at hdvd
    exact absurd (Int.eq_one_of_dvd_one (by positivity) hdvd) (by exact_mod_cast hp.one_lt.ne')

theorem symbol_nine : blockSymbol (blocksI 9) = symI 9 := by
  funext k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · decide +kernel
  · rw [blockSymbol_blocksI_pos 9 (by omega)]; simp [symI, show k ≠ 0 by omega]

theorem isTwoSymbolOf_nine :
    IsTwoSymbolOf ((1 : Matrix (Fin 9) (Fin 9) ℤ).map (Int.cast : ℤ → ℚ_[2])) (symI 9) := by
  have := isTwoSymbolOf_one 9
  rw [intMat_blocksI, symbol_nine] at this
  exact this

theorem pMassTwo_ratio_nine : pMassTwo (symI 9) 1 / (stdP 2 9 1 : ℝ) = 17/64 := by
  have hd : diagProdTwo (symI 9) 1 = 8192/42525 := by
    simp (config := { decide := true }) [diagProdTwo, halfFactor, symI, Finset.prod_range_succ, twoSpecies,
      IsBound, octane, TwoFactor.trivial, Species.diagFactor, lowerProd, Sign.toInt]
    norm_num
  have hs : stdP 2 9 1 = 524288/722925 := by
    simp [stdP, lowerProd, Finset.prod_range_succ]; norm_num
  have hc : crossExp (fun k => (symI 9 k).dim) 1 = 0 := by decide
  have hII : nII (symI 9) 1 = 0 := by decide
  have hII' : nII' (symI 9) 1 = 0 := by decide
  rw [pMassTwo, hd, hc, hII, hII', hs]; norm_num

/-- **The mass of the genus of $I_{9}$** is $17/2786918400$ (Conway–Sloane mass formula). -/
@[kb "conwaysloane1988" "(2), (3), p. 263; §7, p. 266 (the genus of I_n)"]
theorem mass_sumSq_nine : Siegel.mass (sumSq 9) = 17/2786918400 := by
  rw [mass_sumSq_of_symbol (by norm_num) isTwoSymbolOf_nine, pMassTwo_ratio_nine]
  rw [stdMass_table_9 1]
  norm_num

theorem symbol_ten : blockSymbol (blocksI 10) = symI 10 := by
  funext k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · decide +kernel
  · rw [blockSymbol_blocksI_pos 10 (by omega)]; simp [symI, show k ≠ 0 by omega]

theorem isTwoSymbolOf_ten :
    IsTwoSymbolOf ((1 : Matrix (Fin 10) (Fin 10) ℤ).map (Int.cast : ℤ → ℚ_[2])) (symI 10) := by
  have := isTwoSymbolOf_one 10
  rw [intMat_blocksI, symbol_ten] at this
  exact this

theorem pMassTwo_ratio_ten : pMassTwo (symI 10) 1 / (stdP 2 10 1 : ℝ) = 1/4 := by
  have hd : diagProdTwo (symI 10) 1 = 131072/722925 := by
    simp (config := { decide := true }) [diagProdTwo, halfFactor, symI, Finset.prod_range_succ, twoSpecies,
      IsBound, octane, TwoFactor.trivial, Species.diagFactor, lowerProd, Sign.toInt]
    norm_num
  have hs : stdP 2 10 1 = 524288/722925 := by
    simp [stdP, lowerProd, Finset.prod_range_succ]; norm_num
  have hc : crossExp (fun k => (symI 10 k).dim) 1 = 0 := by decide
  have hII : nII (symI 10) 1 = 0 := by decide
  have hII' : nII' (symI 10) 1 = 0 := by decide
  rw [pMassTwo, hd, hc, hII, hII', hs]; norm_num

/-- **The mass of the genus of $I_{10}$** is $1/2229534720$ (Conway–Sloane mass formula). -/
@[kb "conwaysloane1988" "(2), (3), p. 263; §7, p. 266 (the genus of I_n)"]
theorem mass_sumSq_ten : Siegel.mass (sumSq 10) = 1/2229534720 := by
  rw [mass_sumSq_of_symbol (by norm_num) isTwoSymbolOf_ten, pMassTwo_ratio_ten]
  rw [stdMass_table_10 1, show ((-1 : ℤ) ^ 5 * 1) = -1 by norm_num, mul_div_assoc, table6_1_5]
  norm_num

theorem symbol_eleven : blockSymbol (blocksI 11) = symI 11 := by
  funext k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · decide +kernel
  · rw [blockSymbol_blocksI_pos 11 (by omega)]; simp [symI, show k ≠ 0 by omega]

theorem isTwoSymbolOf_eleven :
    IsTwoSymbolOf ((1 : Matrix (Fin 11) (Fin 11) ℤ).map (Int.cast : ℤ → ℚ_[2])) (symI 11) := by
  have := isTwoSymbolOf_one 11
  rw [intMat_blocksI, symbol_eleven] at this
  exact this

theorem pMassTwo_ratio_eleven : pMassTwo (symI 11) 1 / (stdP 2 11 1 : ℝ) = 31/128 := by
  have hd : diagProdTwo (symI 11) 1 = 4194304/23856525 := by
    simp (config := { decide := true }) [diagProdTwo, halfFactor, symI, Finset.prod_range_succ, twoSpecies,
      IsBound, octane, TwoFactor.trivial, Species.diagFactor, lowerProd, Sign.toInt]
    norm_num
  have hs : stdP 2 11 1 = 536870912/739552275 := by
    simp [stdP, lowerProd, Finset.prod_range_succ]; norm_num
  have hc : crossExp (fun k => (symI 11 k).dim) 1 = 0 := by decide
  have hII : nII (symI 11) 1 = 0 := by decide
  have hII' : nII' (symI 11) 1 = 0 := by decide
  rw [pMassTwo, hd, hc, hII, hII', hs]; norm_num

/-- **The mass of the genus of $I_{11}$** is $31/735746457600$ (Conway–Sloane mass formula). -/
@[kb "conwaysloane1988" "(2), (3), p. 263; §7, p. 266 (the genus of I_n)"]
theorem mass_sumSq_eleven : Siegel.mass (sumSq 11) = 31/735746457600 := by
  rw [mass_sumSq_of_symbol (by norm_num) isTwoSymbolOf_eleven, pMassTwo_ratio_eleven]
  rw [stdMass_table_11 1]
  norm_num

theorem symbol_twelve : blockSymbol (blocksI 12) = symI 12 := by
  funext k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · decide +kernel
  · rw [blockSymbol_blocksI_pos 12 (by omega)]; simp [symI, show k ≠ 0 by omega]

theorem isTwoSymbolOf_twelve :
    IsTwoSymbolOf ((1 : Matrix (Fin 12) (Fin 12) ℤ).map (Int.cast : ℤ → ℚ_[2])) (symI 12) := by
  have := isTwoSymbolOf_one 12
  rw [intMat_blocksI, symbol_twelve] at this
  exact this

theorem pMassTwo_ratio_twelve : pMassTwo (symI 12) 1 / (stdP 2 12 1 : ℝ) = 31/128 := by
  have hd : diagProdTwo (symI 12) 1 = 4194304/23856525 := by
    simp (config := { decide := true }) [diagProdTwo, halfFactor, symI, Finset.prod_range_succ, twoSpecies,
      IsBound, octane, TwoFactor.trivial, Species.diagFactor, lowerProd, Sign.toInt]
    norm_num
  have hs : stdP 2 12 1 = 536870912/739552275 := by
    simp [stdP, lowerProd, Finset.prod_range_succ]; norm_num
  have hc : crossExp (fun k => (symI 12 k).dim) 1 = 0 := by decide
  have hII : nII (symI 12) 1 = 0 := by decide
  have hII' : nII' (symI 12) 1 = 0 := by decide
  rw [pMassTwo, hd, hc, hII, hII', hs]; norm_num

/-- **The mass of the genus of $I_{12}$** is $31/5885971660800$ (Conway–Sloane mass formula). -/
@[kb "conwaysloane1988" "(2), (3), p. 263; §7, p. 266 (the genus of I_n)"]
theorem mass_sumSq_twelve : Siegel.mass (sumSq 12) = 31/5885971660800 := by
  rw [mass_sumSq_of_symbol (by norm_num) isTwoSymbolOf_twelve, pMassTwo_ratio_twelve]
  rw [stdMass_table_12 1, show ((-1 : ℤ) ^ 6 * 1) = 1 by norm_num, mul_div_assoc, table6_1_6]
  norm_num

theorem symbol_thirteen : blockSymbol (blocksI 13) = symI 13 := by
  funext k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · decide +kernel
  · rw [blockSymbol_blocksI_pos 13 (by omega)]; simp [symI, show k ≠ 0 by omega]

theorem isTwoSymbolOf_thirteen :
    IsTwoSymbolOf ((1 : Matrix (Fin 13) (Fin 13) ℤ).map (Int.cast : ℤ → ℚ_[2])) (symI 13) := by
  have := isTwoSymbolOf_one 13
  rw [intMat_blocksI, symbol_thirteen] at this
  exact this

theorem pMassTwo_ratio_thirteen : pMassTwo (symI 13) 1 / (stdP 2 13 1 : ℝ) = 63/256 := by
  have hd : diagProdTwo (symI 13) 1 = 8589934592/48070897875 := by
    simp (config := { decide := true }) [diagProdTwo, halfFactor, symI, Finset.prod_range_succ, twoSpecies,
      IsBound, octane, TwoFactor.trivial, Species.diagFactor, lowerProd, Sign.toInt]
    norm_num
  have hs : stdP 2 13 1 = 2199023255552/3028466566125 := by
    simp [stdP, lowerProd, Finset.prod_range_succ]; norm_num
  have hc : crossExp (fun k => (symI 13 k).dim) 1 = 0 := by decide
  have hII : nII (symI 13) 1 = 0 := by decide
  have hII' : nII' (symI 13) 1 = 0 := by decide
  rw [pMassTwo, hd, hc, hII, hII', hs]; norm_num

/-- **The mass of the genus of $I_{13}$** is $691/765176315904000$ (Conway–Sloane mass formula). -/
@[kb "conwaysloane1988" "(2), (3), p. 263; §7, p. 266 (the genus of I_n)"]
theorem mass_sumSq_thirteen : Siegel.mass (sumSq 13) = 691/765176315904000 := by
  rw [mass_sumSq_of_symbol (by norm_num) isTwoSymbolOf_thirteen, pMassTwo_ratio_thirteen]
  rw [stdMass_table_13 1]
  norm_num

end QuadFormsKB.Lattices
