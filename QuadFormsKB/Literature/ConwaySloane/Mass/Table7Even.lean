/-
# Conway–Sloane 1988, §10, Table 7: the totals for even $n$

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §10, Table 7, p. 275.

Table 7 lists, for $n \le 7$, the total mass of the genus $\mathrm I_n(11^+)$ of $f = \mathrm{diag}(11) \oplus I_{n-1}$
predicted by (2) (`vine11Total`, `Table7.lean`, which proves the odd $n$). For even $n = 2s$ the standard mass
$\mathrm{std}(f) = c_n\,\zeta_D(s)/\pi^s$ (Table 3) contains $\zeta_D(s)$ with $D = (-1)^s\,11$. The three values needed are
proved, not assumed: $\zeta_{-11}(1) = 3\pi/(2\sqrt{11})$ (`zetaD_neg_eleven_one`, class number formula with
$h(\mathbb Q(\sqrt{-11})) = 1$, `Table6One.lean`) and the Table 6 entries $\zeta_{11}(2)\,11\sqrt{11}/\pi^2 = \frac72$,
$\zeta_{-11}(3)\,11^2\sqrt{11}/\pi^3 = \frac{27}2$ (`table6_11_2`, `table6_11_3`, `Table6RowsA.lean`). (The input
`Table6Eleven` mentioned in `Table7.lean` is therefore not needed.)

**Proves**
* `vine11_values_2`, `vine11_values_4`, `vine11_values_6`: the 2-adic and 11-adic masses and standard masses of
  $\mathrm I_n(11^+)$ for $n = 2, 4, 6$.
* `table7_total_two`, `table7_total_four`, `table7_total_six`: the predicted masses $\frac34$, $\frac7{96}$,
  $\frac9{2560}$, as printed, together with the sums of the printed contributions.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.Table6One
import QuadFormsKB.Literature.ConwaySloane.Mass.Table7

namespace QuadFormsKB.ConwaySloane.Mass

open Complex Finset QuadFormsKB.Binary
open scoped Real

/-! ### Table 7, even $n$ -/

theorem vine11_values_2 :
    pMassTwo (vine11Two 2) 1 = 1 / 4 ∧ stdP 2 2 11 = 1 / 2 ∧
      pMassOdd 11 (vine11Eleven 2) 2 = (1 / 4 : ℚ) * Real.sqrt 11 ∧ stdP 11 2 11 = 1 / 2 := by
  have hd : diagProdTwo (vine11Two 2) 1 = 1 / 4 := by
    simp (config := { decide := true }) [diagProdTwo, halfFactor, vine11Two, Finset.prod_range_succ, twoSpecies,
      IsBound, octane, TwoFactor.trivial, Species.diagFactor, lowerProd, Sign.toInt]
    norm_num
  have hc : crossExp (fun k => (vine11Two 2 k).dim) 1 = 0 := by decide
  have hII : nII (vine11Two 2) 1 = 0 := by decide
  have hII' : nII' (vine11Two 2) 1 = 0 := by decide
  have hd11 : (∏ k ∈ range 2, (oddSpecies 11 (vine11Eleven 2 k)).diagFactor 11) = (1 / 4 : ℚ) := by
    simp (config := { decide := true }) [vine11Eleven, Finset.prod_range_succ, oddSpecies,
      Species.diagFactor, lowerProd, OddFactor.trivial, Sign.flip, Sign.toInt]
    all_goals norm_num
  have hc11 : crossExp (fun k => (vine11Eleven 2 k).dim) 2 = 1 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pMassTwo, hd, hc, hII, hII']; norm_num
  · norm_num [stdP, lowerProd, Finset.prod_range_succ]
  · rw [pMassOdd, hd11, hc11, pow_one]
    norm_num
  · norm_num [stdP, lowerProd, Finset.prod_range_succ]

theorem vine11_values_4 :
    pMassTwo (vine11Two 4) 1 = 1 / 6 ∧ stdP 2 4 11 = 2 / 3 ∧
      pMassOdd 11 (vine11Eleven 4) 2 = (121 / 480 : ℚ) * (11 * Real.sqrt 11) ∧ stdP 11 4 11 = 121 / 240 := by
  have hd : diagProdTwo (vine11Two 4) 1 = 1 / 6 := by
    simp (config := { decide := true }) [diagProdTwo, halfFactor, vine11Two, Finset.prod_range_succ, twoSpecies,
      IsBound, octane, TwoFactor.trivial, Species.diagFactor, lowerProd, Sign.toInt]
    norm_num
  have hc : crossExp (fun k => (vine11Two 4 k).dim) 1 = 0 := by decide
  have hII : nII (vine11Two 4) 1 = 0 := by decide
  have hII' : nII' (vine11Two 4) 1 = 0 := by decide
  have hd11 : (∏ k ∈ range 2, (oddSpecies 11 (vine11Eleven 4 k)).diagFactor 11) = (121 / 480 : ℚ) := by
    simp (config := { decide := true }) [vine11Eleven, Finset.prod_range_succ, oddSpecies,
      Species.diagFactor, lowerProd, OddFactor.trivial, Sign.flip, Sign.toInt]
    all_goals norm_num
  have hc11 : crossExp (fun k => (vine11Eleven 4 k).dim) 2 = 3 := by decide
  have hs : Real.sqrt ((11 : ℕ) : ℝ) ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pMassTwo, hd, hc, hII, hII']; norm_num
  · norm_num [stdP, lowerProd, Finset.prod_range_succ]
  · rw [pMassOdd, hd11, hc11, pow_succ, hs]
    norm_num
  · norm_num [stdP, lowerProd, Finset.prod_range_succ]

theorem vine11_values_6 :
    pMassTwo (vine11Two 6) 1 = 2 / 15 ∧ stdP 2 6 11 = 32 / 45 ∧
      pMassOdd 11 (vine11Eleven 6) 2 = (1771561 / 7027200 : ℚ) * (121 * Real.sqrt 11) ∧
      stdP 11 6 11 = 1771561 / 3513600 := by
  have hd : diagProdTwo (vine11Two 6) 1 = 2 / 15 := by
    simp (config := { decide := true }) [diagProdTwo, halfFactor, vine11Two, Finset.prod_range_succ, twoSpecies,
      IsBound, octane, TwoFactor.trivial, Species.diagFactor, lowerProd, Sign.toInt]
    norm_num
  have hc : crossExp (fun k => (vine11Two 6 k).dim) 1 = 0 := by decide
  have hII : nII (vine11Two 6) 1 = 0 := by decide
  have hII' : nII' (vine11Two 6) 1 = 0 := by decide
  have hd11 : (∏ k ∈ range 2, (oddSpecies 11 (vine11Eleven 6 k)).diagFactor 11) = (1771561 / 7027200 : ℚ) := by
    simp (config := { decide := true }) [vine11Eleven, Finset.prod_range_succ, oddSpecies,
      Species.diagFactor, lowerProd, OddFactor.trivial, Sign.flip, Sign.toInt]
    all_goals norm_num
  have hc11 : crossExp (fun k => (vine11Eleven 6 k).dim) 2 = 5 := by decide
  have hs : Real.sqrt ((11 : ℕ) : ℝ) ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pMassTwo, hd, hc, hII, hII']; norm_num
  · norm_num [stdP, lowerProd, Finset.prod_range_succ]
  · rw [pMassOdd, hd11, hc11, show 5 = 2 * 2 + 1 from rfl, pow_succ, pow_mul, hs]
    norm_num
  · norm_num [stdP, lowerProd, Finset.prod_range_succ]

/-- **Table 7, $n = 2$** (Conway–Sloane 1988, p. 275): the mass of $\mathrm I_2(11^+)$ predicted by (2) is $\frac34$
(with $\mathrm{std}(f) = 2\zeta_{-11}(1)/\pi$ and $\zeta_{-11}(1) = 3\pi/(2\sqrt{11})$, `zetaD_neg_eleven_one`), and the
printed contributions $\frac14 + \frac12$ add up to it. -/
@[kb "conwaysloane1988" "Table 7, p. 275 (n = 2)"]
theorem table7_total_two : vine11Total 2 = 3 / 4 ∧ (1 / 4 + 1 / 2 : ℝ) = 3 / 4 := by
  refine ⟨?_, by norm_num⟩
  unfold vine11Total
  obtain ⟨h2, s2, h11, s11⟩ := vine11_values_2
  rw [h2, s2, h11, s11, stdMass_table_2, show ((-1 : ℤ) ^ 1 * 11) = -11 by norm_num, zetaD_neg_eleven_one]
  have h11' : Real.sqrt 11 ≠ 0 := by positivity
  have hπ : π ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-- **Table 7, $n = 4$** (Conway–Sloane 1988, p. 275): predicted mass $\frac7{96} = \frac1{96} + \frac1{16}$ (with
$\mathrm{std}(f) = \zeta_{11}(2)/(6\pi^2)$ and the Table 6 entry $\zeta_{11}(2)\,11\sqrt{11}/\pi^2 = \frac72$). -/
@[kb "conwaysloane1988" "Table 7, p. 275 (n = 4)"]
theorem table7_total_four : vine11Total 4 = 7 / 96 ∧ (1 / 96 + 1 / 16 : ℝ) = 7 / 96 := by
  refine ⟨?_, by norm_num⟩
  unfold vine11Total
  obtain ⟨h2, s2, h11, s11⟩ := vine11_values_4
  have h11' : Real.sqrt 11 ≠ 0 := by positivity
  have hπ : π ^ 2 ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hz : zetaD 11 2 = 7 / 2 * π ^ 2 / (11 * Real.sqrt 11) := by
    have h := table6_11_2
    rw [eq_div_iff (by positivity)]
    field_simp at h
    linarith
  rw [h2, s2, h11, s11, stdMass_table_4, show ((-1 : ℤ) ^ 2 * 11) = 11 by norm_num, hz]
  push_cast
  field_simp
  ring

/-- **Table 7, $n = 6$** (Conway–Sloane 1988, p. 275): predicted mass $\frac9{2560} = \frac1{7680} + \frac1{768} +
\frac1{480}$ (with $\mathrm{std}(f) = \zeta_{-11}(3)/(360\pi^3)$ and the Table 6 entry
$\zeta_{-11}(3)\,11^2\sqrt{11}/\pi^3 = \frac{27}2$; the even genus $11_6$ does not contribute to the odd genus). -/
@[kb "conwaysloane1988" "Table 7, p. 275 (n = 6)"]
theorem table7_total_six : vine11Total 6 = 9 / 2560 ∧ (1 / 7680 + 1 / 768 + 1 / 480 : ℝ) = 9 / 2560 := by
  refine ⟨?_, by norm_num⟩
  unfold vine11Total
  obtain ⟨h2, s2, h11, s11⟩ := vine11_values_6
  have h11' : Real.sqrt 11 ≠ 0 := by positivity
  have hπ : π ^ 3 ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hz : zetaD (-11) 3 = 27 / 2 * π ^ 3 / (121 * Real.sqrt 11) := by
    have h := table6_11_3
    rw [eq_div_iff (by positivity)]
    field_simp at h
    linarith
  rw [h2, s2, h11, s11, stdMass_table_6, show ((-1 : ℤ) ^ 3 * 11) = -11 by norm_num, hz]
  push_cast
  field_simp
  ring

end QuadFormsKB.ConwaySloane.Mass
