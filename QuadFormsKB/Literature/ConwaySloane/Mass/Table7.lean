/-
# Conway–Sloane 1988, §10, Table 7: the masses of the determinant $11^+$ vine

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), §10, pp. 274–275, Table 7 (bibliography key `conwaysloane1988`).

Table 7 lists, for $n \le 7$, the total mass of the genus $\mathrm I_n(11^+)$ of $f = \mathrm{diag}(11) \oplus I_{n-1}$
as given by (2), and its decomposition into the contributions of the families $L_k \oplus I_{n-k}$.

* The symbols (p. 274): 2-adic, $f_1 = f$ of type I, dimension $n$, sign $\left(\frac{11}2\right) = -$, oddity
  $11 + (n-1) \equiv n + 2$, octane value $n - 2$ (`vine11Two`); 11-adic, $\dim f_1 = n - 1$, $\dim f_{11} = 1$, both
  determinants residues (`vine11Eleven`).
* The predicted total is $\mathrm{std}(f)\prod_{p \mid 2d}m_p(f)/\mathrm{std}_p(f)$, the working form of (2) used in
  §9 (`vine11Total`). For $n$ odd the standard mass is rational (Table 3) and the totals $\frac5{16}$,
  $\frac{61}{3840}$, $\frac{133}{165888}$ are proved (`table7_total_three`, `_five`, `_seven`). For $n = 1$ the initial
  $2$ of (2) is to be replaced by $1$ (§6, p. 266), and the total is $\frac12$ (`table7_total_one`). For $n$ even the
  standard mass contains $\zeta_{\mp11}(s)$; with the Table 6 values (proved in `Table6One.lean`, `Table6RowsA.lean`)
  the totals $\frac34$, $\frac7{96}$, $\frac9{2560}$ are proved in `Table7Even.lean`.
* The sums of the contributions (`table7_rows`) and the rule "the mass of $L_k \oplus I_r$ is that of
  $L_k \oplus I_{r-1}$ divided by $2r$" (`table7_division`) are arithmetic checks of the printed numbers.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.PMass
import QuadFormsKB.Literature.ConwaySloane.Mass.StandardMass

namespace QuadFormsKB.ConwaySloane.Mass

open Finset Real

/-- The 2-adic symbol of $\mathrm I_n(11^+)$: $1^{-n}_{n+2}$ (Conway–Sloane 1988, §10, p. 274). -/
def vine11Two (n : ℕ) : TwoSymbol := fun k => if k = 0 then ⟨n, .minus, .I, (n + 2 : ℕ)⟩ else TwoFactor.trivial

/-- The 11-adic symbol of $\mathrm I_n(11^+)$: $1^{+(n-1)}11^{+1}$ (Conway–Sloane 1988, §10, p. 274). -/
def vine11Eleven (n : ℕ) : OddSymbol := fun k =>
  if k = 0 then ⟨n - 1, .plus⟩ else if k = 1 then ⟨1, .plus⟩ else OddFactor.trivial

/-- The total mass of $\mathrm I_n(11^+)$ predicted by (2), in the working form of §9:
$\mathrm{std}(f)\cdot\frac{m_2(f)}{\mathrm{std}_2(f)}\cdot\frac{m_{11}(f)}{\mathrm{std}_{11}(f)}$. -/
noncomputable def vine11Total (n : ℕ) : ℝ :=
  stdMass n 11 * (pMassTwo (vine11Two n) 1 / stdP 2 n 11) * (pMassOdd 11 (vine11Eleven n) 2 / stdP 11 n 11)

theorem vine11_values_1 :
    pMassTwo (vine11Two 1) 1 = 1 / 4 ∧ stdP 2 1 11 = 1 / 2 ∧
      pMassOdd 11 (vine11Eleven 1) 2 = (1 / 2 : ℚ) * 1 ∧ stdP 11 1 11 = 1 / 2 := by
  have hd : diagProdTwo (vine11Two 1) 1 = 1 / 4 := by
    simp (config := { decide := true }) [diagProdTwo, halfFactor, vine11Two, Finset.prod_range_succ, twoSpecies,
      IsBound, octane, TwoFactor.trivial, Species.diagFactor, lowerProd, Sign.toInt]
    norm_num
  have hc : crossExp (fun k => (vine11Two 1 k).dim) 1 = 0 := by decide
  have hII : nII (vine11Two 1) 1 = 0 := by decide
  have hII' : nII' (vine11Two 1) 1 = 0 := by decide
  have hd11 : (∏ k ∈ range 2, (oddSpecies 11 (vine11Eleven 1 k)).diagFactor 11) =
      (1 / 2 : ℚ) := by
    simp (config := { decide := true }) [vine11Eleven, Finset.prod_range_succ, oddSpecies,
      Species.diagFactor, lowerProd, OddFactor.trivial, Sign.flip, Sign.toInt]
    all_goals norm_num
  have hc11 : crossExp (fun k => (vine11Eleven 1 k).dim) 2 = 0 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pMassTwo, hd, hc, hII, hII']; norm_num
  · norm_num [stdP, lowerProd, Finset.prod_range_succ]
  · rw [pMassOdd, hd11, hc11]
    norm_num
  · norm_num [stdP, lowerProd, Finset.prod_range_succ]

theorem vine11_values_3 :
    pMassTwo (vine11Two 3) 1 = 1 / 4 ∧ stdP 2 3 11 = 2 / 3 ∧
      pMassOdd 11 (vine11Eleven 3) 2 = (11 / 48 : ℚ) * 11 ∧ stdP 11 3 11 = 121 / 240 := by
  have hd : diagProdTwo (vine11Two 3) 1 = 1 / 4 := by
    simp (config := { decide := true }) [diagProdTwo, halfFactor, vine11Two, Finset.prod_range_succ, twoSpecies,
      IsBound, octane, TwoFactor.trivial, Species.diagFactor, lowerProd, Sign.toInt]
    norm_num
  have hc : crossExp (fun k => (vine11Two 3 k).dim) 1 = 0 := by decide
  have hII : nII (vine11Two 3) 1 = 0 := by decide
  have hII' : nII' (vine11Two 3) 1 = 0 := by decide
  have hd11 : (∏ k ∈ range 2, (oddSpecies 11 (vine11Eleven 3 k)).diagFactor 11) = (11 / 48 : ℚ) := by
    simp (config := { decide := true }) [vine11Eleven, Finset.prod_range_succ, oddSpecies,
      Species.diagFactor, lowerProd, OddFactor.trivial, Sign.flip, Sign.toInt]
    all_goals norm_num
  have hc11 : crossExp (fun k => (vine11Eleven 3 k).dim) 2 = 2 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pMassTwo, hd, hc, hII, hII']; norm_num
  · norm_num [stdP, lowerProd, Finset.prod_range_succ]
  · rw [pMassOdd, hd11, hc11]
    rw [show 2 = 2 * 1 by rfl, pow_mul, Real.sq_sqrt (by norm_num)]; norm_num
  · norm_num [stdP, lowerProd, Finset.prod_range_succ]

theorem vine11_values_5 :
    pMassTwo (vine11Two 5) 1 = 2 / 15 ∧ stdP 2 5 11 = 32 / 45 ∧
      pMassOdd 11 (vine11Eleven 5) 2 = (14641 / 57600 : ℚ) * 121 ∧ stdP 11 5 11 = 1771561 / 3513600 := by
  have hd : diagProdTwo (vine11Two 5) 1 = 2 / 15 := by
    simp (config := { decide := true }) [diagProdTwo, halfFactor, vine11Two, Finset.prod_range_succ, twoSpecies,
      IsBound, octane, TwoFactor.trivial, Species.diagFactor, lowerProd, Sign.toInt]
    norm_num
  have hc : crossExp (fun k => (vine11Two 5 k).dim) 1 = 0 := by decide
  have hII : nII (vine11Two 5) 1 = 0 := by decide
  have hII' : nII' (vine11Two 5) 1 = 0 := by decide
  have hd11 : (∏ k ∈ range 2, (oddSpecies 11 (vine11Eleven 5 k)).diagFactor 11) =
      (14641 / 57600 : ℚ) := by
    simp (config := { decide := true }) [vine11Eleven, Finset.prod_range_succ, oddSpecies,
      Species.diagFactor, lowerProd, OddFactor.trivial, Sign.flip, Sign.toInt]
    all_goals norm_num
  have hc11 : crossExp (fun k => (vine11Eleven 5 k).dim) 2 = 4 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pMassTwo, hd, hc, hII, hII']; norm_num
  · norm_num [stdP, lowerProd, Finset.prod_range_succ]
  · rw [pMassOdd, hd11, hc11]
    rw [show 4 = 2 * 2 by rfl, pow_mul, Real.sq_sqrt (by norm_num)]; norm_num
  · norm_num [stdP, lowerProd, Finset.prod_range_succ]

theorem vine11_values_7 :
    pMassTwo (vine11Two 7) 1 = 64 / 405 ∧ stdP 2 7 11 = 2048 / 2835 ∧
      pMassOdd 11 (vine11Eleven 7) 2 = (2357947691 / 9360230400 : ℚ) * 1331 ∧ stdP 11 7 11 = 3138428376721 / 6224553216000 := by
  have hd : diagProdTwo (vine11Two 7) 1 = 64 / 405 := by
    simp (config := { decide := true }) [diagProdTwo, halfFactor, vine11Two, Finset.prod_range_succ, twoSpecies,
      IsBound, octane, TwoFactor.trivial, Species.diagFactor, lowerProd, Sign.toInt]
    norm_num
  have hc : crossExp (fun k => (vine11Two 7 k).dim) 1 = 0 := by decide
  have hII : nII (vine11Two 7) 1 = 0 := by decide
  have hII' : nII' (vine11Two 7) 1 = 0 := by decide
  have hd11 : (∏ k ∈ range 2, (oddSpecies 11 (vine11Eleven 7 k)).diagFactor 11) =
      (2357947691 / 9360230400 : ℚ) := by
    simp (config := { decide := true }) [vine11Eleven, Finset.prod_range_succ, oddSpecies,
      Species.diagFactor, lowerProd, OddFactor.trivial, Sign.flip, Sign.toInt]
    all_goals norm_num
  have hc11 : crossExp (fun k => (vine11Eleven 7 k).dim) 2 = 6 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pMassTwo, hd, hc, hII, hII']; norm_num
  · norm_num [stdP, lowerProd, Finset.prod_range_succ]
  · rw [pMassOdd, hd11, hc11]
    rw [show 6 = 2 * 3 by rfl, pow_mul, Real.sq_sqrt (by norm_num)]; norm_num
  · norm_num [stdP, lowerProd, Finset.prod_range_succ]

/-- **Table 7, $n = 3$** (Conway–Sloane 1988, p. 275): the mass of $\mathrm I_3(11^+)$ predicted by (2) is $\frac5{16}$,
and the contributions $\frac1{16} + \frac14$ of $11_1 \oplus I_2$ and $11^+_2 \oplus I_1$ add up to it. -/
@[kb "conwaysloane1988" "Table 7, p. 275 (n = 3)"]
theorem table7_total_three : vine11Total 3 = 5 / 16 ∧ (1 / 16 + 1 / 4 : ℝ) = 5 / 16 := by
  refine ⟨?_, by norm_num⟩
  unfold vine11Total
  obtain ⟨h2, s2, h11, s11⟩ := vine11_values_3
  rw [h2, s2, h11, s11, stdMass_table_3]
  norm_num

/-- **Table 7, $n = 5$** (Conway–Sloane 1988, p. 275): predicted mass $\frac{61}{3840} = \frac1{768} + \frac1{96} +
\frac1{240}$. -/
@[kb "conwaysloane1988" "Table 7, p. 275 (n = 5)"]
theorem table7_total_five : vine11Total 5 = 61 / 3840 ∧ (1 / 768 + 1 / 96 + 1 / 240 : ℝ) = 61 / 3840 := by
  refine ⟨?_, by norm_num⟩
  unfold vine11Total
  obtain ⟨h2, s2, h11, s11⟩ := vine11_values_5
  rw [h2, s2, h11, s11, stdMass_table_5]
  norm_num

/-- **Table 7, $n = 7$** (Conway–Sloane 1988, p. 275): predicted mass $\frac{133}{165888} = \frac1{92160} +
\frac1{7680} + \frac1{1920} + \frac1{7680} + \frac1{103680}$. -/
@[kb "conwaysloane1988" "Table 7, p. 275 (n = 7)"]
theorem table7_total_seven : vine11Total 7 = 133 / 165888 ∧
    (1 / 92160 + 1 / 7680 + 1 / 1920 + 1 / 7680 + 1 / 103680 : ℝ) = 133 / 165888 := by
  refine ⟨?_, by norm_num⟩
  unfold vine11Total
  obtain ⟨h2, s2, h11, s11⟩ := vine11_values_7
  rw [h2, s2, h11, s11, stdMass_table_7]
  norm_num

/-- **Table 7, $n = 1$, and §6** (Conway–Sloane 1988, p. 275 and p. 266): in dimension 1 the initial factor $2$ of (2)
is to be replaced by $1$, so the mass of the genus of $\langle 11\rangle$ is half the value of the working form of
(2): $\frac12\cdot\mathrm{std}(f)\frac{m_2}{\mathrm{std}_2}\frac{m_{11}}{\mathrm{std}_{11}} = \frac12$, as printed (and as
it must be: $\lvert\mathrm{Aut}\rangle 11\langle\rvert = 2$). -/
@[kb "conwaysloane1988" "Table 7, p. 275 (n = 1); §6, p. 266"]
theorem table7_total_one : vine11Total 1 / 2 = 1 / 2 := by
  unfold vine11Total
  obtain ⟨h2, s2, h11, s11⟩ := vine11_values_1
  rw [h2, s2, h11, s11, stdMass_table_1]
  norm_num

/-- **Table 7, the division rule** (Conway–Sloane 1988, p. 275): each entry of a column is the entry above divided by
$2r$, e.g. the column $11_1 \oplus I_{n-1}$: $\frac12, \frac14, \frac1{16}, \frac1{96}, \frac1{768}, \frac1{7680},
\frac1{92160}$ (dividing by $2, 4, 6, 8, 10, 12$), and the column $11^+_2 \oplus I_{n-2}$: $\frac12, \frac14, \frac1{16},
\frac1{96}, \frac1{768}, \frac1{7680}$. -/
@[kb "conwaysloane1988" "Table 7, p. 275 (division by 2r)"]
theorem table7_division :
    ((1 : ℚ) / 2 / 2 = 1 / 4 ∧ (1 : ℚ) / 4 / 4 = 1 / 16 ∧ (1 : ℚ) / 16 / 6 = 1 / 96 ∧ (1 : ℚ) / 96 / 8 = 1 / 768 ∧
      (1 : ℚ) / 768 / 10 = 1 / 7680 ∧ (1 : ℚ) / 7680 / 12 = 1 / 92160) ∧
    ((1 : ℚ) / 240 / 2 = 1 / 480 ∧ (1 : ℚ) / 480 / 4 = 1 / 1920) ∧ (1 : ℚ) / 3840 / 2 = 1 / 7680 := by
  norm_num

/-- **Table 7, the even rows** (Conway–Sloane 1988, p. 275): $\frac14 + \frac12 = \frac34$ ($n = 2$),
$\frac1{96} + \frac1{16} = \frac7{96}$ ($n = 4$), $\frac1{7680} + \frac1{768} + \frac1{480} = \frac9{2560}$ ($n = 6$; the
even genus $11_6$, $\{\frac1{3840}\}$, does not contribute). -/
@[kb "conwaysloane1988" "Table 7, p. 275 (sums, n even)"]
theorem table7_rows_even :
    (1 / 4 + 1 / 2 : ℚ) = 3 / 4 ∧ (1 / 96 + 1 / 16 : ℚ) = 7 / 96 ∧ (1 / 7680 + 1 / 768 + 1 / 480 : ℚ) = 9 / 2560 := by
  norm_num

/-! ### §9 (iv): the even unimodular genus $\mathrm{II}_8$ -/

/-- The 2-adic symbol $1^{+8}_{\mathrm{II}}$ of an even unimodular form of dimension 8 ($E_8$). -/
def e8Two : TwoSymbol := fun k => if k = 0 then ⟨8, .plus, .II, 0⟩ else TwoFactor.trivial

/-- **§9 (iv) for $\mathrm{II}_8$** (Conway–Sloane 1988, p. 274: "For $d = 1$ (2) easily yields the expressions for
the mass of unimodular lattices"): for the symbol $1^{+8}_{\mathrm{II}}$ (constituent $\mathrm{II}_8{:}0$, free, species
$8+$, type factor $2^{-8}$) the working form of (2), $\mathrm{std}(f)\,m_2(f)/\mathrm{std}_2(f)$ with
$\mathrm{std}(f) = \zeta_1(4)/(30240\pi^4)$ (Table 3) and $\zeta_1(4) = \pi^4/96$ ((15)), is $\frac1{696729600}$,
the mass of the genus of $E_8$. -/
@[kb "conwaysloane1988" "§9 (iv), p. 274 (II_8)"]
theorem unimodular_II8 : stdMass 8 1 * (pMassTwo e8Two 1 / stdP 2 8 1) = 1 / 696729600 := by
  have hd : diagProdTwo e8Two 1 = 1 / (2 * (3 / 4) * (15 / 16) * (63 / 64) * (15 / 16)) := by
    simp (config := { decide := true }) [diagProdTwo, halfFactor, e8Two, Finset.prod_range_succ, twoSpecies,
      IsBound, octane, TwoFactor.trivial, Species.diagFactor, lowerProd, Sign.toInt]
    norm_num
  have hc : crossExp (fun k => (e8Two k).dim) 1 = 0 := by decide
  have hII : nII e8Two 1 = 8 := by decide
  have hII' : nII' e8Two 1 = 0 := by decide
  have hs : stdP 2 8 1 = 1 / (2 * (3 / 4) * (15 / 16) * (63 / 64)) := by
    norm_num [stdP, lowerProd, Finset.prod_range_succ]
  have hm : pMassTwo e8Two 1 = 1 / (2 * (3 / 4) * (15 / 16) * (63 / 64) * (15 / 16)) / 256 := by
    rw [pMassTwo, hd, hc, hII, hII']; push_cast; norm_num
  rw [hm, hs, stdMass_table_8, show ((-1 : ℤ) ^ 4 * 1) = 1 by norm_num, zetaD_one_four]
  have hpi : (π : ℝ) ^ 4 ≠ 0 := by positivity
  push_cast
  field_simp
  norm_num

end QuadFormsKB.ConwaySloane.Mass
