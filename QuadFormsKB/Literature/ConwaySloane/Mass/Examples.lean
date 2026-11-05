/-
# Conway–Sloane 1988, §9: the worked examples, on the genus symbols

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), §9, pp. 269–273 (bibliography key `conwaysloane1988`).

The tableaux of §9 (i) and (ii) compute the $p$-masses (3) of two forms at the primes dividing $2d$. This file
evaluates `pMassOdd` and `pMassTwo` on the symbols of these forms and compares with $\mathrm{std}_p$ ((6), (17)).

* (i) $f = \mathrm{diag}(7,1,1)$, $d = 7$. 2-adic: one constituent $f_1 = f$, type I, dimension 3, oddity
  $7+1+1 \equiv 1$, sign $+$ (octane value $-1+1+1 = 1$), so the symbol is $1^{+3}_1$ (`ex1Two`). 7-adic:
  $f_1 = \mathrm{diag}(1,1)$ (sign $+$), $f_7 = \mathrm{diag}(1)$ (sign $+$): $1^{+2}7^{+1}$ (`ex1Seven`).
  Values: $m_2 = \frac14 = \frac38\mathrm{std}_2$, $m_7 = \frac{49}{32} = 3\,\mathrm{std}_7$.
* (ii) $f = a_3 \oplus I_1$, $d = 24$, $a_3$ with Gram matrix $\begin{pmatrix}7&1&1\\1&2&0\\1&0&2\end{pmatrix}$. 2-adic
  decomposition $\mathrm{diag}(7, 13/7, 1) \oplus 8\,\mathrm{diag}(3/13)$: $f_1$ of type I, dimension 3, oddity
  $7 + 3 + 1 \equiv 3$ ($13/7 \equiv 3$), sign $-$ (octane $-1$); $f_8$ of type I, dimension 1, oddity $7$
  ($3/13 \equiv 7$), sign $+$ (octane $-1$): $1^{-3}_3 8^{+1}_7$ (`ex2Two`). 3-adic: $\mathrm{diag}(7, 13/7, 1) \oplus
  3\,\mathrm{diag}(8/13)$: $1^{+3}3^{-1}$ (`ex2Three`; $13 \equiv 1$, $8/13 \equiv 2 \pmod 3$).
  Values: $m_2 = \sqrt2 = \frac3{\sqrt2}\mathrm{std}_2$, $m_3 = \frac{27\sqrt3}{32} = \frac{3\sqrt3}2\mathrm{std}_3$.

The symbols are entered by hand from the paper's decompositions (the $p$-adic computations above).
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.PMass

namespace QuadFormsKB.ConwaySloane.Mass

open Finset

/-! ### Example (i): $\mathrm{diag}(7,1,1)$ -/

/-- The 2-adic symbol $1^{+3}_1$ of $\mathrm{diag}(7,1,1)$ (Conway–Sloane 1988, §9 (i), p. 269). -/
def ex1Two : TwoSymbol := fun k => if k = 0 then ⟨3, .plus, .I, 1⟩ else TwoFactor.trivial

/-- The 7-adic symbol $1^{+2}7^{+1}$ of $\mathrm{diag}(7,1,1)$ (Conway–Sloane 1988, §9 (i), p. 269). -/
def ex1Seven : OddSymbol := fun k => if k = 0 then ⟨2, .plus⟩ else if k = 1 then ⟨1, .plus⟩ else OddFactor.trivial

/-- **§9 (i), $p = 2$** (Conway–Sloane 1988, tableau p. 272): $f_{1/2}$ and $f_2$ are bound love forms (species 1,
factor $\frac12$), $f_1 = \mathrm I_3{:}1$ is free of species $2+$ (factor 1); diagonal product $\frac14$, cross term
$1$, type factor $2^{0-0}$: $m_2(f) = \frac14 = \frac38\mathrm{std}_2(f)$. -/
@[kb "conwaysloane1988" "§9 (i), p. 272 (p = 2)"]
theorem example_i_two : pMassTwo ex1Two 1 = 1 / 4 ∧ (stdP 2 3 7 : ℝ) = 2 / 3 ∧
    pMassTwo ex1Two 1 = 3 / 8 * (stdP 2 3 7 : ℝ) := by
  have hd : diagProdTwo ex1Two 1 = 1 / 4 := by
    simp (config := { decide := true }) [diagProdTwo, halfFactor, ex1Two, Finset.prod_range_succ, twoSpecies,
      IsBound, octane, TwoFactor.trivial, Species.diagFactor, lowerProd, Sign.toInt]
    norm_num
  have hs : stdP 2 3 7 = 2 / 3 := by
    simp [stdP, lowerProd]; norm_num
  have hm : pMassTwo ex1Two 1 = 1 / 4 := by
    have hc : crossExp (fun k => (ex1Two k).dim) 1 = 0 := by decide
    have hII : nII ex1Two 1 = 0 := by decide
    have hII' : nII' ex1Two 1 = 0 := by decide
    rw [pMassTwo, hd, hc, hII, hII']; norm_num
  refine ⟨hm, by rw [hs]; norm_num, by rw [hm, hs]; norm_num⟩

/-- **§9 (i), $p = 7$** (Conway–Sloane 1988, tableau p. 272): $f_1 = R_2$ of species $2-$ (factor $\frac7{16}$),
$f_7 = R_1$ of species 1 (factor $\frac12$), cross term $\sqrt{7^{2\times1}}$: $m_7(f) = \frac{49}{32} =
3\,\mathrm{std}_7(f)$. -/
@[kb "conwaysloane1988" "§9 (i), p. 272 (p = 7)"]
theorem example_i_seven : pMassOdd 7 ex1Seven 2 = 49 / 32 ∧ (stdP 7 3 7 : ℝ) = 49 / 96 ∧
    pMassOdd 7 ex1Seven 2 = 3 * (stdP 7 3 7 : ℝ) := by
  have hd : (∏ k ∈ range 2, (oddSpecies 7 (ex1Seven k)).diagFactor 7) = 7 / 32 := by
    simp [ex1Seven, Finset.prod_range_succ, oddSpecies, Species.diagFactor, lowerProd, Sign.flip, Sign.toInt]
    norm_num
  have hc : crossExp (fun k => (ex1Seven k).dim) 2 = 2 := by decide
  have hs : stdP 7 3 7 = 49 / 96 := by
    simp [stdP, lowerProd]; norm_num
  have h7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have hm : pMassOdd 7 ex1Seven 2 = 49 / 32 := by
    rw [pMassOdd, hd, hc]; push_cast; rw [h7]; norm_num
  refine ⟨hm, by rw [hs]; norm_num, by rw [hm, hs]; norm_num⟩

/-! ### Example (ii): $a_3 \oplus I_1$ -/

/-- The 2-adic symbol $1^{-3}_3 8^{+1}_7$ of $a_3 \oplus I_1$ (Conway–Sloane 1988, §9 (ii), p. 273). -/
def ex2Two : TwoSymbol := fun k =>
  if k = 0 then ⟨3, .minus, .I, 3⟩ else if k = 3 then ⟨1, .plus, .I, 7⟩ else TwoFactor.trivial

/-- The 3-adic symbol $1^{+3}3^{-1}$ of $a_3 \oplus I_1$ (Conway–Sloane 1988, §9 (ii), p. 273). -/
def ex2Three : OddSymbol := fun k =>
  if k = 0 then ⟨3, .plus⟩ else if k = 1 then ⟨1, .minus⟩ else OddFactor.trivial

/-- **§9 (ii), $p = 2$** (Conway–Sloane 1988, tableau p. 273): bound love forms $f_{1/2}, f_2, f_4, f_{16}$ (factor
$\frac12$ each), $f_1 = \mathrm I_3{:}-1$ of species $2+$ and $f_8 = \mathrm I_1{:}-1$ of species $0+$ (factor 1);
diagonal product $\frac1{16}$, cross term $\sqrt{8^{3\times1}}$, type factor $2^{0-0}$:
$m_2(f) = \sqrt2 = \frac3{\sqrt2}\mathrm{std}_2(f)$. -/
@[kb "conwaysloane1988" "§9 (ii), p. 273 (p = 2)"]
theorem example_ii_two : pMassTwo ex2Two 4 = Real.sqrt 2 ∧ (stdP 2 4 24 : ℝ) = 2 / 3 ∧
    pMassTwo ex2Two 4 = 3 / Real.sqrt 2 * (stdP 2 4 24 : ℝ) := by
  have hd : diagProdTwo ex2Two 4 = 1 / 16 := by
    simp (config := { decide := true }) [diagProdTwo, halfFactor, ex2Two, Finset.prod_range_succ, twoSpecies,
      IsBound, octane, TwoFactor.trivial, Species.diagFactor, lowerProd, Sign.toInt]
    norm_num
  have hc : crossExp (fun k => (ex2Two k).dim) 4 = 9 := by decide
  have hII : nII ex2Two 4 = 0 := by decide
  have hII' : nII' ex2Two 4 = 0 := by decide
  have hs : stdP 2 4 24 = 2 / 3 := by
    simp [stdP, lowerProd]; norm_num
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2' : Real.sqrt 2 ≠ 0 := by positivity
  have hm : pMassTwo ex2Two 4 = Real.sqrt 2 := by
    rw [pMassTwo, hd, hc, hII, hII']
    have : Real.sqrt 2 ^ 9 = 16 * Real.sqrt 2 := by
      rw [show 9 = 2 * 4 + 1 by rfl, pow_succ, pow_mul, h2]; norm_num
    rw [this]; norm_num; ring
  refine ⟨hm, by rw [hs]; norm_num, ?_⟩
  rw [hm, hs]
  field_simp
  rw [h2]; norm_num

/-- **§9 (ii), $p = 3$** (Conway–Sloane 1988, tableau p. 273): $f_1 = R_3$ of species 3 (factor $\frac9{16}$),
$f_3 = N_1$ of species 1 (factor $\frac12$), cross term $\sqrt{3^{3\times1}}$:
$m_3(f) = \frac{27\sqrt3}{32} = \frac{3\sqrt3}2\mathrm{std}_3(f)$. -/
@[kb "conwaysloane1988" "§9 (ii), p. 273 (p = 3)"]
theorem example_ii_three : pMassOdd 3 ex2Three 2 = 27 * Real.sqrt 3 / 32 ∧ (stdP 3 4 24 : ℝ) = 9 / 16 ∧
    pMassOdd 3 ex2Three 2 = 3 * Real.sqrt 3 / 2 * (stdP 3 4 24 : ℝ) := by
  have hd : (∏ k ∈ range 2, (oddSpecies 3 (ex2Three k)).diagFactor 3) = 9 / 32 := by
    simp [ex2Three, Finset.prod_range_succ, oddSpecies, Species.diagFactor, lowerProd]
    norm_num
  have hc : crossExp (fun k => (ex2Three k).dim) 2 = 3 := by decide
  have hs : stdP 3 4 24 = 9 / 16 := by
    simp [stdP, lowerProd]; norm_num
  have h3 : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
    rw [pow_succ, Real.sq_sqrt (by norm_num)]
  have hm : pMassOdd 3 ex2Three 2 = 27 * Real.sqrt 3 / 32 := by
    rw [pMassOdd, hd, hc]; push_cast; rw [h3]; ring
  refine ⟨hm, by rw [hs]; norm_num, by rw [hm, hs]; push_cast; ring⟩

/-- **The ratio $m(f)/\mathrm{std}(f)$ need not be rational** (clarification of Conway–Sloane 1988, §7, p. 266: "the
actual mass $m(f)$ will be a simple rational multiple of [$\mathrm{std}(f)$]"): in example (ii) it is
$\frac3{\sqrt2}\cdot\frac{3\sqrt3}2 = \frac{9\sqrt6}4$, irrational. It is always a rational multiple of a square root
(the cross terms are half-integral powers of $p$). -/
@[kb "conwaysloane1988" "§7, p. 266 (rational multiple); §9 (ii), p. 273"]
theorem example_ii_ratio_irrational : Irrational (3 / Real.sqrt 2 * (3 * Real.sqrt 3 / 2)) := by
  have h : 3 / Real.sqrt 2 * (3 * Real.sqrt 3 / 2) = (9 / 4 : ℚ) * Real.sqrt 6 := by
    have h2 : Real.sqrt 2 ≠ 0 := by positivity
    have h6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
      rw [← Real.sqrt_mul (by norm_num)]; norm_num
    rw [h6]; field_simp
    rw [Real.sq_sqrt (by norm_num)]; push_cast; ring
  rw [h]
  have h6 : Irrational (Real.sqrt 6) := by
    have : ¬ IsSquare (6 : ℕ) := by
      rintro ⟨r, hr⟩
      have : r ≤ 3 := by nlinarith
      interval_cases r <;> omega
    exact_mod_cast irrational_sqrt_natCast_iff.mpr this
  exact h6.ratCast_mul (by norm_num)

/-! ### §9 (iii): the abbreviated tableau -/

/-- $l$, the number of **bound love forms** (Conway–Sloane 1988, §9 (iii), p. 273): the zero-dimensional constituents
$f_q$ adjacent to a type I constituent, $f_{1/2}$ included. -/
@[kb "conwaysloane1988" "§9 (iii), p. 273"]
def boundLove (σ : TwoSymbol) (N : ℕ) : ℕ :=
  (if (σ 0).type = .I then 1 else 0) + #{k ∈ range (N + 1) | (σ k).dim = 0 ∧ IsBound σ k}

/-- **The abbreviated tableau** (Conway–Sloane 1988, §9 (iii), p. 273): "Because each bound love form contributes a
factor of $\frac12$, the tableaux may be simplified by omitting the love forms and replacing the type factor $2^{j-k}$
by $2^{j-k-l}$": the diagonal product is the product over the constituents of positive dimension times
$2^{-l}$. Hypothesis: the zero-dimensional constituents are $1^{+0}$ (type II, sign $+$, as the existence
conditions (32) of *Sphere Packings, Lattices and Groups* Ch. 15 require). -/
@[kb "conwaysloane1988" "§9 (iii), p. 273"]
theorem diagProdTwo_abbrev (σ : TwoSymbol) (N : ℕ) (hlove : ∀ k, (σ k).dim = 0 → σ k = TwoFactor.trivial) :
    diagProdTwo σ N = (∏ k ∈ range (N + 1) with (σ k).dim ≠ 0, (twoSpecies (σ k) (IsBound σ k)).diagFactor 2) *
      (1 / 2) ^ boundLove σ N := by
  unfold diagProdTwo boundLove halfFactor
  rw [← Finset.prod_filter_not_mul_prod_filter (range (N + 1)) (fun k => (σ k).dim = 0)]
  have hlv : ∏ k ∈ range (N + 1) with (σ k).dim = 0, (twoSpecies (σ k) (IsBound σ k)).diagFactor 2 =
      ∏ k ∈ range (N + 1) with (σ k).dim = 0, (if IsBound σ k then (1 / 2 : ℚ) else 1) := by
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [hlove k (Finset.mem_filter.mp hk).2]
    split_ifs with hb
    · rw [twoSpecies_trivial_bound hb]; simp [Species.diagFactor, Species.odd, lowerProd]
    · rw [twoSpecies_trivial_free hb]; rfl
  rw [hlv, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, Finset.filter_filter, pow_add]
  split_ifs <;> simp only [pow_one, pow_zero] <;> ring

end QuadFormsKB.ConwaySloane.Mass
