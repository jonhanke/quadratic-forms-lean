/-
# Conway–Sloane 1988, §9 (ii): the mass of $a_3 \oplus I_1$ is $\frac3{32}$

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), §9 (ii), pp. 272–273 (bibliography key `conwaysloane1988`). The four-dimensional form
$f = a_3 \oplus I_1$ of determinant $24$ has Gram matrix
$$\begin{pmatrix}7&1&1&0\\1&2&0&0\\1&0&2&0\\0&0&0&1\end{pmatrix}$$
(`ex2Gram`; $a_3$ is the first three-dimensional form of determinant $24$ in the table of Part I, §5), in the
variables $x_0, \ldots, x_3$, and the paper computes $m(f) = \frac3{\sqrt2}\cdot\frac{3\sqrt3}2\cdot\mathrm{std}(f) = \frac3{32}$.

**Proof.**
* The integral substitution `ex2T` (columns $e_0$, $7e_1 - e_0$, $13e_2 + e_1 - 2e_0$, $e_3$, determinant $91$) gives
  $T^{\mathsf T}fT = \mathrm{diag}(7, 91, 312, 1)$ (`ex2T_congr`); this is the paper's diagonalization
  $\mathrm{diag}\{7, 13/7, 24/13\} \oplus 1$ with each vector scaled by an integer prime to $2$ and $3$.
* Over $\mathbb Z_2$: $91 \equiv 3$, $312 = 8\cdot39$, $39 \equiv 7 \pmod 8$, so $f \cong_2 \langle7, 3, 1\rangle \perp 8\langle7\rangle$, whose symbol
  is the paper's $1^{-3}_3 8^{+1}_7$ (`isTwoSymbolOf_ex2`, the symbol `ex2Two` of `Examples.lean`).
* Over $\mathbb Z_3$: $\mathrm{diag}(7, 91, 1) \perp 3\cdot\langle104\rangle$ with $7\cdot91 \equiv 1$ a square and $104 \equiv 2$ a
  non-square mod $3$: the symbol $1^{+3}3^{-1}$ (`isOddSymbolOf_ex2`, the symbol `ex2Three`).
* The mass formula (`mass_eq_stdMass_mul_symbols_unconditional`), the $p$-masses $m_2 = \sqrt2$, $m_3 = 27\sqrt3/32$
  (`example_ii_two`, `example_ii_three`), $\mathrm{std}(f) = \zeta_{24}(2)/(6\pi^2)$ (Table 3) and
  $\zeta_{24}(2) = \pi^2\sqrt6/24$ (`zetaD_twentyfour_two`) give $m(f) = \frac3{32}$.

**Proves** `example_ii_mass` (§9 (ii), p. 273): $m(a_3 \oplus I_1) = \frac3{32}$. Unconditional.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.ZetaSix
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicFinal
import QuadFormsKB.Literature.Cassels.Ch9.Ex6Ex15
import QuadFormsKB.Literature.ConwaySloane.Mass.Duality

open Matrix QuadFormsKB QuadFormsKB.LocalDensity

namespace QuadFormsKB.ConwaySloane.Mass

/-- The Gram matrix of $f = a_3 \oplus I_1$ (Conway–Sloane 1988, §9 (ii), p. 272). -/
def ex2Gram : Matrix (Fin 4) (Fin 4) ℤ := !![7, 1, 1, 0; 1, 2, 0, 0; 1, 0, 2, 0; 0, 0, 0, 1]

/-- The diagonalizing substitution (columns $e_0$, $7e_1 - e_0$, $13e_2 + e_1 - 2e_0$, $e_3$; determinant $91$). -/
def ex2T : Matrix (Fin 4) (Fin 4) ℤ := !![1, -1, -2, 0; 0, 7, 1, 0; 0, 0, 13, 0; 0, 0, 0, 1]

theorem ex2T_congr : ex2Tᵀ * ex2Gram * ex2T = !![7, 0, 0, 0; 0, 91, 0, 0; 0, 0, 312, 0; 0, 0, 0, 1] := by
  decide

theorem ex2T_det : ex2T.det = 91 := by
  simp [ex2T, Matrix.det_succ_row_zero, Fin.sum_univ_succ]

theorem ex2Gram_det : ex2Gram.det = 24 := by
  simp [ex2Gram, Matrix.det_succ_row_zero, Fin.sum_univ_succ]; rfl

theorem ex2Gram_symm : ex2Gram.IsSymm := by
  unfold Matrix.IsSymm; decide

theorem eval_ex2 (x : Fin 4 → ℤ) : (ofMatrixZ ex2Gram).eval x =
    5 * x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + (x 0 + x 1) ^ 2 + (x 0 + x 2) ^ 2 := by
  rw [eval_ofMatrixZ]
  simp [ex2Gram, dotProduct, mulVec, Fin.sum_univ_four]
  ring

theorem ex2Gram_posDef : IntQF.PosDef (ofMatrixZ ex2Gram) := by
  intro x hx
  rw [eval_ex2]
  have : x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 ∨ x 3 ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext fun i => by fin_cases i <;> simp [h.1, h.2.1, h.2.2.1, h.2.2.2])
  rcases this with h | h | h | h <;> positivity

/-! ### Diagonal $\mathbb Z_p$-equivalences -/

/-- Diagonal forms whose entries differ by unit squares are $\mathbb Z_p$-equivalent. -/
theorem zpEquiv_diagonal {p n : ℕ} [Fact p.Prime] (a b : Fin n → ℚ_[p])
    (h : ∀ i, ∃ t : ℤ_[p], IsUnit t ∧ (t : ℚ_[p]) * a i * t = b i) :
    Cassels.ZpEquiv (Matrix.diagonal a) (Matrix.diagonal b) := by
  choose t ht using h
  refine ⟨⟨Matrix.diagonal t, Matrix.diagonal (fun i => (((ht i).1.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p])), ?_, ?_⟩, ?_⟩
  · rw [Matrix.diagonal_mul_diagonal]
    simp
  · rw [Matrix.diagonal_mul_diagonal]
    simp
  · show ((Matrix.diagonal t).map PadicInt.Coe.ringHom)ᵀ * Matrix.diagonal a *
      (Matrix.diagonal t).map PadicInt.Coe.ringHom = Matrix.diagonal b
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact (ht i).2

/-- Two odd integers congruent mod $8$ differ by a unit square of $\mathbb Z_2$. -/
theorem unitSq_of_mod8 (w u : ℤ) (hw : Odd w) (h : (8 : ℤ) ∣ w - u) :
    ∃ t : ℤ_[2], IsUnit t ∧ (t : ℚ_[2]) * w * t = u := by
  obtain ⟨T, hT⟩ := Cassels.dyadic_zpEquiv_of_int !![w] !![u] 1 (by ext i j; fin_cases i; fin_cases j; rfl)
    (by ext i j; fin_cases i; fin_cases j; rfl) (by simpa using hw) (by simp) (fun i j => by
      fin_cases i; fin_cases j; simpa using h)
  refine ⟨T.val 0 0, ?_, ?_⟩
  · have := (Matrix.isUnit_iff_isUnit_det _).1 T.isUnit
    rwa [Matrix.det_unique] at this
  · have := congrFun (congrFun hT 0) 0
    simp [Matrix.mul_apply] at this
    rw [← this]

/-- The 2-adic block decomposition $\langle7\rangle \perp \langle3\rangle \perp 8\langle7\rangle \perp \langle1\rangle$ of $a_3 \oplus I_1$. -/
def ex2Blocks : List Cassels.DyBlock := [.sq 0 7, .sq 0 3, .sq 3 7, .sq 0 1]

/-- **A 2-adic symbol of $a_3 \oplus I_1$ is $1^{-3}_3 8^{+1}_7$** (Conway–Sloane 1988, §9 (ii), p. 273: the 2-adic
decomposition $\mathrm{diag}\{7, 13/7\} \oplus 8\,\mathrm{diag}\{3/13\} \oplus I_1$). -/
@[kb "conwaysloane1988" "§9 (ii), p. 273 (2-adic decomposition)"]
theorem isTwoSymbolOf_ex2 : IsTwoSymbolOf (ex2Gram.map (Int.cast : ℤ → ℚ_[2])) ex2Two := by
  refine ⟨ex2Blocks, ?_, ?_, rfl, ?_, ?_⟩
  · intro b hb
    simp only [ex2Blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> simp [Cassels.DyBlock.Valid]
  · intro b hb
    simp only [ex2Blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> simp [blockExp]
  · have h1 := Cassels.Ch9Ex6.zpEquiv_of_unit_det (p := 2) ex2Gram ex2T (by rw [ex2T_det]; decide)
    rw [ex2T_congr] at h1
    refine h1.trans ?_
    have hd : (!![7, 0, 0, 0; 0, 91, 0, 0; 0, 0, 312, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℤ).map
        (Int.cast : ℤ → ℚ_[2]) = Matrix.diagonal ![((7 : ℤ) : ℚ_[2]), ((91 : ℤ) : ℚ_[2]), (8 : ℚ_[2]) * ((39 : ℤ) : ℚ_[2]),
          ((1 : ℤ) : ℚ_[2])] := by
      ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal]
    have hD : ∀ h : Cassels.dyDim ex2Blocks = 4, (Cassels.dyMat ex2Blocks).submatrix (Fin.cast h.symm) (Fin.cast h.symm) =
        Matrix.diagonal ![((7 : ℤ) : ℚ_[2]), ((3 : ℤ) : ℚ_[2]), (8 : ℚ_[2]) * ((7 : ℤ) : ℚ_[2]), ((1 : ℤ) : ℚ_[2])] := by
      intro h
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [ex2Blocks, Cassels.dyMat, Cassels.orthSumMat, Cassels.DyBlock.mat, Matrix.diagonal,
          Matrix.fromBlocks, finSumFinEquiv] <;> norm_num <;> rfl
    rw [hd, hD rfl]
    apply zpEquiv_diagonal
    intro i
    fin_cases i
    · exact unitSq_of_mod8 7 7 (by decide) (by decide)
    · exact unitSq_of_mod8 91 3 (by decide) (by decide)
    · obtain ⟨t, ht, he⟩ := unitSq_of_mod8 39 7 (by decide) (by decide)
      refine ⟨t, ht, ?_⟩
      show (t : ℚ_[2]) * ((8 : ℚ_[2]) * ((39 : ℤ) : ℚ_[2])) * t = (8 : ℚ_[2]) * ((7 : ℤ) : ℚ_[2])
      rw [← he]; ring
    · exact unitSq_of_mod8 1 1 (by decide) (by decide)
  · funext k
    by_cases hk0 : k = 0
    · subst hk0
      simp only [ex2Two, if_true, blockSymbol, ex2Blocks]
      decide
    by_cases hk3 : k = 3
    · subst hk3
      simp only [ex2Two, blockSymbol, ex2Blocks]
      decide
    · have h0 : ¬ ((0 : ℤ) = (k : ℤ)) := by omega
      have h3 : ¬ ((3 : ℤ) = (k : ℤ)) := by omega
      simp [ex2Two, hk0, hk3, blockSymbol, ex2Blocks, blockExp, h0, h3, Sign.prodList, TwoFactor.trivial]

/-- **The 3-adic symbol of $a_3 \oplus I_1$ is $1^{+3}3^{-1}$** (Conway–Sloane 1988, §9 (ii), p. 273: the 3-adic
decomposition $\mathrm{diag}\{7, 13/7\} \oplus 3\,\mathrm{diag}\{8/13\} \oplus I_1$). -/
@[kb "conwaysloane1988" "§9 (ii), p. 273 (3-adic decomposition)"]
theorem isOddSymbolOf_ex2 :
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    IsOddSymbolOf 3 (ex2Gram.map (Int.cast : ℤ → ℚ_[3])) ex2Three := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine ⟨![0, 0, 1, 0], ![((7 : ℤ) : ℚ_[3]), ((91 : ℤ) : ℚ_[3]), ((104 : ℤ) : ℚ_[3]), ((1 : ℤ) : ℚ_[3])], ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> exact norm_intCast_eq_one (by decide)
  · have h1 := Cassels.Ch9Ex6.zpEquiv_of_unit_det (p := 3) ex2Gram ex2T (by rw [ex2T_det]; decide)
    rw [ex2T_congr] at h1
    convert h1 using 1
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal]
  · have hsq : IsSquare (((7 : ℤ) : ℚ_[3]) * ((91 : ℤ) : ℚ_[3]) * ((1 : ℤ) : ℚ_[3])) := by
      rw [show ((7 : ℤ) : ℚ_[3]) * ((91 : ℤ) : ℚ_[3]) * ((1 : ℤ) : ℚ_[3]) = ((637 : ℤ) : ℚ_[3]) by push_cast; ring]
      exact (isSquare_padic_iff (p := 3) (by norm_num) (by decide)).2 (by norm_num)
    have hns : ¬ IsSquare ((104 : ℤ) : ℚ_[3]) := not_isSquare_of_jacobiSym (by norm_num)
    funext k
    simp only [oddSymbolOfDiag, ex2Three]
    by_cases hk0 : k = 0
    · subst hk0
      have hc : Fintype.card {i : Fin 4 // (![0, 0, 1, 0] : Fin 4 → ℕ) i = 0} = 3 := by decide
      have hp : (∏ i : {i : Fin 4 // (![0, 0, 1, 0] : Fin 4 → ℕ) i = 0},
          (![((7 : ℤ) : ℚ_[3]), ((91 : ℤ) : ℚ_[3]), ((104 : ℤ) : ℚ_[3]), ((1 : ℤ) : ℚ_[3])] : Fin 4 → ℚ_[3]) i) =
          ((7 : ℤ) : ℚ_[3]) * ((91 : ℤ) : ℚ_[3]) * ((1 : ℤ) : ℚ_[3]) := by
        rw [← Finset.prod_subtype (Finset.univ.filter fun i : Fin 4 => (![0, 0, 1, 0] : Fin 4 → ℕ) i = 0)
          (fun i => by simp)
          (fun i => (![((7 : ℤ) : ℚ_[3]), ((91 : ℤ) : ℚ_[3]), ((104 : ℤ) : ℚ_[3]), ((1 : ℤ) : ℚ_[3])] : Fin 4 → ℚ_[3]) i)]
        rw [Finset.prod_filter, Fin.prod_univ_four]
        simp
      rw [hc, hp, if_pos hsq]
      simp
    by_cases hk1 : k = 1
    · subst hk1
      have hc : Fintype.card {i : Fin 4 // (![0, 0, 1, 0] : Fin 4 → ℕ) i = 1} = 1 := by decide
      have hp : (∏ i : {i : Fin 4 // (![0, 0, 1, 0] : Fin 4 → ℕ) i = 1},
          (![((7 : ℤ) : ℚ_[3]), ((91 : ℤ) : ℚ_[3]), ((104 : ℤ) : ℚ_[3]), ((1 : ℤ) : ℚ_[3])] : Fin 4 → ℚ_[3]) i) =
          ((104 : ℤ) : ℚ_[3]) := by
        rw [← Finset.prod_subtype (Finset.univ.filter fun i : Fin 4 => (![0, 0, 1, 0] : Fin 4 → ℕ) i = 1)
          (fun i => by simp)
          (fun i => (![((7 : ℤ) : ℚ_[3]), ((91 : ℤ) : ℚ_[3]), ((104 : ℤ) : ℚ_[3]), ((1 : ℤ) : ℚ_[3])] : Fin 4 → ℚ_[3]) i)]
        rw [Finset.prod_filter, Fin.prod_univ_four]
        simp
      rw [hc, hp, if_neg hns]
      simp
    · have hc : Fintype.card {i : Fin 4 // (![0, 0, 1, 0] : Fin 4 → ℕ) i = k} = 0 := by
        rw [Fintype.card_eq_zero_iff]
        constructor
        rintro ⟨i, hi⟩
        fin_cases i <;> simp at hi <;> omega
      have hp : (∏ i : {i : Fin 4 // (![0, 0, 1, 0] : Fin 4 → ℕ) i = k},
          (![((7 : ℤ) : ℚ_[3]), ((91 : ℤ) : ℚ_[3]), ((104 : ℤ) : ℚ_[3]), ((1 : ℤ) : ℚ_[3])] : Fin 4 → ℚ_[3]) i) = 1 := by
        have : IsEmpty {i : Fin 4 // (![0, 0, 1, 0] : Fin 4 → ℕ) i = k} := Fintype.card_eq_zero_iff.1 hc
        exact Finset.prod_of_isEmpty _
      rw [hc, hp, if_pos IsSquare.one]
      simp [hk0, hk1, OddFactor.trivial]

/-- **§9 (ii): the mass of $a_3 \oplus I_1$ is $\frac3{32}$** (Conway–Sloane 1988, p. 273):
$m(f) = \frac3{\sqrt2}\cdot\frac{3\sqrt3}2\cdot\mathrm{std}(f) = \frac{9\sqrt3}{2\sqrt2}\cdot\frac{\zeta_{24}(2)}{6\pi^2} = \frac3{32}$,
for the Gram matrix $\begin{pmatrix}7&1&1&0\\1&2&0&0\\1&0&2&0\\0&0&0&1\end{pmatrix}$ of $a_3 \oplus I_1$. Unconditional:
the mass formula (`mass_eq_stdMass_mul_symbols_unconditional`), the certified symbols and
$\zeta_{24}(2) = \pi^2\sqrt6/24$ (`zetaD_twentyfour_two`). -/
@[kb "conwaysloane1988" "§9 (ii), p. 273 (m(a₃ ⊕ I₁) = 3/32)"]
theorem example_ii_mass : Siegel.mass (ofMatrixZ ex2Gram) = 3 / 32 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hsupp2 : ex2Two.SupportedBelow 4 := fun k hk => by
    simp [ex2Two, show k ≠ 0 by omega, show k ≠ 3 by omega]
  have hsupp3 : ∀ k, 2 ≤ k → ex2Three k = OddFactor.trivial := fun k hk => by
    simp [ex2Three, show k ≠ 0 by omega, show k ≠ 1 by omega]
  rw [mass_eq_stdMass_mul_symbols_unconditional (by norm_num) ex2Gram_symm ex2Gram_posDef ex2Two 4
    isTwoSymbolOf_ex2 hsupp2 (fun _ => ex2Three) (fun _ => 2) ?_]
  · have hpf : (2 * ex2Gram.det).natAbs.primeFactors = {2, 3} := by
      rw [ex2Gram_det, show (2 * (24 : ℤ)).natAbs = 2 ^ 4 * 3 by norm_num,
        Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
        Nat.Prime.primeFactors (by norm_num)]
      rfl
    rw [hpf, ex2Gram_det]
    rw [Finset.prod_insert (by decide), Finset.prod_singleton, if_pos rfl, if_neg (by norm_num)]
    obtain ⟨hm2, hs2, -⟩ := example_ii_two
    obtain ⟨hm3, hs3, -⟩ := example_ii_three
    rw [hm2, hs2, hm3, hs3, stdMass_table_4, show ((-1 : ℤ) ^ 2 * 24) = 24 by norm_num, zetaD_twentyfour_two]
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have h6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
      rw [← Real.sqrt_mul (by norm_num)]; norm_num
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    rw [h6]
    field_simp
    nlinarith [h2, h3]
  · intro p hp hp2 hdvd
    rw [ex2Gram_det] at hdvd
    have hp3 : p = 3 := by
      have h1 : p ∣ 24 := by exact_mod_cast hdvd
      have h2 : p ∣ 2 ^ 3 * 3 := by simpa using h1
      rcases (Nat.Prime.dvd_mul hp).1 h2 with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)) hp2
      · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
    subst hp3
    exact ⟨isOddSymbolOf_ex2, hsupp3⟩

end QuadFormsKB.ConwaySloane.Mass
