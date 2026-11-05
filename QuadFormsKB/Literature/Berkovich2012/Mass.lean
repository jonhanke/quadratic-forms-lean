import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Berkovich2012.Theorem61
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicFinal
import QuadFormsKB.Literature.ConwaySloane.Mass.ExampleTwo
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemma3
import QuadFormsKB.Literature.ConwaySloane.Theorem11

/-!
# Berkovich–Hanke–Jagy, Lemma 5.1 (the masses)

Source: A. Berkovich, J. Hanke and W. Jagy, *A proof of the S-genus identities for ternary quadratic
forms*, arXiv:1010.1926v2 (bib key `berkovich2012`), §5, Lemma 5.1, p. 6; §6, p. 7.

* `lemma_5_1`: for $S$ odd, the local structure of Lemma 3.1 (fields `local_odd`, `local_two` of the
  named input `SGenusStructure`) gives $\mathrm{Mass}(B_\sigma(x,y)+2Sz^2) =
  \frac1{16}\prod_{p\mid S}\frac{p+\varepsilon_p}2$. The source's proof, by the Conway–Sloane mass
  formula, which the library proves unconditionally (`mass_eq_stdMass_mul_symbols_unconditional`).
* The final `theorem_6_1`, `corollary_6_2` are in `Final.lean`.
-/

namespace QuadFormsKB.Berkovich2012

open QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.ConwaySloane QuadFormsKB.ConwaySloane.Mass
  QuadFormsKB.LocalDensity Finset

/-- The 2-adic blocks $\langle u\rangle \perp 2\langle u\rangle \perp 2\langle 1\rangle$. -/
def twoBlocks (u : ℤ) : List Cassels.DyBlock := [.sq 0 u, .sq 1 u, .sq 1 1]

theorem pMassTwo_twoBlocks (u : ℤ) (hu : u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) :
    pMassTwo (blockSymbol (twoBlocks u)) 2 = 1 / 4 := by
  have hd : diagProdTwo (blockSymbol (twoBlocks u)) 2 = 1 / 16 := by
    rcases hu with rfl | rfl | rfl | rfl <;>
    · simp (config := { decide := true }) [diagProdTwo, halfFactor, blockSymbol, twoBlocks, Finset.prod_range_succ,
        twoSpecies, IsBound, octane, Species.diagFactor, lowerProd, Sign.toInt, blockExp, IsSqBlock,
        Cassels.DyBlock.dim]
      norm_num
  have hc : crossExp (fun k => (blockSymbol (twoBlocks u) k).dim) 2 = 2 := by
    rcases hu with rfl | rfl | rfl | rfl <;> decide
  have hII : nII (blockSymbol (twoBlocks u)) 2 = 0 := by
    rcases hu with rfl | rfl | rfl | rfl <;> decide
  have hII' : nII' (blockSymbol (twoBlocks u)) 2 = 1 := by
    rcases hu with rfl | rfl | rfl | rfl <;> decide
  rw [pMassTwo, hd, hc, hII, hII']
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  push_cast; rw [h2]; norm_num

/-! ### The Gram matrix of $B(x,y) + 2Sz^2$ -/

/-- The Gram matrix $\begin{pmatrix} a & b/2 & 0\\ b/2 & c & 0\\ 0 & 0 & 2S\end{pmatrix}$ of
$B(x,y) + 2Sz^2$, $B = ax^2 + bxy + cy^2$ (integral when $b$ is even). -/
def sGram (S : ℕ) (B : BinQF) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![B.a, B.b / 2, 0; B.b / 2, B.c, 0; 0, 0, 2 * S]

lemma even_b_of_disc {S : ℕ} {B : BinQF} (hd : B.disc = -8 * S) : Even B.b := by
  have h : B.b ^ 2 = 4 * B.a * B.c - 8 * S := by unfold BinQF.disc at hd; linarith
  have h2 : Even (B.b ^ 2) := by rw [h]; exact ⟨2 * B.a * B.c - 4 * S, by ring⟩
  exact (Int.even_pow.1 h2).1

lemma sForm_eq_ofMatrixZ {S : ℕ} {B : BinQF} (hd : B.disc = -8 * S) :
    sForm S B = ofMatrixZ (sGram S B) := by
  obtain ⟨k, hk⟩ := even_b_of_disc hd
  have hk2 : B.b / 2 = k := by omega
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sForm, QuadForm.ofUpper, ofMatrixZ, sGram, hk2] <;> omega

lemma sGram_transpose (S : ℕ) (B : BinQF) : (sGram S B).transpose = sGram S B := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

lemma sGram_det {S : ℕ} {B : BinQF} (hd : B.disc = -8 * S) : (sGram S B).det = 4 * S ^ 2 := by
  obtain ⟨k, hk⟩ := even_b_of_disc hd
  have hk2 : B.b / 2 = k := by omega
  unfold BinQF.disc at hd
  rw [sGram, Matrix.det_fin_three]
  simp only [hk2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.head_fin_const]
  rw [hk] at hd
  nlinarith

lemma diag_eq_ofMatrixZ (a : Fin 3 → ℤ) : QuadForm.diag a = ofMatrixZ (Matrix.diagonal a) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [QuadForm.diag, ofMatrixZ, Matrix.diagonal]

/-- Transport of a $\mathbb Z_p$-equivalence of $B(x,y)+2Sz^2$ with a diagonal form to the Gram matrices. -/
lemma zpEquiv_of_isometricGL {p : ℕ} [Fact p.Prime] {S : ℕ} {B : BinQF} (hd : B.disc = -8 * S)
    (a : Fin 3 → ℤ)
    (h : IsometricGL ((sForm S B).map (Int.castRingHom ℤ_[p])) ((QuadForm.diag a).map (Int.castRingHom ℤ_[p]))) :
    Cassels.ZpEquiv ((sGram S B).map (Int.cast : ℤ → ℚ_[p]))
      (Matrix.diagonal fun i => ((a i : ℤ) : ℚ_[p])) := by
  rw [sForm_eq_ofMatrixZ hd, diag_eq_ofMatrixZ] at h
  have h' := (isometricGL_padic_iff (sGram_transpose S B) (Matrix.diagonal_transpose a)).1 h
  rw [Matrix.diagonal_map (map_zero _)] at h'
  exact h'

/-! ### The 2-adic symbol -/

lemma isTwoSymbolOf_sGram {S : ℕ} {B : BinQF} (hd : B.disc = -8 * S) {u : ℤ} (hu : Odd u)
    (h : IsometricGL ((sForm S B).map (Int.castRingHom ℤ_[2]))
      ((QuadForm.diag ![u, 2 * u, 2]).map (Int.castRingHom ℤ_[2]))) :
    ∃ v : ℤ, (v = 1 ∨ v = 3 ∨ v = 5 ∨ v = 7) ∧
      IsTwoSymbolOf ((sGram S B).map (Int.cast : ℤ → ℚ_[2])) (blockSymbol (twoBlocks v)) := by
  have h1 := zpEquiv_of_isometricGL hd _ h
  refine ⟨u % 8, ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := hu; omega
  have hv : Odd (u % 8) := by obtain ⟨k, rfl⟩ := hu; exact ⟨(2 * k + 1) % 8 / 2, by omega⟩
  have h8 : (8 : ℤ) ∣ u - u % 8 := ⟨u / 8, by omega⟩
  have hv' : u % 8 = 1 ∨ u % 8 = 3 ∨ u % 8 = 5 ∨ u % 8 = 7 := by obtain ⟨k, rfl⟩ := hu; omega
  refine ⟨twoBlocks (u % 8), ?_, ?_, rfl, ?_, rfl⟩
  · intro b hb
    simp only [twoBlocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp [Cassels.DyBlock.Valid, hv']
  · intro b hb
    simp only [twoBlocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp [blockExp]
  · refine h1.trans ?_
    have hD : ∀ h : Cassels.dyDim (twoBlocks (u % 8)) = 3,
        (Cassels.dyMat (twoBlocks (u % 8))).submatrix (Fin.cast h.symm) (Fin.cast h.symm) =
        Matrix.diagonal ![((u % 8 : ℤ) : ℚ_[2]), 2 * ((u % 8 : ℤ) : ℚ_[2]), 2] := by
      intro h
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [twoBlocks, Cassels.dyMat, Cassels.orthSumMat, Cassels.DyBlock.mat, Matrix.diagonal,
          Matrix.fromBlocks, finSumFinEquiv] <;> rfl
    rw [hD (by simp [twoBlocks, Cassels.dyDim, Cassels.DyBlock.dim])]
    apply zpEquiv_diagonal
    intro i
    obtain ⟨t, ht, he⟩ := unitSq_of_mod8 u (u % 8) hu h8
    fin_cases i
    · exact ⟨t, ht, by simpa using he⟩
    · refine ⟨t, ht, ?_⟩
      push_cast
      rw [← he]; ring
    · exact ⟨1, isUnit_one, by simp⟩

/-! ### The $p$-adic symbols, $p \mid S$ -/

/-- The $p$-adic symbol $1^{\pm 1} p^{\pm 2}$ of $\alpha x^2 + \alpha p y^2 + p z^2$ (both signs
$\left(\frac{\alpha}{p}\right)$). -/
def oddSym (s : Sign) : OddSymbol := fun k =>
  if k = 0 then ⟨1, s⟩ else if k = 1 then ⟨2, s⟩ else OddFactor.trivial

lemma pMassOdd_oddSym_ratio (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (s : Sign) (d : ℤ) :
    pMassOdd p (oddSym s) 2 / (stdP p 3 d : ℝ) =
      ((p : ℝ) + (oddSpecies p ⟨2, s⟩).sign.toInt) / 2 := by
  have hp3 : (3 : ℝ) ≤ p := by
    have := (Fact.out : p.Prime).two_le
    have : p ≠ 2 := hp2
    exact_mod_cast (show 3 ≤ p by omega)
  have hc : crossExp (fun k => (oddSym s k).dim) 2 = 2 := by
    simp [crossExp, oddSym, Finset.sum_range_succ]
  have hdiag : (∏ k ∈ range 2, (oddSpecies p (oddSym s k)).diagFactor p) =
      (2 : ℚ)⁻¹ * (2 * (1 - (oddSpecies p ⟨2, s⟩).sign.toInt * (p : ℚ)⁻¹))⁻¹ := by
    simp [Finset.prod_range_succ, oddSym, oddSpecies, Species.diagFactor, lowerProd]
  have hstd : stdP p 3 d = (2 * (1 - ((p : ℚ) ^ 2)⁻¹))⁻¹ := by
    simp [stdP, lowerProd, show Odd 3 by decide]
  rw [pMassOdd, hdiag, hc, hstd]
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt (by positivity)
  rw [hsq]
  have he : (oddSpecies p ⟨2, s⟩).sign.toInt = 1 ∨ (oddSpecies p ⟨2, s⟩).sign.toInt = -1 := by
    cases (oddSpecies p ⟨2, s⟩).sign <;> simp [Sign.toInt]
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (p : ℝ) + 1 ≠ 0 := by linarith
  have h3 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  rcases he with he | he <;> rw [he] <;> push_cast
  · rw [show (1 : ℝ) - 1 * (p : ℝ)⁻¹ = (p - 1) / p by field_simp,
      show (1 : ℝ) - ((p : ℝ) ^ 2)⁻¹ = (p ^ 2 - 1) / p ^ 2 by field_simp]
    field_simp
    ring
  · rw [show (1 : ℝ) - -1 * (p : ℝ)⁻¹ = (p + 1) / p by field_simp; ring,
      show (1 : ℝ) - ((p : ℝ) ^ 2)⁻¹ = (p ^ 2 - 1) / p ^ 2 by field_simp]
    field_simp
    ring

/-- The sign of $\alpha$ in $\mathbb Q_p$: $+$ iff $\alpha$ is a square. -/
noncomputable def sqSign {p : ℕ} [Fact p.Prime] (α : ℤ) : Sign := by
  classical
  exact if IsSquare (α : ℚ_[p]) then .plus else .minus

lemma oddSpecies_sign_toInt {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {α : ℤ} (hα : ¬ (p : ℤ) ∣ α) :
    (oddSpecies p ⟨2, sqSign (p := p) α⟩).sign.toInt = legendreSym p (-α) := by
  classical
  have hsq := isSquare_intCast_padic_iff (p := p) hp2 hα
  rw [← jacobiSym.legendreSym.to_jacobiSym] at hsq
  have hne : legendreSym p α ≠ 0 := by
    rw [Ne, legendreSym.eq_zero_iff]
    intro h
    apply hα
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd α p).1 h
  have hpm : legendreSym p α = 1 ∨ legendreSym p α = -1 := by
    rcases legendreSym.eq_one_or_neg_one p (a := α) (by
      intro h; exact hne ((legendreSym.eq_zero_iff p α).2 h)) with h | h <;> simp [h]
  have hneg : legendreSym p (-α) = ZMod.χ₄ p * legendreSym p α := by
    rw [show -α = -1 * α by ring, legendreSym.mul, legendreSym.at_neg_one hp2]
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by
    have := (Fact.out : p.Prime).eq_one_or_self_of_dvd 2
    rcases Nat.Prime.eq_two_or_odd (Fact.out : p.Prime) with h | h
    · exact absurd h hp2
    · omega
  rw [hneg]
  rcases hp4 with h4 | h4
  · rw [ZMod.χ₄_nat_one_mod_four h4]
    rcases hpm with h | h
    · have : IsSquare (α : ℚ_[p]) := hsq.2 h
      simp [oddSpecies, sqSign, this, h, h4, Sign.toInt, show ¬ Odd 2 by decide]
    · have : ¬ IsSquare (α : ℚ_[p]) := fun h' => by rw [hsq.1 h'] at h; norm_num at h
      simp [oddSpecies, sqSign, this, h, h4, Sign.toInt, show ¬ Odd 2 by decide]
  · rw [ZMod.χ₄_nat_three_mod_four h4]
    rcases hpm with h | h
    · have : IsSquare (α : ℚ_[p]) := hsq.2 h
      simp [oddSpecies, sqSign, this, h, h4, Sign.toInt, Sign.flip, show ¬ Odd 2 by decide]
    · have : ¬ IsSquare (α : ℚ_[p]) := fun h' => by rw [hsq.1 h'] at h; norm_num at h
      simp [oddSpecies, sqSign, this, h, h4, Sign.toInt, Sign.flip, show ¬ Odd 2 by decide]

lemma isOddSymbolOf_sGram {S : ℕ} {B : BinQF} (hd : B.disc = -8 * S) {p : ℕ} [Fact p.Prime]
    {α : ℤ} (hα : ¬ (p : ℤ) ∣ α)
    (h : IsometricGL ((sForm S B).map (Int.castRingHom ℤ_[p]))
      ((QuadForm.diag ![α, α * p, (p : ℤ)]).map (Int.castRingHom ℤ_[p]))) :
    IsOddSymbolOf p ((sGram S B).map (Int.cast : ℤ → ℚ_[p])) (oddSym (sqSign (p := p) α)) := by
  classical
  have h1 := zpEquiv_of_isometricGL hd _ h
  have hn : ‖(α : ℚ_[p])‖ = 1 :=
    le_antisymm (Padic.norm_int_le_one α) (not_lt.1 fun h' => hα (Padic.norm_intCast_lt_one_iff.1 h'))
  refine ⟨![0, 1, 1], ![(α : ℚ_[p]), (α : ℚ_[p]), 1], ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [hn]
  · have : (Matrix.diagonal fun i => ((![α, α * p, (p : ℤ)] i : ℤ) : ℚ_[p])) =
        Matrix.diagonal fun i => (p : ℚ_[p]) ^ (![0, 1, 1] i) * ![(α : ℚ_[p]), (α : ℚ_[p]), 1] i := by
      congr 1; funext i; fin_cases i <;> simp; ring
    rw [← this]; exact h1
  · have h0 : ∏ i : {i : Fin 3 // (![0, 1, 1] : Fin 3 → ℕ) i = 0}, ![(α : ℚ_[p]), (α : ℚ_[p]), 1] i.1 = α := by
      rw [← Finset.prod_subtype ({0} : Finset (Fin 3)) (fun x => by fin_cases x <;> simp)]
      simp
    have h1' : ∏ i : {i : Fin 3 // (![0, 1, 1] : Fin 3 → ℕ) i = 1}, ![(α : ℚ_[p]), (α : ℚ_[p]), 1] i.1 = α := by
      rw [← Finset.prod_subtype ({1, 2} : Finset (Fin 3)) (fun x => by fin_cases x <;> simp)]
      simp
    funext k
    simp only [oddSym, oddSymbolOfDiag]
    rcases k with _ | _ | k
    · rw [h0]
      simp only [if_pos rfl, ite_true, sqSign]
      congr 1
    · rw [h1']
      simp only [show (0 + 1 : ℕ) ≠ 0 by omega, ite_false, if_pos rfl, ite_true, sqSign]
      congr 1
    · simp only [show k + 1 + 1 ≠ 0 by omega, show k + 1 + 1 ≠ 1 by omega, ite_false, OddFactor.trivial,
        OddFactor.mk.injEq]
      have hc : Fintype.card {i : Fin 3 // (![0, 1, 1] : Fin 3 → ℕ) i = k + 1 + 1} = 0 := by
        rw [Fintype.card_eq_zero_iff]
        constructor
        rintro ⟨i, hi⟩
        fin_cases i <;> simp at hi <;> omega
      have hp : (∏ i : {i : Fin 3 // (![0, 1, 1] : Fin 3 → ℕ) i = k + 1 + 1},
          ![(α : ℚ_[p]), (α : ℚ_[p]), 1] i.1) = 1 := by
        have : IsEmpty {i : Fin 3 // (![0, 1, 1] : Fin 3 → ℕ) i = k + 1 + 1} := Fintype.card_eq_zero_iff.1 hc
        exact Finset.prod_of_isEmpty _
      rw [hc, hp, if_pos IsSquare.one]
      simp

/-! ### Lemma 5.1 -/

lemma blockSymbol_twoBlocks_supported (v : ℤ) : (blockSymbol (twoBlocks v)).SupportedBelow 2 := by
  intro k hk
  have hk' : (k : ℤ) ≠ 0 ∧ (k : ℤ) ≠ 1 := by omega
  have hf : List.filter (fun b => decide (blockExp b = (k : ℤ))) (twoBlocks v) = [] := by
    simp [twoBlocks, blockExp, Ne.symm hk'.1, Ne.symm hk'.2]
  unfold blockSymbol
  simp only [hf]
  rfl

lemma primeFactors_eight_mul {S : ℕ} (hSodd : Odd S) :
    (2 * (4 * (S : ℤ) ^ 2)).natAbs.primeFactors = insert 2 S.primeFactors := by
  have hS0 : S ≠ 0 := by rintro rfl; exact absurd hSodd (by decide)
  have : (2 * (4 * (S : ℤ) ^ 2)).natAbs = 2 ^ 3 * S ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow]; simp; ring
  rw [this, Nat.primeFactors_mul (by norm_num) (pow_ne_zero _ hS0),
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two, Nat.primeFactors_pow _ (by norm_num)]
  rfl

/-- **Lemma 5.1** (the masses of the genera of the S-genus), **proved** from the local structure of
Lemma 3.1 (the fields `local_odd`, `local_two` of `SGenusStructure`): for $S$ odd and every sign vector
$\sigma$, $\mathrm{Mass}(B_\sigma(x,y) + 2Sz^2) = \frac1{16}\prod_{p \mid S}\frac{p+\varepsilon_p}{2}$.

The source's proof: the Conway–Sloane mass formula. Here: `mass_eq_stdMass_mul_symbols_unconditional`
(the library's unconditional Conway–Sloane formula) with the standard mass $\mathrm{std}(f) = \frac16$
in dimension 3, the 2-adic symbol of $u x^2 + 2u y^2 + 2z^2$ (2-mass $\frac14 = \frac38\mathrm{std}_2$,
`pMassTwo_twoBlocks`) and the $p$-adic symbols $1^{\pm1}p^{\pm2}$ of $\alpha x^2 + \alpha p y^2 + pz^2$
($p$-mass ratio $\frac{p+\varepsilon_p}2$, `pMassOdd_oddSym_ratio`, with the species sign
$\left(\frac{-\alpha}p\right) = \varepsilon_p$, `oddSpecies_sign_toInt`). -/
@[kb "berkovich2012" "§5, Lemma 5.1, p. 6"]
theorem lemma_5_1 {S : ℕ} (hSodd : Odd S) {B : Signs S → BinQF} (hS : SGenusStructure S B) :
    SGenusMass S B := by
  classical
  refine ⟨fun σ => ?_⟩
  have hd := hS.disc σ
  have hSpos : 0 < S := hSodd.pos
  have hpd : IntQF.PosDef (ofMatrixZ (sGram S (B σ))) := by
    rw [← sForm_eq_ofMatrixZ hd]; exact sForm_posDef hSpos (hS.posDef σ)
  obtain ⟨u, hu, h2⟩ := hS.local_two σ
  obtain ⟨v, hv, hτ⟩ := isTwoSymbolOf_sGram hd hu h2
  choose α hα using fun p (h : p ∈ S.primeFactors) => hS.local_odd σ ⟨p, h⟩
  let σf : ℕ → OddSymbol := fun p => if h : p ∈ S.primeFactors then
    oddSym (@sqSign p ⟨Nat.prime_of_mem_primeFactors h⟩ (α p h)) else fun _ => OddFactor.trivial
  have hodd : ∀ p : ℕ, (hp : p.Prime) → p ≠ 2 → (p : ℤ) ∣ (sGram S (B σ)).det →
      haveI : Fact p.Prime := ⟨hp⟩
      IsOddSymbolOf p ((sGram S (B σ)).map (Int.cast : ℤ → ℚ_[p])) (σf p) ∧
        ∀ k, 2 ≤ k → σf p k = OddFactor.trivial := by
    intro p hp hp2 hdvd
    haveI : Fact p.Prime := ⟨hp⟩
    have hmem : p ∈ S.primeFactors := by
      rw [sGram_det hd] at hdvd
      have h1 : p ∣ 4 * S ^ 2 := by exact_mod_cast hdvd
      have h2' : p ∣ S ^ 2 := by
        rcases (Nat.Prime.dvd_mul hp).1 h1 with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
            (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h))) hp2
        · exact h
      exact Nat.mem_primeFactors.2 ⟨hp, hp.dvd_of_dvd_pow h2', hSpos.ne'⟩
    simp only [σf, dif_pos hmem]
    refine ⟨isOddSymbolOf_sGram hd (hα p hmem).1 (hα p hmem).2.2, fun k hk => ?_⟩
    simp [oddSym, show k ≠ 0 by omega, show k ≠ 1 by omega]
  rw [sForm_eq_ofMatrixZ hd, mass_eq_stdMass_mul_symbols_unconditional (by norm_num) (sGram_transpose S _) hpd
    (blockSymbol (twoBlocks v)) 2 hτ (blockSymbol_twoBlocks_supported v) σf (fun _ => 2) hodd,
    sGram_det hd, primeFactors_eight_mul hSodd, Finset.prod_insert (fun h => by
      have := Nat.dvd_of_mem_primeFactors h
      exact absurd (hSodd.of_dvd_nat this) (by decide)), if_pos rfl, pMassTwo_twoBlocks v hv,
    stdMass_table_3]
  have hstd2 : (stdP 2 3 (4 * (S : ℤ) ^ 2) : ℝ) = 2 / 3 := by
    simp [stdP, lowerProd, show Odd 3 by decide]; norm_num
  rw [hstd2, ← Finset.prod_attach]
  have hprod : ∏ x ∈ S.primeFactors.attach,
      (if (x : ℕ) = 2 then (1 / 4 : ℝ) else pMassOdd x (σf x) 2) /
        (stdP x 3 (4 * (S : ℤ) ^ 2) : ℝ) =
      ∏ p : {p // p ∈ S.primeFactors}, ((p : ℝ) + sgnB (σ p)) / 2 := by
    rw [← Finset.univ_eq_attach]
    refine Finset.prod_congr rfl fun x _ => ?_
    have hx2 : (x : ℕ) ≠ 2 := fun h => by
      have := Nat.dvd_of_mem_primeFactors x.2
      rw [h] at this
      exact absurd (hSodd.of_dvd_nat this) (by decide)
    haveI : Fact (x : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors x.2⟩
    rw [if_neg hx2]
    simp only [σf, dif_pos x.2]
    rw [pMassOdd_oddSym_ratio _ hx2, oddSpecies_sign_toInt hx2 (hα x x.2).1, (hα x x.2).2.1]
  rw [hprod]
  ring

end QuadFormsKB.Berkovich2012
