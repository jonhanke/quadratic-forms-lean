/-
# O'Meara §106F, 106.r38: the unimodular lattices on $I_n$, $n \le 13$ (Kneser), proved

O'Meara 1973, §106F, p. 335, the remark after 106:13 (Kneser 1957): for $1 \le n \le 13$ every unimodular lattice on
$V = I_n$ over $\mathbb Q$ is properly isometric to $\mathbb Z^n$ ($I_n$), to $E_8 \perp \mathbb Z^{n-8}$ ($\Phi_8 \perp I_{n-8}$,
$n \ge 8$) or to $E_{12} \perp \mathbb Z^{n-12}$ ($\Phi_{12} \perp I_{n-12}$, $n \ge 12$), and these are pairwise not
isometric. The named statement `OMeara106_r38` (`Sec106Rank9.lean`) is now a theorem: `omeara106_r38`.

*Proof (not in the book, which cites Kneser).* For $n \le 9$ this is 106:13 (`omeara106_13`). For $10 \le n \le 13$:
a unimodular lattice $L$ on $I_n$ ($8 \nmid n$, so $L$ is odd) has a basis whose Gram form lies in the genus of $I_n$
(`exists_basis_sameGenus`, via Conway–Sloane 1988 §11 Lemma 2). The mass of that genus is computed from the Conway–Sloane
mass formula (`mass_sumSq_ten`, …), and it equals
$$\frac1{2^n n!} + \frac1{|W(E_8)|\,2^{n-8}(n-8)!} \;\Big[+ \frac1{2^{11}12!\,2^{n-12}(n-12)!}\Big],$$
the sum of the weights of the listed forms; $|W(E_8)| = 696729600$ is itself obtained from the mass for $n = 9$
(`card_aut_e8`), and $|O(E_{12})| \le 2^{11}12!$ is proved directly (`card_autLat_omearaE_twelve_le`). So the listed
forms exhaust the genus (`exists_intEquiv_of_mass_le`), and the Gram-form equivalence gives an isometry of lattices
(`isIsometric_glImage_of_intEquiv`), which is made proper with the transposition of $x_0, x_1$ (an improper automorphism
of each listed lattice). Distinctness: the numbers of vectors of norm $1$ are $2n$, $2(n-8)$, $2(n-12)$.

All unconditional. Indices are 0-based.
-/
import QuadFormsKB.Literature.OMeara.Sec106Rank13Aut
import QuadFormsKB.Literature.OMeara.Sec106Rank13Swap
import QuadFormsKB.Literature.Cassels.Ch11ClassesSpinorGenera530

open Matrix NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

open Siegel LocalDensity ConwaySloane.Mass

theorem inv_card_le_of_card_le {α : Type*} [Finite α] [Nonempty α] {B : ℕ} (h : Nat.card α ≤ B) :
    ((B : ℝ))⁻¹ ≤ ((Nat.card α : ℝ))⁻¹ := by
  have hpos : (0 : ℝ) < Nat.card α := by exact_mod_cast Nat.card_pos
  exact inv_anti₀ hpos (by exact_mod_cast h)

theorem card_aut_e8_sumI (k : ℕ) :
    Nat.card (Aut (ofMatrixZ (sumI e8Data.G k))) = 2 ^ k * k.factorial * 696729600 := by
  rw [card_aut_sumI e8Data.posDefGram_G (e8Data.no_norm_one (by norm_num) le_rfl) k, card_aut_e8]

theorem card_aut_d12_sumI_le (k : ℕ) :
    Nat.card (Aut (ofMatrixZ (sumI e12Data.G k))) ≤ 2 ^ k * k.factorial * (2 ^ 11 * Nat.factorial 12) := by
  rw [card_aut_sumI e12Data.posDefGram_G (e12Data.no_norm_one (by norm_num) (by norm_num)) k]
  exact Nat.mul_le_mul_left _ card_aut_d12_le

theorem repNum_e8_sumI (k : ℕ) : repNum (ofMatrixZ (sumI e8Data.G k)) 1 = 2 * k :=
  repNum_sumI_one e8Data.posDefGram_G (e8Data.no_norm_one (by norm_num) le_rfl) k

theorem repNum_d12_sumI (k : ℕ) : repNum (ofMatrixZ (sumI e12Data.G k)) 1 = 2 * k :=
  repNum_sumI_one e12Data.posDefGram_G (e12Data.no_norm_one (by norm_num) (by norm_num)) k

theorem posDef_aut_finite {n : ℕ} {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) : Finite (Aut Q) := IntQF.PosDef.finite_aut hQ

/-- The identity basis: $\mathbb Z^n$ with Gram form $I_n$. -/
theorem gram_one (n : ℕ) (x : Fin n → ℚ) : (sumSq n).evalIn ℚ ((1 : GL (Fin n) ℚ).val *ᵥ x) = (sumSq n).evalIn ℚ x := by
  simp


/-- **The genus of $I_{10}$** consists of the classes of the listed forms. -/
theorem cover_ten {Q' : QuadForm ℤ 10} (h : Siegel.SameGenus (sumSq 10) Q') :
    IntEquiv (sumSq 10) Q' ∨ IntEquiv (ofMatrixZ (sumI e8Data.G 2)) Q' := by
  let R : Fin 2 → QuadForm ℤ 10 := ![sumSq 10, ofMatrixZ (sumI e8Data.G 2)]
  have hge8 : Siegel.SameGenus (sumSq 10) (ofMatrixZ (sumI e8Data.G 2)) :=
    sameGenus_sumSq_of_det_one (n := 10) (by norm_num) (e8Data.posDefGram_sumI 2)
      (e8Data.det_sumI (by norm_num) le_rfl 2) (gramType_eq_one_of_odd ⟨8, by norm_num⟩ ⟨0, by rw [sumI_apply]; simp⟩)
  have hne1 : ¬ IntEquiv (sumSq 10) (ofMatrixZ (sumI e8Data.G 2)) := fun h => by
    have := repNum_eq_of_intEquiv h 1
    rw [repNum_sumSq_one, repNum_e8_sumI] at this; omega
  obtain ⟨i, hi⟩ := exists_intEquiv_of_mass_le posDef_sumSq R (fun i => by fin_cases i; exacts [Siegel.SameGenus.refl _, hge8])
    (fun i j h => by
      fin_cases i <;> fin_cases j
      all_goals first
        | rfl
        | exact absurd h hne1 | exact absurd (IsometricGL.symm h) hne1)
    (![(((2 : ℕ) ^ 10 * Nat.factorial 10 : ℕ) : ℝ)⁻¹, (((2 : ℕ) ^ 2 * Nat.factorial 2 * 696729600 : ℕ) : ℝ)⁻¹])
    (fun i => by
      fin_cases i
      · show (((2 : ℕ) ^ 10 * Nat.factorial 10 : ℕ) : ℝ)⁻¹ ≤ ((Nat.card (Aut (sumSq 10)) : ℝ))⁻¹
        rw [card_aut_sumSq]
      · show (((2 : ℕ) ^ 2 * Nat.factorial 2 * 696729600 : ℕ) : ℝ)⁻¹ ≤
          ((Nat.card (Aut (ofMatrixZ (sumI e8Data.G 2))) : ℝ))⁻¹
        rw [card_aut_e8_sumI])
    (by rw [mass_sumSq_ten]; simp [Fin.sum_univ_succ, Nat.factorial]; norm_num) h
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr hi

/-- **106.r38 for $n = 10$**: every unimodular lattice on $I_{10}$ is properly isometric to one of the listed lattices. -/
theorem covers_ten (L : Lat ℚ 10) (hL : IsUnimodularZ (sumSqForm 10) L.1) :
    IsProperIsometric (sumSqForm 10) intVec L.1 ∨ IsProperIsometric (sumSqForm 10) (omearaEZ 10) L.1 := by
  obtain ⟨γ, G, hLγ, hgram, hgen⟩ := exists_basis_sameGenus (by norm_num) (by norm_num) L hL
  rw [hLγ]
  rcases cover_ten hgen with h | h
  · left
    have hi := isIsometric_glImage_of_intEquiv 1 γ (gram_one 10) hgram h
    rw [glImage_one] at hi
    exact isProperIsometric_of_isIsometric_swap (by norm_num) (intVec_swap _) hi
  · right
    have hi := isIsometric_glImage_of_intEquiv (e8Data.blk 2) γ (e8Data.gram_blk 2) hgram h
    rw [e8Data.glImage_blk (by norm_num) (by norm_num) 2] at hi
    exact isProperIsometric_of_isIsometric_swap (by norm_num)
      (omearaEPerp_swap (m := 8) (n := 10) (by norm_num) le_rfl (by norm_num)) hi

/-- **The genus of $I_{11}$** consists of the classes of the listed forms. -/
theorem cover_eleven {Q' : QuadForm ℤ 11} (h : Siegel.SameGenus (sumSq 11) Q') :
    IntEquiv (sumSq 11) Q' ∨ IntEquiv (ofMatrixZ (sumI e8Data.G 3)) Q' := by
  let R : Fin 2 → QuadForm ℤ 11 := ![sumSq 11, ofMatrixZ (sumI e8Data.G 3)]
  have hge8 : Siegel.SameGenus (sumSq 11) (ofMatrixZ (sumI e8Data.G 3)) :=
    sameGenus_sumSq_of_det_one (n := 11) (by norm_num) (e8Data.posDefGram_sumI 3)
      (e8Data.det_sumI (by norm_num) le_rfl 3) (gramType_eq_one_of_odd ⟨8, by norm_num⟩ ⟨0, by rw [sumI_apply]; simp⟩)
  have hne1 : ¬ IntEquiv (sumSq 11) (ofMatrixZ (sumI e8Data.G 3)) := fun h => by
    have := repNum_eq_of_intEquiv h 1
    rw [repNum_sumSq_one, repNum_e8_sumI] at this; omega
  obtain ⟨i, hi⟩ := exists_intEquiv_of_mass_le posDef_sumSq R (fun i => by fin_cases i; exacts [Siegel.SameGenus.refl _, hge8])
    (fun i j h => by
      fin_cases i <;> fin_cases j
      all_goals first
        | rfl
        | exact absurd h hne1 | exact absurd (IsometricGL.symm h) hne1)
    (![(((2 : ℕ) ^ 11 * Nat.factorial 11 : ℕ) : ℝ)⁻¹, (((2 : ℕ) ^ 3 * Nat.factorial 3 * 696729600 : ℕ) : ℝ)⁻¹])
    (fun i => by
      fin_cases i
      · show (((2 : ℕ) ^ 11 * Nat.factorial 11 : ℕ) : ℝ)⁻¹ ≤ ((Nat.card (Aut (sumSq 11)) : ℝ))⁻¹
        rw [card_aut_sumSq]
      · show (((2 : ℕ) ^ 3 * Nat.factorial 3 * 696729600 : ℕ) : ℝ)⁻¹ ≤
          ((Nat.card (Aut (ofMatrixZ (sumI e8Data.G 3))) : ℝ))⁻¹
        rw [card_aut_e8_sumI])
    (by rw [mass_sumSq_eleven]; simp [Fin.sum_univ_succ, Nat.factorial]; norm_num) h
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr hi

/-- **106.r38 for $n = 11$**: every unimodular lattice on $I_{11}$ is properly isometric to one of the listed lattices. -/
theorem covers_eleven (L : Lat ℚ 11) (hL : IsUnimodularZ (sumSqForm 11) L.1) :
    IsProperIsometric (sumSqForm 11) intVec L.1 ∨ IsProperIsometric (sumSqForm 11) (omearaEZ 11) L.1 := by
  obtain ⟨γ, G, hLγ, hgram, hgen⟩ := exists_basis_sameGenus (by norm_num) (by norm_num) L hL
  rw [hLγ]
  rcases cover_eleven hgen with h | h
  · left
    have hi := isIsometric_glImage_of_intEquiv 1 γ (gram_one 11) hgram h
    rw [glImage_one] at hi
    exact isProperIsometric_of_isIsometric_swap (by norm_num) (intVec_swap _) hi
  · right
    have hi := isIsometric_glImage_of_intEquiv (e8Data.blk 3) γ (e8Data.gram_blk 3) hgram h
    rw [e8Data.glImage_blk (by norm_num) (by norm_num) 3] at hi
    exact isProperIsometric_of_isIsometric_swap (by norm_num)
      (omearaEPerp_swap (m := 8) (n := 11) (by norm_num) le_rfl (by norm_num)) hi

/-- **The genus of $I_{12}$** consists of the classes of the listed forms. -/
theorem cover_twelve {Q' : QuadForm ℤ 12} (h : Siegel.SameGenus (sumSq 12) Q') :
    IntEquiv (sumSq 12) Q' ∨ IntEquiv (ofMatrixZ (sumI e8Data.G 4)) Q' ∨ IntEquiv (ofMatrixZ (sumI e12Data.G 0)) Q' := by
  let R : Fin 3 → QuadForm ℤ 12 := ![sumSq 12, ofMatrixZ (sumI e8Data.G 4), ofMatrixZ (sumI e12Data.G 0)]
  have hge8 : Siegel.SameGenus (sumSq 12) (ofMatrixZ (sumI e8Data.G 4)) :=
    sameGenus_sumSq_of_det_one (n := 12) (by norm_num) (e8Data.posDefGram_sumI 4)
      (e8Data.det_sumI (by norm_num) le_rfl 4) (gramType_eq_one_of_odd ⟨8, by norm_num⟩ ⟨0, by rw [sumI_apply]; simp⟩)
  have hgd12 : Siegel.SameGenus (sumSq 12) (ofMatrixZ (sumI e12Data.G 0)) :=
    sameGenus_sumSq_of_det_one (n := 12) (by norm_num) (e12Data.posDefGram_sumI 0)
      (e12Data.det_sumI (by norm_num) (by norm_num) 0) (gramType_eq_one_of_odd ⟨0, by norm_num⟩ ⟨1, by rw [sumI_apply]; simp [e12Data, d12Gram]⟩)
  have hne1 : ¬ IntEquiv (sumSq 12) (ofMatrixZ (sumI e8Data.G 4)) := fun h => by
    have := repNum_eq_of_intEquiv h 1
    rw [repNum_sumSq_one, repNum_e8_sumI] at this; omega
  have hne2 : ¬ IntEquiv (sumSq 12) (ofMatrixZ (sumI e12Data.G 0)) := fun h => by
    have := repNum_eq_of_intEquiv h 1
    rw [repNum_sumSq_one, repNum_d12_sumI] at this; omega
  have hne3 : ¬ IntEquiv (ofMatrixZ (sumI e8Data.G 4)) (ofMatrixZ (sumI e12Data.G 0)) := fun h => by
    have := repNum_eq_of_intEquiv h 1
    rw [repNum_e8_sumI, repNum_d12_sumI] at this; omega
  obtain ⟨i, hi⟩ := exists_intEquiv_of_mass_le posDef_sumSq R (fun i => by fin_cases i; exacts [Siegel.SameGenus.refl _, hge8, hgd12])
    (fun i j h => by
      fin_cases i <;> fin_cases j
      all_goals first
        | rfl
        | exact absurd h hne1 | exact absurd (IsometricGL.symm h) hne1
        | exact absurd h hne2 | exact absurd (IsometricGL.symm h) hne2
        | exact absurd h hne3 | exact absurd (IsometricGL.symm h) hne3)
    (![(((2 : ℕ) ^ 12 * Nat.factorial 12 : ℕ) : ℝ)⁻¹, (((2 : ℕ) ^ 4 * Nat.factorial 4 * 696729600 : ℕ) : ℝ)⁻¹, (((2 : ℕ) ^ 0 * Nat.factorial 0 * (2 ^ 11 * Nat.factorial 12) : ℕ) : ℝ)⁻¹])
    (fun i => by
      fin_cases i
      · show (((2 : ℕ) ^ 12 * Nat.factorial 12 : ℕ) : ℝ)⁻¹ ≤ ((Nat.card (Aut (sumSq 12)) : ℝ))⁻¹
        rw [card_aut_sumSq]
      · show (((2 : ℕ) ^ 4 * Nat.factorial 4 * 696729600 : ℕ) : ℝ)⁻¹ ≤
          ((Nat.card (Aut (ofMatrixZ (sumI e8Data.G 4))) : ℝ))⁻¹
        rw [card_aut_e8_sumI]
      · show (((2 : ℕ) ^ 0 * Nat.factorial 0 * (2 ^ 11 * Nat.factorial 12) : ℕ) : ℝ)⁻¹ ≤
          ((Nat.card (Aut (ofMatrixZ (sumI e12Data.G 0))) : ℝ))⁻¹
        haveI := posDef_aut_finite (e12Data.posDefGram_sumI 0).intPosDef
        exact inv_card_le_of_card_le (card_aut_d12_sumI_le 0))
    (by rw [mass_sumSq_twelve]; simp [Fin.sum_univ_succ, Nat.factorial]; norm_num) h
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr hi)

/-- **106.r38 for $n = 12$**: every unimodular lattice on $I_{12}$ is properly isometric to one of the listed lattices. -/
theorem covers_twelve (L : Lat ℚ 12) (hL : IsUnimodularZ (sumSqForm 12) L.1) :
    IsProperIsometric (sumSqForm 12) intVec L.1 ∨ IsProperIsometric (sumSqForm 12) (omearaEZ 12) L.1 ∨ IsProperIsometric (sumSqForm 12) (omearaEPerp 12 12) L.1 := by
  obtain ⟨γ, G, hLγ, hgram, hgen⟩ := exists_basis_sameGenus (by norm_num) (by norm_num) L hL
  rw [hLγ]
  rcases cover_twelve hgen with h | h | h
  · left
    have hi := isIsometric_glImage_of_intEquiv 1 γ (gram_one 12) hgram h
    rw [glImage_one] at hi
    exact isProperIsometric_of_isIsometric_swap (by norm_num) (intVec_swap _) hi
  · right; left
    have hi := isIsometric_glImage_of_intEquiv (e8Data.blk 4) γ (e8Data.gram_blk 4) hgram h
    rw [e8Data.glImage_blk (by norm_num) (by norm_num) 4] at hi
    exact isProperIsometric_of_isIsometric_swap (by norm_num)
      (omearaEPerp_swap (m := 8) (n := 12) (by norm_num) le_rfl (by norm_num)) hi
  · right; right
    have hi := isIsometric_glImage_of_intEquiv (e12Data.blk 0) γ (e12Data.gram_blk 0) hgram h
    rw [e12Data.glImage_blk (by norm_num) (by norm_num) 0] at hi
    exact isProperIsometric_of_isIsometric_swap (by norm_num)
      (omearaEPerp_swap (m := 12) (n := 12) (by norm_num) (by norm_num) (by norm_num)) hi

/-- **The genus of $I_{13}$** consists of the classes of the listed forms. -/
theorem cover_thirteen {Q' : QuadForm ℤ 13} (h : Siegel.SameGenus (sumSq 13) Q') :
    IntEquiv (sumSq 13) Q' ∨ IntEquiv (ofMatrixZ (sumI e8Data.G 5)) Q' ∨ IntEquiv (ofMatrixZ (sumI e12Data.G 1)) Q' := by
  let R : Fin 3 → QuadForm ℤ 13 := ![sumSq 13, ofMatrixZ (sumI e8Data.G 5), ofMatrixZ (sumI e12Data.G 1)]
  have hge8 : Siegel.SameGenus (sumSq 13) (ofMatrixZ (sumI e8Data.G 5)) :=
    sameGenus_sumSq_of_det_one (n := 13) (by norm_num) (e8Data.posDefGram_sumI 5)
      (e8Data.det_sumI (by norm_num) le_rfl 5) (gramType_eq_one_of_odd ⟨8, by norm_num⟩ ⟨0, by rw [sumI_apply]; simp⟩)
  have hgd12 : Siegel.SameGenus (sumSq 13) (ofMatrixZ (sumI e12Data.G 1)) :=
    sameGenus_sumSq_of_det_one (n := 13) (by norm_num) (e12Data.posDefGram_sumI 1)
      (e12Data.det_sumI (by norm_num) (by norm_num) 1) (gramType_eq_one_of_odd ⟨0, by norm_num⟩ ⟨1, by rw [sumI_apply]; simp [e12Data, d12Gram]⟩)
  have hne1 : ¬ IntEquiv (sumSq 13) (ofMatrixZ (sumI e8Data.G 5)) := fun h => by
    have := repNum_eq_of_intEquiv h 1
    rw [repNum_sumSq_one, repNum_e8_sumI] at this; omega
  have hne2 : ¬ IntEquiv (sumSq 13) (ofMatrixZ (sumI e12Data.G 1)) := fun h => by
    have := repNum_eq_of_intEquiv h 1
    rw [repNum_sumSq_one, repNum_d12_sumI] at this; omega
  have hne3 : ¬ IntEquiv (ofMatrixZ (sumI e8Data.G 5)) (ofMatrixZ (sumI e12Data.G 1)) := fun h => by
    have := repNum_eq_of_intEquiv h 1
    rw [repNum_e8_sumI, repNum_d12_sumI] at this; omega
  obtain ⟨i, hi⟩ := exists_intEquiv_of_mass_le posDef_sumSq R (fun i => by fin_cases i; exacts [Siegel.SameGenus.refl _, hge8, hgd12])
    (fun i j h => by
      fin_cases i <;> fin_cases j
      all_goals first
        | rfl
        | exact absurd h hne1 | exact absurd (IsometricGL.symm h) hne1
        | exact absurd h hne2 | exact absurd (IsometricGL.symm h) hne2
        | exact absurd h hne3 | exact absurd (IsometricGL.symm h) hne3)
    (![(((2 : ℕ) ^ 13 * Nat.factorial 13 : ℕ) : ℝ)⁻¹, (((2 : ℕ) ^ 5 * Nat.factorial 5 * 696729600 : ℕ) : ℝ)⁻¹, (((2 : ℕ) ^ 1 * Nat.factorial 1 * (2 ^ 11 * Nat.factorial 12) : ℕ) : ℝ)⁻¹])
    (fun i => by
      fin_cases i
      · show (((2 : ℕ) ^ 13 * Nat.factorial 13 : ℕ) : ℝ)⁻¹ ≤ ((Nat.card (Aut (sumSq 13)) : ℝ))⁻¹
        rw [card_aut_sumSq]
      · show (((2 : ℕ) ^ 5 * Nat.factorial 5 * 696729600 : ℕ) : ℝ)⁻¹ ≤
          ((Nat.card (Aut (ofMatrixZ (sumI e8Data.G 5))) : ℝ))⁻¹
        rw [card_aut_e8_sumI]
      · show (((2 : ℕ) ^ 1 * Nat.factorial 1 * (2 ^ 11 * Nat.factorial 12) : ℕ) : ℝ)⁻¹ ≤
          ((Nat.card (Aut (ofMatrixZ (sumI e12Data.G 1))) : ℝ))⁻¹
        haveI := posDef_aut_finite (e12Data.posDefGram_sumI 1).intPosDef
        exact inv_card_le_of_card_le (card_aut_d12_sumI_le 1))
    (by rw [mass_sumSq_thirteen]; simp [Fin.sum_univ_succ, Nat.factorial]; norm_num) h
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr hi)

/-- **106.r38 for $n = 13$**: every unimodular lattice on $I_{13}$ is properly isometric to one of the listed lattices. -/
theorem covers_thirteen (L : Lat ℚ 13) (hL : IsUnimodularZ (sumSqForm 13) L.1) :
    IsProperIsometric (sumSqForm 13) intVec L.1 ∨ IsProperIsometric (sumSqForm 13) (omearaEZ 13) L.1 ∨ IsProperIsometric (sumSqForm 13) (omearaEPerp 12 13) L.1 := by
  obtain ⟨γ, G, hLγ, hgram, hgen⟩ := exists_basis_sameGenus (by norm_num) (by norm_num) L hL
  rw [hLγ]
  rcases cover_thirteen hgen with h | h | h
  · left
    have hi := isIsometric_glImage_of_intEquiv 1 γ (gram_one 13) hgram h
    rw [glImage_one] at hi
    exact isProperIsometric_of_isIsometric_swap (by norm_num) (intVec_swap _) hi
  · right; left
    have hi := isIsometric_glImage_of_intEquiv (e8Data.blk 5) γ (e8Data.gram_blk 5) hgram h
    rw [e8Data.glImage_blk (by norm_num) (by norm_num) 5] at hi
    exact isProperIsometric_of_isIsometric_swap (by norm_num)
      (omearaEPerp_swap (m := 8) (n := 13) (by norm_num) le_rfl (by norm_num)) hi
  · right; right
    have hi := isIsometric_glImage_of_intEquiv (e12Data.blk 1) γ (e12Data.gram_blk 1) hgram h
    rw [e12Data.glImage_blk (by norm_num) (by norm_num) 1] at hi
    exact isProperIsometric_of_isIsometric_swap (by norm_num)
      (omearaEPerp_swap (m := 12) (n := 13) (by norm_num) (by norm_num) (by norm_num)) hi

/-- The listed lattices for $n \in \{12, 13\}$ are pairwise not isometric (numbers of norm-$1$ vectors). -/
theorem distinct_twelve_thirteen {n : ℕ} (hn : n = 12 ∨ n = 13) :
    ¬ IsIsometric (sumSqForm n) intVec (omearaEPerp 12 n) ∧
      ¬ IsIsometric (sumSqForm n) (omearaEZ n) (omearaEPerp 12 n) := by
  rcases hn with rfl | rfl
  · constructor
    · rintro ⟨σ, hσ, he⟩
      have h := intEquiv_of_isIsometric_glImage 1 (e12Data.blk 0) σ (gram_one 12) (e12Data.gram_blk 0) hσ (by
        rw [glImage_one, e12Data.glImage_blk (by norm_num) (by norm_num) 0]; exact he)
      have := repNum_eq_of_intEquiv h 1
      rw [repNum_sumSq_one, repNum_d12_sumI] at this; omega
    · rintro ⟨σ, hσ, he⟩
      have h := intEquiv_of_isIsometric_glImage (e8Data.blk 4) (e12Data.blk 0) σ (e8Data.gram_blk 4)
        (e12Data.gram_blk 0) hσ (by
          rw [e8Data.glImage_blk (by norm_num) (by norm_num) 4, e12Data.glImage_blk (by norm_num) (by norm_num) 0]
          exact he)
      have := repNum_eq_of_intEquiv h 1
      rw [repNum_e8_sumI, repNum_d12_sumI] at this; omega
  · constructor
    · rintro ⟨σ, hσ, he⟩
      have h := intEquiv_of_isIsometric_glImage 1 (e12Data.blk 1) σ (gram_one 13) (e12Data.gram_blk 1) hσ (by
        rw [glImage_one, e12Data.glImage_blk (by norm_num) (by norm_num) 1]; exact he)
      have := repNum_eq_of_intEquiv h 1
      rw [repNum_sumSq_one, repNum_d12_sumI] at this; omega
    · rintro ⟨σ, hσ, he⟩
      have h := intEquiv_of_isIsometric_glImage (e8Data.blk 5) (e12Data.blk 1) σ (e8Data.gram_blk 5)
        (e12Data.gram_blk 1) hσ (by
          rw [e8Data.glImage_blk (by norm_num) (by norm_num) 5, e12Data.glImage_blk (by norm_num) (by norm_num) 1]
          exact he)
      have := repNum_eq_of_intEquiv h 1
      rw [repNum_e8_sumI, repNum_d12_sumI] at this; omega

/-- For $n \le 9$: 106:13 with proper isometries. -/
theorem covers_le_nine {n : ℕ} (h1 : 1 ≤ n) (h9 : n ≤ 9) (L : Lat ℚ n) (hL : IsUnimodularZ (sumSqForm n) L.1) :
    IsProperIsometric (sumSqForm n) intVec L.1 ∨ (8 ≤ n ∧ IsProperIsometric (sumSqForm n) (omearaEZ n) L.1) := by
  have hQ : (sumSqForm n).Nondegenerate := QuadForm.nondegenerate_diag (fun _ => one_ne_zero)
  rcases (omeara106_13 h1 h9 hL).or with h | ⟨h8, h⟩
  · left
    rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | h2
    · exact isProperIsometric_of_isIsometric _ hQ odd_one h
    · exact isProperIsometric_of_isIsometric_swap h2 (intVec_swap h2) h
  · right
    exact ⟨h8, isProperIsometric_of_isIsometric_swap (by omega)
      (omearaEPerp_swap (m := 8) (by norm_num) le_rfl h8) h⟩

/-- **O'Meara 106.r38 (Kneser), proved** (O'Meara 1973, §106F, p. 335, the remark after 106:13, stated there without
proof): for $1 \le n \le 13$ the proper classes of unimodular lattices on $V = I_n$ over $\mathbb Q$ are those of
$\mathbb Z^n$, $E_8 \perp \mathbb Z^{n-8}$ ($n \ge 8$) and $E_{12} \perp \mathbb Z^{n-12}$ ($n \ge 12$), pairwise not
isometric. Unconditional (the proof is described in the module docstring). -/
@[kb "omeara1963" "§106F, 106.r38, p. 335 (Kneser 1957: proper classes for 1 ≤ n ≤ 13; proved by the mass formula)"]
theorem omeara106_r38 : OMeara106_r38 where
  unimodular n := ⟨fun h8 => omearaEZ_unimodular h8, fun h12 => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h12
    exact isUnimodularZ_omearaEPerp (by norm_num) (by norm_num) k⟩
  covers n h1 h13 L hL := by
    rcases (by omega : n ≤ 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13) with h9 | rfl | rfl | rfl | rfl
    · rcases covers_le_nine h1 h9 L hL with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases covers_ten L hL with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨by norm_num, h⟩)
    · rcases covers_eleven L hL with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨by norm_num, h⟩)
    · rcases covers_twelve L hL with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨by norm_num, h⟩)
      · exact Or.inr (Or.inr ⟨by norm_num, h⟩)
    · rcases covers_thirteen L hL with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨by norm_num, h⟩)
      · exact Or.inr (Or.inr ⟨by norm_num, h⟩)
  distinct n h13 := by
    refine ⟨fun h8 => not_isIsometric_intVec_omearaEZ h8, fun h12 => ?_, fun h12 => ?_⟩
    · exact (distinct_twelve_thirteen (by omega)).1
    · exact (distinct_twelve_thirteen (by omega)).2

end QuadFormsKB.Lattices
