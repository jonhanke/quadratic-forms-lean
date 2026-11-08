/-
# O'Meara §106F, toward 106.r38: automorphism groups and the completeness criterion

**Proves** (all unconditional)
* `card_aut_e8`: $|\mathrm{Aut}(E_8)| = 696729600$ for the form with Gram matrix the $E_8$ Cartan matrix. The proof is
  by the mass: the genus of $I_9$ consists of the classes of $I_9$ and $E_8 \perp I_1$
  (`intEquiv_of_sameGenus_sumSq_nine`, from O'Meara 106:13), its mass is $\tfrac{17}{2786918400}$
  (`mass_sumSq_nine`), and $|\mathrm{Aut}(I_9)| = 2^9\cdot 9!$, so $|\mathrm{Aut}(E_8 \perp I_1)| = 1393459200$ and
  $|\mathrm{Aut}(E_8)| = 1393459200/2$ (`card_aut_sumI`).
* `card_aut_d12_le`: $|\mathrm{Aut}(E_{12})| \le 2^{11}\cdot 12!$ for the form `ofMatrixZ d12Gram` (from
  `card_autLat_omearaE_twelve_le` through `card_aut_le_card_autLat`).
* `exists_intEquiv_of_mass_le`: the completeness criterion with lower bounds $b_i \le 1/|\mathrm{Aut}(R_i)|$ whose sum is at
  least the mass.

Indices are 0-based.
-/
import QuadFormsKB.Literature.OMeara.Sec106Rank13Classes
import QuadFormsKB.Literature.OMeara.Sec106Rank13Mass

open Matrix NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

open Siegel LocalDensity ConwaySloane.Mass

variable {n : ℕ}

/-- The Gram identity for the basis of $E_m$. -/
theorem EBasisData.gram_gl {m : ℕ} (D : EBasisData m) (x : Fin m → ℚ) :
    (sumSq m).evalIn ℚ (D.gl.val *ᵥ x) = (ofMatrixZ D.G).evalIn ℚ x := by
  rw [evalIn_sumSq, Cassels.Thm71Coords.evalIn_ofMatrixZ _ D.G_symm]
  have h := D.gl_norm x
  rw [D.gl_val]
  simp only [dotProduct, sq] at h ⊢
  rw [h]
  rfl

/-- $E_8 \perp I_1$ is odd. -/
theorem gramType_e8_one : gramType (sumI e8Data.G 1) = 1 :=
  gramType_eq_one_of_odd (Fin.natAdd 8 0) ⟨0, by rw [sumI_apply]; simp⟩

theorem sameGenus_e8_one : Siegel.SameGenus (sumSq 9) (ofMatrixZ (sumI e8Data.G 1)) :=
  sameGenus_sumSq_of_det_one (n := 9) (by norm_num) (e8Data.posDefGram_sumI 1)
    (e8Data.det_sumI (by norm_num) le_rfl 1) gramType_e8_one

/-- **$|\mathrm{Aut}(E_8 \perp I_1)| = 1393459200$**, from the mass of the genus of $I_9$. -/
theorem card_aut_e8_one : Nat.card (Aut (ofMatrixZ (sumI e8Data.G 1))) = 1393459200 := by
  let R : Fin 2 → QuadForm ℤ 9 := ![sumSq 9, ofMatrixZ (sumI e8Data.G 1)]
  have hA := e8Data.posDefGram_G
  have h1 := e8Data.no_norm_one (by norm_num) le_rfl
  have hne : ¬ IntEquiv (sumSq 9) (ofMatrixZ (sumI e8Data.G 1)) :=
    not_intEquiv_sumSq_sumI (m := 8) (k := 1) hA h1 (by norm_num)
  have hm := mass_eq_sum_of_cover posDef_sumSq R
    (fun i => by fin_cases i; exacts [Siegel.SameGenus.refl _, sameGenus_e8_one])
    (fun i j h => by
      fin_cases i <;> fin_cases j
      · rfl
      · exact absurd h hne
      · exact absurd (IsometricGL.symm h) hne
      · rfl)
    (fun Q' hQ' => by
      rcases intEquiv_of_sameGenus_sumSq_nine hQ' with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩)
  rw [mass_sumSq_nine, Fin.sum_univ_two] at hm
  simp only [R, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, card_aut_sumSq] at hm
  have hpos : (0 : ℝ) < Nat.card (Aut (ofMatrixZ (sumI e8Data.G 1))) := by
    exact_mod_cast IntQF.PosDef.card_aut_pos (e8Data.posDefGram_sumI 1).intPosDef
  have : (Nat.card (Aut (ofMatrixZ (sumI e8Data.G 1))) : ℝ) = 1393459200 := by
    have h2 : ((Nat.card (Aut (ofMatrixZ (sumI e8Data.G 1))) : ℝ))⁻¹ = 1 / 1393459200 := by
      norm_num [Nat.factorial] at hm ⊢; linarith
    have := inv_inj.mp (h2.trans (one_div _))
    exact this
  exact_mod_cast this

/-- **$|\mathrm{Aut}(E_8)| = 696729600$** ($= |W(E_8)|$), for the form with Gram matrix the $E_8$ Cartan matrix. -/
@[kb "omeara1963" "§106F, p. 335 (|O(E₈)| = 696729600, from the mass of the genus of I₉)"]
theorem card_aut_e8 : Nat.card (Aut (ofMatrixZ e8Data.G)) = 696729600 := by
  have h := card_aut_sumI e8Data.posDefGram_G (e8Data.no_norm_one (by norm_num) le_rfl) 1
  rw [card_aut_e8_one] at h
  norm_num at h
  omega

/-- **$|\mathrm{Aut}(E_{12})| \le 2^{11}\cdot 12!$** for the form with Gram matrix `d12Gram`. -/
theorem card_aut_d12_le : Nat.card (Aut (ofMatrixZ e12Data.G)) ≤ 2 ^ 11 * Nat.factorial 12 := by
  refine (card_aut_le_card_autLat e12Data.posDefGram_G.intPosDef e12Data.gl e12Data.gram_gl).trans ?_
  rw [e12Data.glImage_gl (by norm_num) (by norm_num)]
  exact card_autLat_omearaE_twelve_le

/-- **The completeness criterion with lower bounds.** If the $R_i$ are pairwise inequivalent forms in the genus of $Q$,
$b_i \le 1/|\mathrm{Aut}(R_i)|$ and $\mathrm{Mass}(Q) \le \sum_i b_i$, then every form of the genus is equivalent to
some $R_i$. -/
theorem exists_intEquiv_of_mass_le {ι : Type*} [Fintype ι] {Q : IntQF n} (hQ : Q.PosDef) (R : ι → QuadForm ℤ n)
    (hgen : ∀ i, Siegel.SameGenus Q (R i)) (hdist : ∀ i j, IntEquiv (R i) (R j) → i = j) (b : ι → ℝ)
    (hb : ∀ i, b i ≤ ((Nat.card (Aut (R i)) : ℝ))⁻¹) (hm : Siegel.mass Q ≤ ∑ i, b i)
    {Q' : QuadForm ℤ n} (h : Siegel.SameGenus Q Q') : ∃ i, IntEquiv (R i) Q' := by
  refine Kneser.exists_intEquiv_of_sum_eq_mass hQ R hgen hdist ?_ h
  exact le_antisymm (Kneser.sum_inv_card_aut_le_mass hQ R hgen hdist)
    (hm.trans (Finset.sum_le_sum fun i _ => hb i))

end QuadFormsKB.Lattices
