/-
# Conway–Sloane 1988, §9 (i): the symbols of $\mathrm{diag}(7,1,1)$

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), §9 (i), p. 269 (bibliography key `conwaysloane1988`).

Certifies that the symbols `ex1Two` ($1^{+3}_1$) and `ex1Seven` ($1^{+2}7^{+1}$) entered in `Examples.lean` are a 2-adic
and the 7-adic symbol of the form $f = \mathrm{diag}(7,1,1)$ in the sense of *Sphere Packings, Lattices and Groups* Ch. 15 (`IsTwoSymbolOf`,
`IsOddSymbolOf`): $f$ is itself a diagonal Jordan decomposition.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.Formula
import QuadFormsKB.Literature.ConwaySloane.Mass.Examples

namespace QuadFormsKB.ConwaySloane.Mass

open Finset

/-- The Gram matrix $\mathrm{diag}(7,1,1)$ of §9 (i). -/
def ex1Gram : Matrix (Fin 3) (Fin 3) ℤ := Matrix.diagonal ![7, 1, 1]

/-- **The 7-adic symbol of $\mathrm{diag}(7,1,1)$ is $1^{+2}7^{+1}$** (Conway–Sloane 1988, §9 (i), p. 269). -/
@[kb "conwaysloane1988" "§9 (i), p. 269 (7-adic decomposition)"]
theorem isOddSymbolOf_ex1 :
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    IsOddSymbolOf 7 (ex1Gram.map (Int.cast : ℤ → ℚ_[7])) ex1Seven := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine ⟨![1, 0, 0], fun _ => 1, fun _ => norm_one, ?_, ?_⟩
  · have : ex1Gram.map (Int.cast : ℤ → ℚ_[7]) =
        Matrix.diagonal fun i => (7 : ℚ_[7]) ^ (![1, 0, 0] i) * (fun _ => (1 : ℚ_[7])) i := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ex1Gram, Matrix.diagonal]
    rw [this]
    exact Cassels.ZpEquiv.refl _
  · have hsq : ∀ k : ℕ, IsSquare (∏ i : {i // (![1, 0, 0] : Fin 3 → ℕ) i = k}, (fun _ => (1 : ℚ_[7])) i) :=
      fun k => ⟨1, by simp⟩
    funext k
    simp only [ex1Seven, oddSymbolOfDiag, hsq, if_true]
    rcases k with _ | _ | k
    · simp only [if_pos rfl, OddFactor.mk.injEq, and_true]
      rw [Fintype.card_subtype]
      decide
    · simp only [show (0 + 1 : ℕ) ≠ 0 by omega, if_false, if_pos rfl, OddFactor.mk.injEq, and_true]
      rw [Fintype.card_subtype]
      decide
    · simp only [show k + 1 + 1 ≠ 0 by omega, show k + 1 + 1 ≠ 1 by omega, if_false, OddFactor.trivial,
        OddFactor.mk.injEq, and_true]
      symm
      rw [Fintype.card_eq_zero_iff]
      constructor
      rintro ⟨i, hi⟩
      fin_cases i <;> simp at hi <;> omega

/-- The block decomposition $\langle7\rangle \perp \langle1\rangle \perp \langle1\rangle$ of $\mathrm{diag}(7,1,1)$
over $\mathbb Z_2$. -/
def ex1Blocks : List Cassels.DyBlock := [.sq 0 7, .sq 0 1, .sq 0 1]

/-- **A 2-adic symbol of $\mathrm{diag}(7,1,1)$ is $1^{+3}_1$** (Conway–Sloane 1988, §9 (i), p. 269: "$f_1 = f$, of
type I, dimension 3 and octane value $-1+1+1 = 1$"). -/
@[kb "conwaysloane1988" "§9 (i), p. 269 (2-adic decomposition)"]
theorem isTwoSymbolOf_ex1 : IsTwoSymbolOf (ex1Gram.map (Int.cast : ℤ → ℚ_[2])) ex1Two := by
  refine ⟨ex1Blocks, ?_, ?_, rfl, ?_, ?_⟩
  · intro b hb
    simp only [ex1Blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp [Cassels.DyBlock.Valid]
  · intro b hb
    simp only [ex1Blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp [blockExp]
  · have : ex1Gram.map (Int.cast : ℤ → ℚ_[2]) =
        (Cassels.dyMat ex1Blocks).submatrix (Fin.cast rfl) (Fin.cast rfl) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [ex1Gram, ex1Blocks, Cassels.dyMat, Cassels.orthSumMat, Cassels.DyBlock.mat, Matrix.diagonal,
          Matrix.fromBlocks, finSumFinEquiv] <;> rfl
    rw [this]
    exact Cassels.ZpEquiv.refl _
  · funext k
    by_cases hk : k = 0
    · subst hk
      simp only [ex1Two, if_true, blockSymbol, ex1Blocks]
      decide
    · have hk' : (k : ℤ) ≠ 0 := by exact_mod_cast hk
      have hf : List.filter (fun b => decide (blockExp b = (k : ℤ))) ex1Blocks = [] := by
        simp [ex1Blocks, blockExp, hk'.symm]
      show (if k = 0 then _ else TwoFactor.trivial) = blockSymbol ex1Blocks k
      rw [if_neg hk]
      unfold blockSymbol
      simp only [hf]
      rfl

end QuadFormsKB.ConwaySloane.Mass
