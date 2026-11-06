/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Dyadic7CountTrans

/-!
# Paper 7 at $p = 2$: evaluation tools for the families of representatives

Helpers used for each family of `Dyadic7.reps` (one family per row of Hanke's Table 5.3):

* `blockSymbol_cons`, `localize_cons`: evaluation of symbols and localized lists of explicit block lists;
* `dimType_eq_of_forget`: lists differing only in the units of their diagonal blocks have the same dimensions and
  types (`forgetUnit`);
* `minSq_eq_filter`, `minBin_eq_filter`: the first-in-class unit triples (pairs) for a computable description of the
  classes;
* `massWt_eq_local`: the mass weight of an admissible list from a window decomposition, with
  `pMassTwo_base` ($m_2(D_0(u)) = 1/6$, $D_0(u) = 2xy \perp 2(-u)z^2$);
* `hasseQ_sqL`, `hasseQ_binL`, `hasseQ_baseList`: Hasse invariants of the two shapes, with exponents modulo 2.

Indices are 0-based.
-/

open Finset

namespace QuadFormsKB.Dyadic7

open QuadFormsKB.ConwaySloane QuadFormsKB.ConwaySloane.Mass Cassels QuadFormsKB.Hanke2011Ternary

/-! ### Evaluating symbols and localized lists -/

/-- The constituent obtained by adding the block `b` to the constituent `f` (of the same scale). -/
def addBlock (b : DyBlock) (f : TwoFactor) : TwoFactor :=
  ⟨b.dim + f.dim, (blockSign b).mul f.sign, if IsSqBlock b then .I else f.type, blockOddity b + f.oddity⟩

theorem blockSymbol_nil (k : ℕ) : blockSymbol [] k = TwoFactor.trivial := by
  simp [blockSymbol, TwoFactor.trivial, Sign.prodList]

theorem blockSymbol_cons (b : DyBlock) (D : List DyBlock) (k : ℕ) :
    blockSymbol (b :: D) k = if blockExp b = k then addBlock b (blockSymbol D k) else blockSymbol D k := by
  by_cases h : blockExp b = k
  · rw [if_pos h]
    simp only [blockSymbol, addBlock, List.filter_cons, h, decide_true, if_true, List.map_cons, List.sum_cons,
      Sign.prodList, List.any_cons]
    congr 1
    by_cases hs : IsSqBlock b <;> simp [hs]
  · rw [if_neg h]
    simp only [blockSymbol, List.filter_cons, h, decide_false]
    rfl

theorem localize_nil (l len : ℕ) : localize [] l len = [] := rfl

theorem localize_cons (b : DyBlock) (D : List DyBlock) (l len : ℕ) :
    localize (b :: D) l len = if (l : ℤ) ≤ blockExp b ∧ blockExp b < (l : ℤ) + len then
      shiftBlock (-(l : ℤ)) b :: localize D l len else localize D l len := by
  unfold localize
  by_cases h : (l : ℤ) ≤ blockExp b ∧ blockExp b < (l : ℤ) + len
  · rw [if_pos h, List.filter_cons_of_pos (by simpa using h)]; rfl
  · rw [if_neg h, List.filter_cons_of_neg (by simpa using h)]

@[simp] theorem blockExp_binBlock (c e : ℤ) : blockExp (binBlock c e) = e := by
  unfold binBlock; split_ifs <;> rfl

@[simp] theorem shiftBlock_binBlock (d c e : ℤ) : shiftBlock d (binBlock c e) = binBlock c (e + d) := by
  unfold binBlock; split_ifs <;> rfl

theorem localize_sq_in {E u : ℤ} {D : List DyBlock} {l len : ℕ} (h1 : (l : ℤ) ≤ E) (h2 : E < (l : ℤ) + len) :
    localize (.sq E u :: D) l len = .sq (E - l) u :: localize D l len := by
  rw [localize_cons, if_pos ⟨h1, h2⟩]; simp [shiftBlock, sub_eq_add_neg]

theorem localize_sq_out {E u : ℤ} {D : List DyBlock} {l len : ℕ} (h : E < (l : ℤ) ∨ (l : ℤ) + len ≤ E) :
    localize (.sq E u :: D) l len = localize D l len := by
  rw [localize_cons, if_neg (by simp only [blockExp]; omega)]

theorem localize_bin_in {E c : ℤ} {D : List DyBlock} {l len : ℕ} (h1 : (l : ℤ) ≤ E) (h2 : E < (l : ℤ) + len) :
    localize (binBlock c E :: D) l len = binBlock c (E - l) :: localize D l len := by
  rw [localize_cons, if_pos ⟨by simpa using h1, by simpa using h2⟩]; simp [sub_eq_add_neg]

theorem localize_bin_out {E c : ℤ} {D : List DyBlock} {l len : ℕ} (h : E < (l : ℤ) ∨ (l : ℤ) + len ≤ E) :
    localize (binBlock c E :: D) l len = localize D l len := by
  rw [localize_cons, if_neg (by simp only [blockExp_binBlock]; omega)]

theorem binBlock_inj_exp {c E E' : ℤ} : binBlock c E = binBlock c E' ↔ E = E' := by
  unfold binBlock; split_ifs <;> simp

/-- Evaluate localized explicit lists. -/
macro "loc_tac" : tactic => `(tactic| (
  simp (disch := omega) only [sqL, sqList, binL, binList, localize_nil, localize_sq_in, localize_sq_out,
    localize_bin_in, localize_bin_out]
  try simp only [List.cons.injEq, DyBlock.sq.injEq, binBlock_inj_exp, and_true, true_and]
  try (repeat' constructor) <;> omega))

/-! ### Lists differing only in units -/

/-- The block with its unit forgotten (set to $1$). -/
def forgetUnit : DyBlock → DyBlock
  | .sq e _ => .sq e 1
  | .hyp e => .hyp e
  | .ell e => .hyp e

@[simp] theorem forgetUnit_binBlock (c e : ℤ) : forgetUnit (binBlock c e) = .hyp e := by
  unfold binBlock; split_ifs <;> rfl

theorem blockExp_forgetUnit (b : DyBlock) : blockExp (forgetUnit b) = blockExp b := by cases b <;> rfl
theorem dim_forgetUnit (b : DyBlock) : (forgetUnit b).dim = b.dim := by cases b <;> rfl
theorem isSqBlock_forgetUnit (b : DyBlock) : IsSqBlock (forgetUnit b) ↔ IsSqBlock b := by cases b <;> rfl

theorem dim_eq_of_forget {L L' : List DyBlock} (h : L.map forgetUnit = L'.map forgetUnit) (k : ℕ) :
    (blockSymbol L k).dim = (blockSymbol L' k).dim := by
  rw [dim_blockSymbol, dim_blockSymbol]
  have e : ∀ M : List DyBlock, (M.map fun b => if blockExp b = k then b.dim else 0) =
      (M.map forgetUnit).map fun b => if blockExp b = k then b.dim else 0 := by
    intro M; rw [List.map_map]; congr 1; funext b; simp [blockExp_forgetUnit, dim_forgetUnit]
  rw [e L, e L', h]

theorem type_eq_of_forget {L L' : List DyBlock} (h : L.map forgetUnit = L'.map forgetUnit) (k : ℕ) :
    (blockSymbol L k).type = (blockSymbol L' k).type := by
  have key : ∀ M : List DyBlock, ((blockSymbol M k).type = .I ↔
      ∃ b ∈ M.map forgetUnit, IsSqBlock b ∧ blockExp b = k) := by
    intro M
    rw [type_eq_I_iff]
    simp only [List.mem_map, exists_exists_and_eq_and, isSqBlock_forgetUnit, blockExp_forgetUnit]
  have hiff : (blockSymbol L k).type = .I ↔ (blockSymbol L' k).type = .I := by rw [key L, key L', h]
  cases hL : (blockSymbol L k).type <;> cases hL' : (blockSymbol L' k).type <;> simp_all

/-! ### First-in-class units for a computable description of the classes -/

theorem minSq_eq_filter {u : ℤ} {e₁ e₂ : ℕ} (E : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ → Prop) [DecidableRel E]
    (hE : ∀ x ∈ sqUnits3 u, ∀ y ∈ sqUnits3 u, SymEquiv (sqL e₁ e₂ x) (sqL e₁ e₂ y) ↔ E x y) :
    minSq u e₁ e₂ = (sqUnits3 u).filter fun x => ∀ x' ∈ sqUnits3 u, E x' x → enc3 x ≤ enc3 x' := by
  classical
  unfold minSq
  refine Finset.filter_congr fun x hx => ?_
  exact forall₂_congr fun x' hx' => imp_congr_left (hE x' hx' x hx)

theorem minBin_eq_filter {u : ℤ} {m e : ℕ} (E : ℤ × ℤ → ℤ × ℤ → Prop) [DecidableRel E]
    (hE : ∀ x ∈ binUnits u, ∀ y ∈ binUnits u, SymEquiv (binL m e x) (binL m e y) ↔ E x y) :
    minBin u m e = (binUnits u).filter fun x => ∀ x' ∈ binUnits u, E x' x → enc2 x ≤ enc2 x' := by
  classical
  unfold minBin
  refine Finset.filter_congr fun x hx => ?_
  exact forall₂_congr fun x' hx' => imp_congr_left (hE x' hx' x hx)

/-! ### Mass weights from windows -/

/-- The species (Conway–Sloane 1988, Table 1) of the constituents of scales $2^0, \dots, 2^{len-1}$ of $L$. -/
def locSpecies (L : List DyBlock) (len : ℕ) : List Species :=
  (List.range len).map fun i => twoSpecies (blockSymbol L i) (IsBound (blockSymbol L) i)

theorem locDiag_eq (L : List DyBlock) (len : ℕ) :
    locDiag L len = ((locSpecies L len).map (Species.diagFactor 2)).prod := by
  unfold locDiag locSpecies
  rw [List.map_map, ← List.toFinset_range, List.prod_toFinset _ (List.nodup_range)]
  rfl

theorem pMassTwo_base {u : ℤ} (hu : u ∈ sqUnits) : pMassTwo (blockSymbol (baseList u)) 2 = 1 / 6 := by
  have hdec : WinDecomp (baseList u) [(0, 3)] := by
    refine ⟨by simp, by simp, ?_, ?_, ?_⟩
    · intro b hb
      simp only [baseList, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> simp [blockExp]
    · simp [localize_cons, localize_nil, baseList, blockExp, blockSymbol_cons, blockSymbol_nil, addBlock,
        TwoFactor.trivial, shiftBlock, IsSqBlock]
    · simp [localize_cons, localize_nil, baseList, blockExp, blockSymbol_cons, blockSymbol_nil, addBlock,
        TwoFactor.trivial, shiftBlock]
  have htriv : ∀ k, 2 ≤ k → blockSymbol (baseList u) k = TwoFactor.trivial := fun k hk =>
    blockSymbol_of_forall_ne fun b hb => by
      simp only [baseList, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> simp [blockExp] <;> omega
  rw [← pMassTwo_congr htriv (show 2 ≤ 3 by omega),
    pMassTwo_eq_local hdec (by simp) (by simp [baseList, blockSymbol_cons, blockSymbol_nil, addBlock, blockExp,
      TwoFactor.trivial, IsSqBlock]) (by simp)]
  rw [crossExp_blockSymbol _ (fun b hb => by
    simp only [baseList, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> simp [blockExp])]
  have hloc : localize (baseList u) 0 3 = [DyBlock.hyp 0, DyBlock.sq 1 ((-u) % 8)] := by
    simp [localize_cons, localize_nil, baseList, blockExp, shiftBlock]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, List.sum_cons, List.sum_nil,
    Nat.sub_zero, hloc]
  have hc : (([DyBlock.hyp 0, DyBlock.sq 1 ((-u) % 8)].map fun b =>
      ([DyBlock.hyp 0, DyBlock.sq 1 ((-u) % 8)].map fun b' =>
        if (blockExp b).toNat < (blockExp b').toNat ∧ (blockExp b').toNat < 3 then
          ((blockExp b').toNat - (blockExp b).toNat) * b.dim * b'.dim else 0).sum).sum) = 2 := by
    simp [blockExp, DyBlock.dim]
  simp only [sqUnits, Finset.mem_insert, Finset.mem_singleton] at hu
  have hd : locDiag [DyBlock.hyp 0, DyBlock.sq 1 ((-u) % 8)] 3 = 1 / 3 := by
    have : locSpecies [DyBlock.hyp 0, DyBlock.sq 1 ((-u) % 8)] 3 = [⟨3, .plus⟩, ⟨0, .plus⟩, ⟨1, .plus⟩] := by
      rcases hu with rfl | rfl | rfl | rfl <;> decide
    rw [locDiag_eq, this]
    norm_num [Species.diagFactor, lowerProd]
  have hn : locNII [DyBlock.hyp 0, DyBlock.sq 1 ((-u) % 8)] 3 = 2 := by
    rcases hu with rfl | rfl | rfl | rfl <;> decide
  have hn' : locNII' [DyBlock.hyp 0, DyBlock.sq 1 ((-u) % 8)] 3 = 0 := by
    rcases hu with rfl | rfl | rfl | rfl <;> decide
  simp only [baseList] at hc ⊢
  rw [hc, hd, hn, hn']
  norm_num

/-- **Mass weight of an admissible list, from a window decomposition.** -/
theorem massWt_eq_local {h : ℕ} {u : ℤ} (hu : u ∈ sqUnits) {D : List DyBlock} {ws : List (ℕ × ℕ)}
    (hD : WinDecomp D ws) (hnd : ws.Nodup) (h0 : (blockSymbol D 0).type = .II) {N : ℕ}
    (hN : ∀ w ∈ ws, w.2 ≤ N) (hhN : h + 1 ≤ N) (hexp : ∀ b ∈ D, 0 ≤ blockExp b ∧ blockExp b ≤ h) :
    massWt h u D = (1 / 4 : ℝ) ^ (h - 1) * 6 *
      ((((ws.map fun w => locDiag (localize D w.1 (w.2 - w.1)) (w.2 - w.1)).prod : ℚ) : ℝ) *
        Real.sqrt 2 ^ crossExp (fun k => (blockSymbol D k).dim) N *
        (2 : ℝ) ^ (((ws.map fun w => locNII' (localize D w.1 (w.2 - w.1)) (w.2 - w.1)).sum : ℤ) -
          ((ws.map fun w => locNII (localize D w.1 (w.2 - w.1)) (w.2 - w.1)).sum : ℤ))) := by
  have htriv : ∀ k, h + 1 ≤ k → blockSymbol D k = TwoFactor.trivial := fun k hk =>
    blockSymbol_of_forall_ne fun b hb => by have := hexp b hb; omega
  unfold massWt
  rw [← pMassTwo_congr htriv hhN, pMassTwo_eq_local hD hnd h0 hN, pMassTwo_base hu]
  ring

/-! ### Hasse invariants of the two shapes -/

theorem hasseQ_sqL (e₁ e₂ : ℕ) (x : ℤ × ℤ × ℤ) :
    hasseQ (sqL e₁ e₂ x) = hasseList [(0, (x.1 : ZMod 8)), ((e₁ + 1) % 2, (x.2.1 : ZMod 8)),
      ((e₂ + 1) % 2, (x.2.2 : ZMod 8))] := by
  unfold hasseQ
  rw [hasseList_mod]
  simp [sqL, sqList, blockDiag]

theorem hasseQ_binL (m e : ℕ) (x : ℤ × ℤ) :
    hasseQ (binL m e x) = hasseList [(m % 2, 1), (m % 2, if x.1 = 3 then 3 else -1),
      ((e + 1) % 2, (x.2 : ZMod 8))] := by
  unfold hasseQ
  rw [hasseList_mod]
  simp only [binL, binList, binBlock]
  split_ifs <;> simp [blockDiag]

theorem hasseQ_baseList (u : ℤ) :
    hasseQ (baseList u) = hasseList [(0, 1), (0, -1), (0, (((-u) % 8 : ℤ) : ZMod 8))] := by
  unfold hasseQ
  rw [hasseList_mod]
  simp [baseList, blockDiag]

end QuadFormsKB.Dyadic7
