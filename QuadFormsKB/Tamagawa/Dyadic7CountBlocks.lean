/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Dyadic7CountWindow
import QuadFormsKB.Tamagawa.Dyadic7Table

/-!
# Paper 7 at $p = 2$: block lists, windows, 2-masses and class sums

Generic tools for proving `Dyadic7.TernaryDyadicMassCount` (Hanke 2011, Thm. 4.12 / Table 5.3):

* **Symbols of block lists, locally.** `localize D l len`: the blocks of $D$ with exponent in $[l, l + len)$, shifted
  down by $l$; `blockSymbol_localize`: the symbol of $D$ at scale $2^{l+i}$ is that of `localize D l len` at $2^i$.
  `blockSymbol_perm`: the symbol only depends on the multiset of blocks.
* **Window decompositions** (`WinDecomp D ws`): the windows `ws` are disjoint, contain all exponents of $D$ and begin
  and end with type II scales. Then (`moveEquiv_iff_local`) sign walking and oddity fusion between two lists with the
  same windows is decided window by window on the localized lists (`WinEq`), and (`pMassTwo_eq_local`)
  Conway–Sloane's 2-mass factors as a product of window factors (`locDiag`, `locNII`, `locNII'`) times the cross
  term, which is given by the exponents (`crossExp_blockSymbol`).
* **Primitivity** in terms of blocks (`isPrimBlocks_iff`) and the two shapes of admissible lists
  (`exists_sorted_of_mem_admSet`: up to order, $D = [2^m\beta, 2^e w x^2]$ with $\beta$ a binary block, or
  $D = [2 a x^2, 2^{e_1} b y^2, 2^{e_2} c z^2]$, $1 \le e_1 \le e_2$).
* **Class sums** (`sum_div_card_eq_sum`): a sum over a finite set of $g/(\text{class size})$, for $g$ constant on
  classes, is the sum of $g$ over a set of class representatives; `massWt` and `hasseQ` are class invariants
  (`massWt_eq_of_moveEquiv`, `hasseQ_eq_of_moveEquiv`).

Indices are 0-based.
-/

open Finset

namespace QuadFormsKB.Dyadic7

open QuadFormsKB.ConwaySloane QuadFormsKB.ConwaySloane.Mass Cassels QuadFormsKB.Hanke2011Ternary
  IsDedekindDomain NumberField

/-! ### Shifting and localizing block lists -/

/-- The block `b` with its exponent shifted by `d`. -/
def shiftBlock (d : ℤ) : DyBlock → DyBlock
  | .sq e u => .sq (e + d) u
  | .hyp e => .hyp (e + d)
  | .ell e => .ell (e + d)

@[simp] theorem blockExp_shiftBlock (d : ℤ) (b : DyBlock) : blockExp (shiftBlock d b) = blockExp b + d := by
  cases b <;> rfl
@[simp] theorem dim_shiftBlock (d : ℤ) (b : DyBlock) : (shiftBlock d b).dim = b.dim := by cases b <;> rfl
@[simp] theorem blockSign_shiftBlock (d : ℤ) (b : DyBlock) : blockSign (shiftBlock d b) = blockSign b := by
  cases b <;> rfl
@[simp] theorem blockOddity_shiftBlock (d : ℤ) (b : DyBlock) : blockOddity (shiftBlock d b) = blockOddity b := by
  cases b <;> rfl
@[simp] theorem decide_isSqBlock_shiftBlock (d : ℤ) (b : DyBlock) :
    decide (IsSqBlock (shiftBlock d b)) = decide (IsSqBlock b) := by
  cases b <;> rfl

/-- **The blocks of $D$ in the window $[l, l + len)$**, shifted down by $l$. -/
def localize (D : List DyBlock) (l len : ℕ) : List DyBlock :=
  (D.filter fun b => decide ((l : ℤ) ≤ blockExp b ∧ blockExp b < (l : ℤ) + len)).map (shiftBlock (-(l : ℤ)))

theorem blockSymbol_eq_of_filter {D D' : List DyBlock} {k k' : ℕ} (d : ℤ)
    (h : D'.filter (fun b => decide (blockExp b = (k' : ℤ))) =
      (D.filter fun b => decide (blockExp b = (k : ℤ))).map (shiftBlock d)) :
    blockSymbol D' k' = blockSymbol D k := by
  simp only [blockSymbol, h, List.map_map, Function.comp_def, dim_shiftBlock, blockSign_shiftBlock,
    blockOddity_shiftBlock, List.any_map, decide_isSqBlock_shiftBlock]

/-- **Symbols are local:** the constituent of scale $2^{l+i}$ of $D$ is the constituent of scale $2^i$ of the blocks of
$D$ in the window $[l, l + len)$, shifted down by $l$ ($i < len$). -/
theorem blockSymbol_localize (D : List DyBlock) (l len i : ℕ) (hi : i < len) :
    blockSymbol (localize D l len) i = blockSymbol D (l + i) := by
  apply blockSymbol_eq_of_filter (-(l : ℤ))
  unfold localize
  rw [List.filter_map, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro b _
  rw [Bool.eq_iff_iff]
  simp only [Function.comp_apply, blockExp_shiftBlock, Bool.and_eq_true, decide_eq_true_eq]
  push_cast
  omega

theorem blockSymbol_of_forall_ne {D : List DyBlock} {k : ℕ} (h : ∀ b ∈ D, blockExp b ≠ k) :
    blockSymbol D k = TwoFactor.trivial := by
  have hnil : D.filter (fun b => decide (blockExp b = (k : ℤ))) = [] :=
    List.filter_eq_nil_iff.2 fun b hb hbk => h b hb (by simpa using hbk)
  simp only [blockSymbol, hnil]
  simp [TwoFactor.trivial, Sign.prodList]

theorem blockSymbol_localize_of_le (D : List DyBlock) (l len j : ℕ) (hj : len ≤ j) :
    blockSymbol (localize D l len) j = TwoFactor.trivial := by
  refine blockSymbol_of_forall_ne fun b hb => ?_
  simp only [localize, List.mem_map, List.mem_filter, decide_eq_true_eq] at hb
  obtain ⟨b', ⟨-, h1, h2⟩, rfl⟩ := hb
  simp only [blockExp_shiftBlock]
  omega

/-- A constituent of type II of a block list has oddity $0$. -/
theorem oddity_eq_zero_of_typeII (D : List DyBlock) (k : ℕ) (h : (blockSymbol D k).type = .II) :
    (blockSymbol D k).oddity = 0 := by
  simp only [blockSymbol] at h ⊢
  split_ifs at h with hany
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
  cases b with
  | sq e u => exact absurd (List.any_eq_true.2 ⟨_, hb, by simp [IsSqBlock]⟩) hany
  | hyp e => rfl
  | ell e => rfl

theorem Sign.prodList_perm {l l' : List Sign} (h : l.Perm l') : Sign.prodList l = Sign.prodList l' := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [Sign.prodList, ih]
  | swap x y l => simp only [Sign.prodList]; cases x <;> cases y <;> rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **The symbol of a block list only depends on the multiset of blocks.** -/
theorem blockSymbol_perm {D D' : List DyBlock} (h : D.Perm D') : blockSymbol D = blockSymbol D' := by
  funext k
  have hf := h.filter (fun b => decide (blockExp b = (k : ℤ)))
  simp only [blockSymbol]
  have hany : (D.filter fun b => decide (blockExp b = (k : ℤ))).any (fun b => decide (IsSqBlock b)) =
      (D'.filter fun b => decide (blockExp b = (k : ℤ))).any (fun b => decide (IsSqBlock b)) := by
    rw [Bool.eq_iff_iff]
    simp only [List.any_eq_true]
    exact ⟨fun ⟨x, hx, h'⟩ => ⟨x, hf.subset hx, h'⟩, fun ⟨x, hx, h'⟩ => ⟨x, hf.symm.subset hx, h'⟩⟩
  rw [(hf.map _).sum_eq, Sign.prodList_perm (hf.map _), (hf.map _).sum_eq, hany]

/-! ### Window decompositions of block lists -/

/-- **A window decomposition** of the block list $D$: the windows $(l, r)$ of `ws` are nonempty and pairwise disjoint,
every exponent of $D$ lies in a window, and the first and last scales of every window are of type II. -/
structure WinDecomp (D : List DyBlock) (ws : List (ℕ × ℕ)) : Prop where
  lt : ∀ w ∈ ws, w.1 < w.2
  disj : ∀ w ∈ ws, ∀ w' ∈ ws, w ≠ w' → w.2 ≤ w'.1 ∨ w'.2 ≤ w.1
  cover : ∀ b ∈ D, ∃ w ∈ ws, (w.1 : ℤ) ≤ blockExp b ∧ blockExp b < w.2
  left : ∀ w ∈ ws, (blockSymbol (localize D w.1 (w.2 - w.1)) 0).type = .II
  right : ∀ w ∈ ws, (blockSymbol (localize D w.1 (w.2 - w.1)) (w.2 - w.1 - 1)).type = .II

namespace WinDecomp

variable {D : List DyBlock} {ws : List (ℕ × ℕ)} (hD : WinDecomp D ws)
include hD

theorem out {k : ℕ} (hk : ∀ w ∈ ws, ¬ (w.1 ≤ k ∧ k < w.2)) : blockSymbol D k = TwoFactor.trivial := by
  refine blockSymbol_of_forall_ne fun b hb hbk => ?_
  obtain ⟨w, hw, h1, h2⟩ := hD.cover b hb
  exact hk w hw ⟨by omega, by omega⟩

theorem inside {w : ℕ × ℕ} {i : ℕ} (hi : i < w.2 - w.1) :
    blockSymbol D (w.1 + i) = blockSymbol (localize D w.1 (w.2 - w.1)) i :=
  (blockSymbol_localize D w.1 _ i hi).symm

theorem typeII_start {w : ℕ × ℕ} (hw : w ∈ ws) : (blockSymbol D w.1).type = .II := by
  have h := hD.left w hw
  rwa [← hD.inside (i := 0) (by have := hD.lt w hw; omega), add_zero] at h

theorem typeII_end {w : ℕ × ℕ} (hw : w ∈ ws) : (blockSymbol D (w.2 - 1)).type = .II := by
  have hlt := hD.lt w hw
  have h := hD.right w hw
  rwa [← hD.inside (i := w.2 - w.1 - 1) (by omega), show w.1 + (w.2 - w.1 - 1) = w.2 - 1 by omega] at h

theorem typeII_before {w : ℕ × ℕ} (hw : w ∈ ws) (h0 : w.1 ≠ 0) : (blockSymbol D (w.1 - 1)).type = .II := by
  by_cases hin : ∃ w' ∈ ws, w'.1 ≤ w.1 - 1 ∧ w.1 - 1 < w'.2
  · obtain ⟨w', hw', h1, h2⟩ := hin
    have hne : w ≠ w' := by rintro rfl; omega
    rcases hD.disj w hw w' hw' hne with h | h
    · have := hD.lt w hw; omega
    · rw [show w.1 - 1 = w'.2 - 1 by omega]; exact hD.typeII_end hw'
  · push Not at hin
    rw [hD.out fun w' hw' h => by have := hin w' hw' h.1; omega]; rfl

theorem typeII_after {w : ℕ × ℕ} (hw : w ∈ ws) : (blockSymbol D w.2).type = .II := by
  by_cases hin : ∃ w' ∈ ws, w'.1 ≤ w.2 ∧ w.2 < w'.2
  · obtain ⟨w', hw', h1, h2⟩ := hin
    have hne : w ≠ w' := by rintro rfl; omega
    rcases hD.disj w hw w' hw' hne with h | h
    · rw [show w.2 = w'.1 by omega]; exact hD.typeII_start hw'
    · have := hD.lt w hw; omega
  · push Not at hin
    rw [hD.out fun w' hw' h => by have := hin w' hw' h.1; omega]; rfl

theorem typeII_out {k : ℕ} (hk : ∀ w ∈ ws, ¬ (w.1 ≤ k ∧ k < w.2)) : (blockSymbol D k).type = .II := by
  rw [hD.out hk]; rfl

/-- Outside the windows the constituents are free: their neighbours are of type II. -/
theorem not_isBound_out {k : ℕ} (hk : ∀ w ∈ ws, ¬ (w.1 ≤ k ∧ k < w.2)) : ¬ IsBound (blockSymbol D) k := by
  rintro (⟨hk0, h⟩ | h)
  · by_cases hin : ∃ w ∈ ws, w.1 ≤ k - 1 ∧ k - 1 < w.2
    · obtain ⟨w, hw, h1, h2⟩ := hin
      have hk2 : k = w.2 := by
        by_contra hne; exact hk w hw ⟨by omega, by omega⟩
      rw [show k - 1 = w.2 - 1 by omega, hD.typeII_end hw] at h; exact absurd h (by decide)
    · push Not at hin
      rw [hD.typeII_out fun w hw h' => by have := hin w hw h'.1; omega] at h; exact absurd h (by decide)
  · by_cases hin : ∃ w ∈ ws, w.1 ≤ k + 1 ∧ k + 1 < w.2
    · obtain ⟨w, hw, h1, h2⟩ := hin
      have hk2 : k + 1 = w.1 := by
        by_contra hne; exact hk w hw ⟨by omega, by omega⟩
      rw [hk2, hD.typeII_start hw] at h; exact absurd h (by decide)
    · push Not at hin
      rw [hD.typeII_out fun w hw h' => by have := hin w hw h'.1; omega] at h; exact absurd h (by decide)

theorem isBound_inside {w : ℕ × ℕ} (hw : w ∈ ws) {i : ℕ} (hi : i < w.2 - w.1) :
    IsBound (blockSymbol D) (w.1 + i) ↔ IsBound (blockSymbol (localize D w.1 (w.2 - w.1))) i := by
  have hlt := hD.lt w hw
  unfold IsBound
  apply or_congr
  · rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp only [add_zero, ne_eq, not_true_eq_false, false_and, iff_false, not_and]
      intro h0
      rw [hD.typeII_before hw h0]; decide
    · rw [show w.1 + i - 1 = w.1 + (i - 1) by omega, hD.inside (show i - 1 < w.2 - w.1 by omega)]
      exact ⟨fun h => ⟨by omega, h.2⟩, fun h => ⟨by omega, h.2⟩⟩
  · by_cases hi' : i + 1 < w.2 - w.1
    · rw [show w.1 + i + 1 = w.1 + (i + 1) by omega, hD.inside hi']
    · rw [show w.1 + i + 1 = w.2 by omega, hD.typeII_after hw,
        blockSymbol_localize_of_le _ _ _ _ (by omega)]
      decide

end WinDecomp

/-- **Sign walking and oddity fusion between block lists, window by window.** If $D$ and $D'$ have the same window
decomposition `ws` (`hD`, `hD'`) and their localized lists have the same dimensions and types on every window
(`hloc`), then the symbols of $D$ and $D'$ are related by the moves iff `WinEq` holds for the localized symbols on
every window. -/
theorem moveEquiv_iff_local {D D' : List DyBlock} {ws : List (ℕ × ℕ)} (hD : WinDecomp D ws)
    (hD' : WinDecomp D' ws)
    (hloc : ∀ w ∈ ws, ∀ i < w.2 - w.1,
      (blockSymbol (localize D' w.1 (w.2 - w.1)) i).dim = (blockSymbol (localize D w.1 (w.2 - w.1)) i).dim ∧
      (blockSymbol (localize D' w.1 (w.2 - w.1)) i).type = (blockSymbol (localize D w.1 (w.2 - w.1)) i).type) :
    MoveEquiv (blockSymbol D) (blockSymbol D') ↔
      ∀ w ∈ ws, WinEq (blockSymbol (localize D w.1 (w.2 - w.1))) (blockSymbol (localize D' w.1 (w.2 - w.1)))
        (w.2 - w.1) := by
  set N := (ws.map Prod.snd).sum
  have hwN : ∀ w ∈ ws, w.2 ≤ N := fun w hw => List.le_sum_of_mem (List.mem_map_of_mem hw)
  have hagree : ∀ k, (∀ w ∈ ws, ¬ (w.1 ≤ k ∧ k < w.2)) → blockSymbol D' k = blockSymbol D k := fun k hk => by
    rw [hD.out hk, hD'.out hk]
  have hcases : ∀ k, (∃ w ∈ ws, ∃ i < w.2 - w.1, k = w.1 + i) ∨ (∀ w ∈ ws, ¬ (w.1 ≤ k ∧ k < w.2)) := by
    intro k
    by_cases h : ∃ w ∈ ws, w.1 ≤ k ∧ k < w.2
    · obtain ⟨w, hw, h1, h2⟩ := h
      exact Or.inl ⟨w, hw, k - w.1, by omega, by omega⟩
    · push Not at h
      exact Or.inr fun w hw h' => by have := h w hw h'.1; omega
  have hdim : ∀ k, (blockSymbol D' k).dim = (blockSymbol D k).dim := by
    intro k
    rcases hcases k with ⟨w, hw, i, hi, rfl⟩ | hk
    · rw [hD.inside hi, hD'.inside hi]; exact (hloc w hw i hi).1
    · rw [hagree k hk]
  have htype : ∀ k, (blockSymbol D' k).type = (blockSymbol D k).type := by
    intro k
    rcases hcases k with ⟨w, hw, i, hi, rfl⟩ | hk
    · rw [hD.inside hi, hD'.inside hi]; exact (hloc w hw i hi).2
    · rw [hagree k hk]
  have hodd : ∀ k, ¬ IsTypeI (blockSymbol D) k → (blockSymbol D' k).oddity = (blockSymbol D k).oddity := by
    intro k hk
    have h1 : (blockSymbol D k).type = .II := (typeII_iff_not_isTypeI _ _).mpr hk
    rw [oddity_eq_zero_of_typeII D k h1, oddity_eq_zero_of_typeII D' k (by rw [htype k]; exact h1)]
  have hout : ∀ k, N ≤ k → ∀ w ∈ ws, ¬ (w.1 ≤ k ∧ k < w.2) := fun k hk w hw h => by
    have := hwN w hw; omega
  have hN : ∀ k, N ≤ k → blockSymbol D' k = blockSymbol D k ∧ ¬ IsTypeI (blockSymbol D) k := fun k hk =>
    ⟨hagree k (hout k hk), (typeII_iff_not_isTypeI _ _).mp (hD.typeII_out (hout k hk))⟩
  have hal : ∀ w ∈ ws, w.1 < w.2 ∧ (w.1 = 0 ∨ (¬ IsTypeI (blockSymbol D) (w.1 - 1) ∧
      ¬ IsTypeI (blockSymbol D) w.1)) ∧ ¬ IsTypeI (blockSymbol D) (w.2 - 1) ∧ ¬ IsTypeI (blockSymbol D) w.2 := by
    intro w hw
    refine ⟨hD.lt w hw, ?_, (typeII_iff_not_isTypeI _ _).mp (hD.typeII_end hw),
      (typeII_iff_not_isTypeI _ _).mp (hD.typeII_after hw)⟩
    by_cases h0 : w.1 = 0
    · exact Or.inl h0
    · exact Or.inr ⟨(typeII_iff_not_isTypeI _ _).mp (hD.typeII_before hw h0),
        (typeII_iff_not_isTypeI _ _).mp (hD.typeII_start hw)⟩
  rw [moveEquiv_iff_winEq ws hdim htype hodd hN hwN hagree hD.disj hal]
  refine forall₂_congr fun w hw => winEq_congr (fun i hi => ?_) (fun i hi => ?_)
  · exact hD.inside hi
  · exact hD'.inside hi

/-! ### The 2-mass, window by window -/

/-- The product of the diagonal factors $M_2$ (Conway–Sloane 1988, (3) and Table 1) over the scales
$0, \dots, len - 1$ of the block list $L$. -/
def locDiag (L : List DyBlock) (len : ℕ) : ℚ :=
  ∏ i ∈ range len, (twoSpecies (blockSymbol L i) (IsBound (blockSymbol L) i)).diagFactor 2

/-- The total dimension of the type II constituents of $L$ of scales $2^0, \dots, 2^{len-1}$. -/
def locNII (L : List DyBlock) (len : ℕ) : ℕ :=
  ∑ i ∈ range len, if (blockSymbol L i).type = .II then (blockSymbol L i).dim else 0

/-- The number of adjacent pairs of type I constituents of $L$ of scales $2^i$, $2^{i+1}$, $i < len$. -/
def locNII' (L : List DyBlock) (len : ℕ) : ℕ :=
  ∑ i ∈ range len, if (blockSymbol L i).type = .I ∧ (blockSymbol L (i + 1)).type = .I then 1 else 0

/-- A product over $[0, n)$ of a function that is $1$ outside disjoint windows is the product of the window products. -/
@[to_additive]
theorem prod_range_eq_windows {M : Type*} [CommMonoid M] (F : ℕ → M) (ws : List (ℕ × ℕ)) (hnd : ws.Nodup)
    (hdisj : ∀ w ∈ ws, ∀ w' ∈ ws, w ≠ w' → w.2 ≤ w'.1 ∨ w'.2 ≤ w.1) (n : ℕ) (hn : ∀ w ∈ ws, w.2 ≤ n)
    (hF : ∀ k, (∀ w ∈ ws, ¬ (w.1 ≤ k ∧ k < w.2)) → F k = 1) :
    ∏ k ∈ range n, F k = (ws.map fun w => ∏ i ∈ range (w.2 - w.1), F (w.1 + i)).prod := by
  classical
  set U := ws.toFinset.biUnion fun w => Ico w.1 w.2
  have hU : U ⊆ range n := by
    intro k hk
    obtain ⟨w, hw, hk⟩ := Finset.mem_biUnion.1 hk
    have := hn w (List.mem_toFinset.1 hw)
    simp only [Finset.mem_Ico] at hk
    exact Finset.mem_range.2 (by omega)
  rw [← Finset.prod_subset hU fun k _ hkU => hF k fun w hw hkw =>
    hkU (Finset.mem_biUnion.2 ⟨w, List.mem_toFinset.2 hw, Finset.mem_Ico.2 hkw⟩)]
  rw [Finset.prod_biUnion]
  · rw [List.prod_toFinset _ hnd]
    congr 1
    refine List.map_congr_left fun w _ => ?_
    exact Finset.prod_Ico_eq_prod_range F w.1 w.2
  · intro w hw w' hw' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [Finset.mem_Ico] at hk hk'
    rcases hdisj w (List.mem_toFinset.1 hw) w' (List.mem_toFinset.1 hw') hne with h | h <;> omega

theorem diagFactor_trivial_free {σ : TwoSymbol} {k : ℕ} (hk : σ k = TwoFactor.trivial) (hb : ¬ IsBound σ k) :
    (twoSpecies (σ k) (IsBound σ k)).diagFactor 2 = 1 := by
  rw [hk, twoSpecies_trivial_free hb]; rfl

/-- **Conway–Sloane's 2-mass of a block list, window by window.** If $D$ has the window decomposition `ws` (no
repeated windows, all ending by $N$) and its scale-1 constituent is of type II, then
$$m_2(D) = \prod_{w}\mathrm{locDiag}(w)\cdot\sqrt2^{\,c}\cdot 2^{\sum_w(\mathrm{locNII}'(w) - \mathrm{locNII}(w))},$$
$c$ the exponent of the cross term (`crossExp`), the window factors computed on the localized lists. -/
theorem pMassTwo_eq_local {D : List DyBlock} {ws : List (ℕ × ℕ)} (hD : WinDecomp D ws) (hnd : ws.Nodup)
    (h0 : (blockSymbol D 0).type = .II) {N : ℕ} (hN : ∀ w ∈ ws, w.2 ≤ N) :
    pMassTwo (blockSymbol D) N =
      (((ws.map fun w => locDiag (localize D w.1 (w.2 - w.1)) (w.2 - w.1)).prod : ℚ) : ℝ) *
        Real.sqrt 2 ^ crossExp (fun k => (blockSymbol D k).dim) N *
        (2 : ℝ) ^ (((ws.map fun w => locNII' (localize D w.1 (w.2 - w.1)) (w.2 - w.1)).sum : ℤ) -
          ((ws.map fun w => locNII (localize D w.1 (w.2 - w.1)) (w.2 - w.1)).sum : ℤ)) := by
  have hdiag : diagProdTwo (blockSymbol D) N =
      (ws.map fun w => locDiag (localize D w.1 (w.2 - w.1)) (w.2 - w.1)).prod := by
    unfold diagProdTwo halfFactor
    rw [if_neg (by rw [h0]; decide), one_mul,
      prod_range_eq_windows _ ws hnd hD.disj (N + 1) (fun w hw => by have := hN w hw; omega)
        fun k hk => diagFactor_trivial_free (hD.out hk) (hD.not_isBound_out hk)]
    congr 1
    refine List.map_congr_left fun w hw => Finset.prod_congr rfl fun i hi => ?_
    have hi' : i < w.2 - w.1 := Finset.mem_range.1 hi
    rw [hD.inside hi']
    exact congrArg (Species.diagFactor 2) (twoSpecies_congr (hD.isBound_inside hw hi') rfl rfl rfl)
  have hII : nII (blockSymbol D) N = (ws.map fun w => locNII (localize D w.1 (w.2 - w.1)) (w.2 - w.1)).sum := by
    unfold nII
    rw [sum_range_eq_windows _ ws hnd hD.disj N hN fun k hk => by rw [hD.out hk]; simp [TwoFactor.trivial]]
    congr 1
    refine List.map_congr_left fun w hw => Finset.sum_congr rfl fun i hi => ?_
    rw [hD.inside (Finset.mem_range.1 hi)]
  have hII' : nII' (blockSymbol D) N =
      (ws.map fun w => locNII' (localize D w.1 (w.2 - w.1)) (w.2 - w.1)).sum := by
    unfold nII'
    rw [sum_range_eq_windows _ ws hnd hD.disj N hN fun k hk => by
      rw [if_neg]; rw [hD.out hk]; exact fun h => absurd h.1 (by decide)]
    congr 1
    refine List.map_congr_left fun w hw => Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    have hlt := hD.lt w hw
    rw [hD.inside hi']
    by_cases h' : i + 1 < w.2 - w.1
    · rw [show w.1 + i + 1 = w.1 + (i + 1) by omega, hD.inside h']
    · have hend : (blockSymbol D (w.1 + i)).type = .II := by
        rw [show w.1 + i = w.2 - 1 by omega]; exact hD.typeII_end hw
      rw [hD.inside hi'] at hend
      rw [if_neg (fun h => absurd h.1 (by rw [hend]; decide)), if_neg (fun h => absurd h.1 (by rw [hend]; decide))]
  unfold pMassTwo
  rw [hdiag, hII, hII']

/-- The dimension of a constituent of a block list, as a sum over the blocks. -/
theorem dim_blockSymbol (D : List DyBlock) (k : ℕ) :
    (blockSymbol D k).dim = (D.map fun b => if blockExp b = k then b.dim else 0).sum := by
  simp only [blockSymbol]
  induction D with
  | nil => rfl
  | cons b D ih =>
    by_cases h : blockExp b = k
    · simp [List.filter_cons, h, ih]
    · simp [List.filter_cons, h, ih]

theorem sum_list_map_finset {ι α : Type*} (s : Finset ι) (L : List α) (f : ι → α → ℕ) :
    ∑ i ∈ s, (L.map (f i)).sum = (L.map fun a => ∑ i ∈ s, f i a).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [Finset.sum_add_distrib, ih]

/-- **The cross term of a block list** (Conway–Sloane 1988, (3)): $\sum_{k < k' < N}(k' - k)n_kn_{k'}$ as a double sum
over the blocks. -/
theorem crossExp_blockSymbol (D : List DyBlock) (h0 : ∀ b ∈ D, 0 ≤ blockExp b) (N : ℕ) :
    crossExp (fun k => (blockSymbol D k).dim) N =
      (D.map fun b => (D.map fun b' => if (blockExp b).toNat < (blockExp b').toNat ∧ (blockExp b').toNat < N
        then ((blockExp b').toNat - (blockExp b).toNat) * b.dim * b'.dim else 0).sum).sum := by
  have hd : ∀ k : ℕ, (blockSymbol D k).dim = (D.map fun b => if (blockExp b).toNat = k then b.dim else 0).sum := by
    intro k
    rw [dim_blockSymbol]
    congr 1
    refine List.map_congr_left fun b hb => ?_
    have := h0 b hb
    congr 1
    apply propext
    omega
  unfold crossExp
  simp only [hd]
  -- expand the products of sums
  have e1 : ∀ k' k : ℕ, (k' - k) * (D.map fun b => if (blockExp b).toNat = k then b.dim else 0).sum *
      (D.map fun b => if (blockExp b).toNat = k' then b.dim else 0).sum =
      (D.map fun b => (D.map fun b' => (k' - k) * (if (blockExp b).toNat = k then b.dim else 0) *
        (if (blockExp b').toNat = k' then b'.dim else 0)).sum).sum := by
    intro k' k
    have h1 : ∀ b, (D.map fun b' => (k' - k) * (if (blockExp b).toNat = k then b.dim else 0) *
        (if (blockExp b').toNat = k' then b'.dim else 0)).sum =
        (k' - k) * (if (blockExp b).toNat = k then b.dim else 0) *
          (D.map fun b' => if (blockExp b').toNat = k' then b'.dim else 0).sum := fun b =>
      List.sum_map_mul_left _ _ _
    simp only [h1]
    rw [List.sum_map_mul_right, List.sum_map_mul_left]
  simp only [e1]
  simp only [sum_list_map_finset]
  congr 1
  refine List.map_congr_left fun b _ => ?_
  congr 1
  refine List.map_congr_left fun b' _ => ?_
  set e := (blockExp b).toNat
  set e' := (blockExp b').toNat
  have inner : ∀ k', ∑ k ∈ range k', (k' - k) * (if e = k then b.dim else 0) * (if e' = k' then b'.dim else 0) =
      if e' = k' then (if e < k' then (k' - e) * b.dim * b'.dim else 0) else 0 := by
    intro k'
    rw [Finset.sum_eq_single e]
    · by_cases h : e < k'
      · by_cases h' : e' = k' <;> simp [h, h']
      · simp [h, Nat.sub_eq_zero_of_le (not_lt.1 h)]
    · intro k _ hk; simp [Ne.symm hk]
    · intro he
      simp [Nat.sub_eq_zero_of_le (by simpa using he : k' ≤ e)]
  simp only [inner]
  rw [Finset.sum_ite_eq]
  by_cases h1 : e < e' <;> by_cases h2 : e' < N <;> simp [h1, h2]

/-! ### The Hasse invariant only depends on exponents modulo 2 -/

theorem hilb2_mod (a b : ℕ × ZMod 8) : hilb2 a b = hilb2 (a.1 % 2, a.2) (b.1 % 2, b.2) := by
  unfold hilb2
  rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := _ + (a.1 % 2, a.2).1 * _ + _)]
  congr 1
  exact ((Nat.ModEq.refl _).add ((Nat.mod_modEq _ _).symm.mul_right _)).add
    ((Nat.mod_modEq _ _).symm.mul_right _)

theorem hasseList_mod : ∀ l : List (ℕ × ZMod 8), hasseList l = hasseList (l.map fun p => (p.1 % 2, p.2))
  | [] => rfl
  | a :: l => by
    simp only [hasseList, List.map_cons, List.map_map]
    rw [← hasseList_mod l]
    congr 1
    congr 1
    refine List.map_congr_left fun b _ => ?_
    rw [hilb2_mod]
    simp [Nat.mod_mod]

/-! ### Primitivity in terms of blocks -/

/-- The block contributes an odd coefficient to $Q_D = \tfrac12 H_D$: it is $2 u x^2$, $2^0\cdot 2xy$ or
$2^0(2x^2 + 2xy + 2y^2)$. -/
def IsPrimBlock : DyBlock → Prop
  | .sq e _ => e = 1
  | .hyp e => e = 0
  | .ell e => e = 0

instance (b : DyBlock) : Decidable (IsPrimBlock b) := by cases b <;> unfold IsPrimBlock <;> infer_instance

theorem exists_fin_add {a b : ℕ} (P : Fin (a + b) → Prop) :
    (∃ i, P i) ↔ (∃ i, P (Fin.castAdd b i)) ∨ ∃ i, P (Fin.natAdd a i) := by
  constructor
  · rintro ⟨i, hi⟩
    induction i using Fin.addCases with
    | left i => exact Or.inl ⟨i, hi⟩
    | right i => exact Or.inr ⟨i, hi⟩
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩) <;> exact ⟨_, hi⟩

@[simp] theorem orthSumMat_cc' {a b : ℕ} (F : Matrix (Fin a) (Fin a) ℤ) (G : Matrix (Fin b) (Fin b) ℤ)
    (i j : Fin a) : orthSumMat F G (Fin.castAdd b i) (Fin.castAdd b j) = F i j := by
  simp [orthSumMat, Matrix.reindex_apply]
@[simp] theorem orthSumMat_cn' {a b : ℕ} (F : Matrix (Fin a) (Fin a) ℤ) (G : Matrix (Fin b) (Fin b) ℤ)
    (i : Fin a) (j : Fin b) : orthSumMat F G (Fin.castAdd b i) (Fin.natAdd a j) = 0 := by
  simp [orthSumMat, Matrix.reindex_apply]
@[simp] theorem orthSumMat_nc' {a b : ℕ} (F : Matrix (Fin a) (Fin a) ℤ) (G : Matrix (Fin b) (Fin b) ℤ)
    (i : Fin b) (j : Fin a) : orthSumMat F G (Fin.natAdd a i) (Fin.castAdd b j) = 0 := by
  simp [orthSumMat, Matrix.reindex_apply]
@[simp] theorem orthSumMat_nn' {a b : ℕ} (F : Matrix (Fin a) (Fin a) ℤ) (G : Matrix (Fin b) (Fin b) ℤ)
    (i j : Fin b) : orthSumMat F G (Fin.natAdd a i) (Fin.natAdd a j) = G i j := by
  simp [orthSumMat, Matrix.reindex_apply]

/-- The odd coefficients of $Q_D$, read off its Hessian $H_D$ (`dyMatInt`): an odd $H_{ii}/2$ or an odd $H_{ij}$,
$i \ne j$. -/
def OddCoeff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∃ i, ¬ (2 : ℤ) ∣ M i i / 2) ∨ ∃ i j, i ≠ j ∧ ¬ (2 : ℤ) ∣ M i j

theorem two_pow_mul_div_two (n : ℕ) (u : ℤ) (hn : 1 ≤ n) : (2 : ℤ) ^ n * u / 2 = 2 ^ (n - 1) * u := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 1 + m - 1 = m by omega, pow_add, pow_one, mul_assoc]
  exact Int.mul_ediv_cancel_left _ two_ne_zero

theorem oddCoeff_one (M : Matrix (Fin 1) (Fin 1) ℤ) : OddCoeff M ↔ ¬ (2 : ℤ) ∣ M 0 0 / 2 := by
  simp [OddCoeff, Fin.exists_fin_one]

theorem oddCoeff_two (M : Matrix (Fin 2) (Fin 2) ℤ) : OddCoeff M ↔
    ¬ (2 : ℤ) ∣ M 0 0 / 2 ∨ ¬ (2 : ℤ) ∣ M 1 1 / 2 ∨ ¬ (2 : ℤ) ∣ M 0 1 ∨ ¬ (2 : ℤ) ∣ M 1 0 := by
  simp only [OddCoeff, Fin.exists_fin_two]
  simp
  tauto

theorem not_two_dvd_two_pow_iff (n : ℕ) : ¬ (2 : ℤ) ∣ 2 ^ n ↔ n = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · have := dvd_pow_self (2 : ℤ) (show n ≠ 0 by omega)
    simp only [this, not_true_eq_false, false_iff]; omega

theorem oddCoeff_block (b : DyBlock) (hv : b.Valid) (h0 : 0 ≤ blockExp b) (hev : ¬ IsOddUnimodBlock b) :
    OddCoeff (blockMatInt b) ↔ IsPrimBlock b := by
  cases b with
  | sq e u =>
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    have hn : n ≠ 0 := fun h => hev (by simp [IsOddUnimodBlock, h])
    have hu : Odd u := by
      simp only [DyBlock.Valid] at hv; rcases hv with rfl | rfl | rfl | rfl <;> decide
    change OddCoeff (!![(2:ℤ) ^ (n:ℤ).toNat * u] : Matrix (Fin 1) (Fin 1) ℤ) ↔ _
    rw [oddCoeff_one]
    simp only [IsPrimBlock, Int.toNat_natCast, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
      Matrix.empty_val']
    rw [two_pow_mul_div_two n u (by omega)]
    constructor
    · intro h
      by_contra hne
      exact h (dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _)
    · intro h
      have : n = 1 := by exact_mod_cast h
      subst this
      simpa using fun h => (Int.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr h)
  | hyp e =>
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    change OddCoeff (!![0, (2:ℤ) ^ (n:ℤ).toNat; 2 ^ (n:ℤ).toNat, 0] : Matrix (Fin 2) (Fin 2) ℤ) ↔ _
    rw [oddCoeff_two]
    simp only [IsPrimBlock, Int.toNat_natCast]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Int.zero_ediv, dvd_zero,
      not_true_eq_false, false_or, or_self, not_two_dvd_two_pow_iff]
    omega
  | ell e =>
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    change OddCoeff (!![(2:ℤ) ^ ((n:ℤ).toNat + 1), 2 ^ (n:ℤ).toNat; 2 ^ (n:ℤ).toNat, 2 ^ ((n:ℤ).toNat + 1)] :
      Matrix (Fin 2) (Fin 2) ℤ) ↔ _
    rw [oddCoeff_two]
    simp only [IsPrimBlock, Int.toNat_natCast]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    rw [show (2 : ℤ) ^ (n + 1) / 2 = 2 ^ n by rw [pow_succ]; exact Int.mul_ediv_cancel _ two_ne_zero]
    simp only [or_self, not_two_dvd_two_pow_iff]
    omega

theorem oddCoeff_orthSum {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℤ) (B : Matrix (Fin b) (Fin b) ℤ) :
    OddCoeff (orthSumMat A B) ↔ OddCoeff A ∨ OddCoeff B := by
  unfold OddCoeff
  constructor
  · rintro (⟨i, hi⟩ | ⟨i, j, hij, h⟩)
    · induction i using Fin.addCases with
      | left i => exact Or.inl (Or.inl ⟨i, by simpa using hi⟩)
      | right i => exact Or.inr (Or.inl ⟨i, by simpa using hi⟩)
    · induction i using Fin.addCases with
      | left i =>
        induction j using Fin.addCases with
        | left j => exact Or.inl (Or.inr ⟨i, j, fun e => hij (by rw [e]), by simpa using h⟩)
        | right j => simp at h
      | right i =>
        induction j using Fin.addCases with
        | left j => simp at h
        | right j => exact Or.inr (Or.inr ⟨i, j, fun e => hij (by rw [e]), by simpa using h⟩)
  · rintro ((⟨i, hi⟩ | ⟨i, j, hij, h⟩) | (⟨i, hi⟩ | ⟨i, j, hij, h⟩))
    · exact Or.inl ⟨Fin.castAdd b i, by simpa using hi⟩
    · exact Or.inr ⟨Fin.castAdd b i, Fin.castAdd b j, fun e => hij (Fin.castAdd_inj.1 e), by simpa using h⟩
    · exact Or.inl ⟨Fin.natAdd a i, by simpa using hi⟩
    · exact Or.inr ⟨Fin.natAdd a i, Fin.natAdd a j, fun e => hij ((Fin.natAdd_inj a).1 e), by simpa using h⟩

theorem oddCoeff_dyMatInt : ∀ (D : List DyBlock), (∀ b ∈ D, b.Valid) → (∀ b ∈ D, 0 ≤ blockExp b) →
    (∀ b ∈ D, ¬ IsOddUnimodBlock b) → (OddCoeff (dyMatInt D) ↔ ∃ b ∈ D, IsPrimBlock b)
  | [], _, _, _ => by
    simp only [List.not_mem_nil, false_and, exists_false, iff_false, OddCoeff]
    rintro (⟨i, -⟩ | ⟨i, -⟩) <;> exact absurd i.2 (by simp [dyDim])
  | b :: D, hv, h0, hev => by
    have ih := oddCoeff_dyMatInt D (fun c hc => hv c (List.mem_cons_of_mem _ hc))
      (fun c hc => h0 c (List.mem_cons_of_mem _ hc)) (fun c hc => hev c (List.mem_cons_of_mem _ hc))
    have hb := oddCoeff_block b (hv b (List.mem_cons_self ..)) (h0 b (List.mem_cons_self ..))
      (hev b (List.mem_cons_self ..))
    show OddCoeff (orthSumMat (blockMatInt b) (dyMatInt D)) ↔ _
    rw [oddCoeff_orthSum, hb, ih]
    simp only [List.mem_cons, exists_eq_or_imp]

/-- **Primitivity of $Q_D$ in terms of blocks:** some coefficient of $Q_D$ is odd iff $D$ has a block $2ux^2$,
$2^0\cdot2xy$ or $2^0(2x^2+2xy+2y^2)$ (for valid blocks, nonnegative exponents, even Hessian). -/
theorem isPrimBlocks_iff {D : List DyBlock} (hv : ∀ b ∈ D, b.Valid) (h0 : ∀ b ∈ D, 0 ≤ blockExp b)
    (hev : ∀ b ∈ D, ¬ IsOddUnimodBlock b) : IsPrimBlocks D ↔ ∃ b ∈ D, IsPrimBlock b := by
  rw [← oddCoeff_dyMatInt D hv h0 hev]
  unfold IsPrimBlocks OddCoeff
  simp only [formZ, QuadForm.ofUpper, Matrix.of_apply, hessZ_self]
  constructor
  · rintro ⟨i, j, h⟩
    by_cases hij : i ≤ j
    · rw [if_pos hij] at h
      by_cases he : i = j
      · subst he; exact Or.inl ⟨i, by simpa using h⟩
      · exact Or.inr ⟨i, j, he, by simpa [he] using h⟩
    · rw [if_neg hij] at h; exact absurd (dvd_zero _) h
  · rintro (⟨i, h⟩ | ⟨i, j, hne, h⟩)
    · exact ⟨i, i, by simpa using h⟩
    · rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact ⟨i, j, by simpa [hlt.le, hne] using h⟩
      · refine ⟨j, i, ?_⟩
        have hs : dyMatInt D j i = dyMatInt D i j := by
          have := congrFun (congrFun (transpose_dyMatInt D) i) j
          simpa [Matrix.transpose_apply] using this
        simpa [hlt.le, hne.symm, hs] using h

/-! ### The two shapes of admissible lists -/

/-- The binary block of unit `c`: $2^e\cdot 2xy$ if $c \ne 3$ ($\det = -1$), $2^e(2x^2+2xy+2y^2)$ if $c = 3$. -/
def binBlock (c e : ℤ) : DyBlock := if c = 3 then .ell e else .hyp e

/-- The binary shape $[2^m\beta_c,\ 2^e w x^2]$. -/
def binList (c w : ℤ) (m e : ℕ) : List DyBlock := [binBlock c m, .sq e w]

/-- The diagonal shape $[2 a x^2,\ 2^{e_1} b y^2,\ 2^{e_2} c z^2]$. -/
def sqList (a b c : ℤ) (e₁ e₂ : ℕ) : List DyBlock := [.sq 1 a, .sq e₁ b, .sq e₂ c]

theorem perm3_of_le {α : Type*} (x y z : α) (P : α → α → α → Prop)
    (h : ∀ x' y' z', [x, y, z].Perm [x', y', z'] → P x' y' z') :
    P x y z ∧ P y x z ∧ P x z y ∧ P z x y ∧ P y z x ∧ P z y x := by
  refine ⟨h _ _ _ (List.Perm.refl _), h _ _ _ (List.Perm.swap y x [z]), h _ _ _ (List.Perm.cons x
    (List.Perm.swap z y [])), ?_, ?_, ?_⟩
  · exact h _ _ _ ((List.Perm.cons x (List.Perm.swap z y [])).trans (List.Perm.swap z x [y]))
  · exact h _ _ _ ((List.Perm.swap y x [z]).trans (List.Perm.cons y (List.Perm.swap z x [])))
  · exact h _ _ _ ((List.Perm.swap y x [z]).trans ((List.Perm.cons y (List.Perm.swap z x [])).trans
      (List.Perm.swap z y [x])))

/-- **The two shapes of admissible ternary lists.** Every $D \in \mathrm{adm}(h, u)$ is, up to order, either
`binList c w m e` ($c \in \{-1, 3\}$, $w \in \{1,3,5,7\}$, $cw \equiv u \pmod 8$, $2m + e = h$, $e \ge 1$, and $m = 0$
or $e = 1$), or `sqList a b c e₁ e₂` ($a, b, c \in \{1,3,5,7\}$, $abc \equiv u \pmod 8$, $1 \le e_1 \le e_2$,
$1 + e_1 + e_2 = h$). -/
theorem exists_sorted_of_mem_admSet {h : ℕ} {u : ℤ} {D : List DyBlock} (hD : D ∈ admSet h u) :
    (∃ c w : ℤ, ∃ m e : ℕ, D.Perm (binList c w m e) ∧ (c = -1 ∨ c = 3) ∧ w ∈ sqUnits ∧
      (c * w) % 8 = u % 8 ∧ 2 * m + e = h ∧ 1 ≤ e ∧ (m = 0 ∨ e = 1)) ∨
    (∃ a b c : ℤ, ∃ e₁ e₂ : ℕ, D.Perm (sqList a b c e₁ e₂) ∧ a ∈ sqUnits ∧ b ∈ sqUnits ∧ c ∈ sqUnits ∧
      (a * b * c) % 8 = u % 8 ∧ 1 ≤ e₁ ∧ e₁ ≤ e₂ ∧ 1 + e₁ + e₂ = h) := by
  obtain ⟨hv, h0, hn, hev, hpr, hval, hunit⟩ := mem_admSet_iff.1 hD
  rw [isPrimBlocks_iff hv h0 hev] at hpr
  have hsq : ∀ (e u' : ℤ), DyBlock.sq e u' ∈ D → u' ∈ sqUnits ∧ ∃ n : ℕ, e = n ∧ 1 ≤ n := by
    intro e u' hm
    have h1 := hv _ hm
    have h2 := h0 _ hm
    have h3 := hev _ hm
    simp only [DyBlock.Valid] at h1
    simp only [blockExp] at h2
    simp only [IsOddUnimodBlock] at h3
    refine ⟨by simp [sqUnits]; tauto, e.toNat, by omega, by omega⟩
  rcases D with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨t, l⟩⟩⟩⟩
  · simp [dyDim] at hn
  · have := dim_bounds x; simp [dyDim] at hn; omega
  · -- two blocks: one binary, one diagonal
    left
    have key : ∀ (β : DyBlock) (e w : ℤ), β.dim = 2 → [β, .sq e w].Perm [x, y] →
        ∃ c w : ℤ, ∃ m e : ℕ, [x, y].Perm (binList c w m e) ∧ (c = -1 ∨ c = 3) ∧ w ∈ sqUnits ∧
          (c * w) % 8 = u % 8 ∧ 2 * m + e = h ∧ 1 ≤ e ∧ (m = 0 ∨ e = 1) := by
      intro β e w hβ hp
      have hmem : ∀ b, b ∈ [β, .sq e w] → b ∈ [x, y] := fun b hb => hp.subset hb
      obtain ⟨hw, n, rfl, hn1⟩ := hsq e w (hmem _ (by simp))
      have hβm := hmem β (by simp)
      have hβ0 := h0 β hβm
      have hval' : valSum [β, .sq (n : ℤ) w] = h := by
        rw [← hval]; exact (hp.map _).sum_eq
      have hunit' : unitProd [β, .sq (n : ℤ) w] % 8 = u % 8 := by
        rw [← hunit]; unfold unitProd; rw [(hp.map _).prod_eq]
      have hpr' : ∃ b ∈ [β, .sq (n : ℤ) w], IsPrimBlock b := by
        obtain ⟨b, hb, hb'⟩ := hpr; exact ⟨b, hp.symm.subset hb, hb'⟩
      cases β with
      | sq _ _ => simp [DyBlock.dim] at hβ
      | hyp m =>
        obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hβ0
        refine ⟨-1, w, k, n, ?_, Or.inl rfl, hw, ?_, ?_, hn1, ?_⟩
        · rw [binList, binBlock, if_neg (by decide)]; exact hp.symm
        · simpa [unitProd, blockUnit] using hunit'
        · simp [valSum, DyBlock.dim, blockExp] at hval'; omega
        · simp [IsPrimBlock] at hpr'; omega
      | ell m =>
        obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hβ0
        refine ⟨3, w, k, n, ?_, Or.inr rfl, hw, ?_, ?_, hn1, ?_⟩
        · rw [binList, binBlock, if_pos rfl]; exact hp.symm
        · simpa [unitProd, blockUnit] using hunit'
        · simp [valSum, DyBlock.dim, blockExp] at hval'; omega
        · simp [IsPrimBlock] at hpr'; omega
    cases x with
    | sq e w =>
      cases y with
      | sq _ _ => simp [dyDim, DyBlock.dim] at hn
      | hyp m => exact key (.hyp m) e w rfl (List.Perm.swap _ _ [])
      | ell m => exact key (.ell m) e w rfl (List.Perm.swap _ _ [])
    | hyp m =>
      cases y with
      | sq e w => exact key (.hyp m) e w rfl (List.Perm.refl _)
      | hyp _ => simp [dyDim, DyBlock.dim] at hn
      | ell _ => simp [dyDim, DyBlock.dim] at hn
    | ell m =>
      cases y with
      | sq e w => exact key (.ell m) e w rfl (List.Perm.refl _)
      | hyp _ => simp [dyDim, DyBlock.dim] at hn
      | ell _ => simp [dyDim, DyBlock.dim] at hn
  · -- three blocks: all diagonal
    right
    have hx : ∃ e a, x = .sq e a := by
      cases x with
      | sq e a => exact ⟨e, a, rfl⟩
      | hyp _ => have h1 := dim_bounds y; have h2 := dim_bounds z; simp only [dyDim, DyBlock.dim] at hn h1 h2; omega
      | ell _ => have h1 := dim_bounds y; have h2 := dim_bounds z; simp only [dyDim, DyBlock.dim] at hn h1 h2; omega
    have hy : ∃ e a, y = .sq e a := by
      cases y with
      | sq e a => exact ⟨e, a, rfl⟩
      | hyp _ => have h1 := dim_bounds x; have h2 := dim_bounds z; simp only [dyDim, DyBlock.dim] at hn h1 h2; omega
      | ell _ => have h1 := dim_bounds x; have h2 := dim_bounds z; simp only [dyDim, DyBlock.dim] at hn h1 h2; omega
    have hz : ∃ e a, z = .sq e a := by
      cases z with
      | sq e a => exact ⟨e, a, rfl⟩
      | hyp _ => have h1 := dim_bounds x; have h2 := dim_bounds y; simp only [dyDim, DyBlock.dim] at hn h1 h2; omega
      | ell _ => have h1 := dim_bounds x; have h2 := dim_bounds y; simp only [dyDim, DyBlock.dim] at hn h1 h2; omega
    obtain ⟨e₁, a₁, rfl⟩ := hx
    obtain ⟨e₂, a₂, rfl⟩ := hy
    obtain ⟨e₃, a₃, rfl⟩ := hz
    obtain ⟨ha₁, n₁, rfl, h₁⟩ := hsq e₁ a₁ (by simp)
    obtain ⟨ha₂, n₂, rfl, h₂⟩ := hsq e₂ a₂ (by simp)
    obtain ⟨ha₃, n₃, rfl, h₃⟩ := hsq e₃ a₃ (by simp)
    have hval' : n₁ + n₂ + n₃ = h := by simp [valSum, DyBlock.dim, blockExp] at hval; omega
    have hunit' : (a₁ * a₂ * a₃) % 8 = u % 8 := by simpa [unitProd, blockUnit, mul_assoc] using hunit
    have hone : n₁ = 1 ∨ n₂ = 1 ∨ n₃ = 1 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
      obtain ⟨b, hb, hb'⟩ := hpr
      rcases hb with rfl | rfl | rfl <;> simp [IsPrimBlock] at hb' <;> omega
    -- the goal for a sorted triple
    let P : DyBlock → DyBlock → DyBlock → Prop := fun _ _ _ => True
    have goal : ∀ (p q r : ℕ) (a b c : ℤ), [DyBlock.sq (n₁ : ℤ) a₁, .sq (n₂ : ℤ) a₂, .sq (n₃ : ℤ) a₃].Perm
        [.sq (p : ℤ) a, .sq (q : ℤ) b, .sq (r : ℤ) c] → p = 1 → 1 ≤ q → q ≤ r → a ∈ sqUnits → b ∈ sqUnits →
        c ∈ sqUnits → (a * b * c) % 8 = u % 8 → 1 + q + r = h →
        ∃ a b c : ℤ, ∃ e₁ e₂ : ℕ, [DyBlock.sq (n₁ : ℤ) a₁, .sq (n₂ : ℤ) a₂, .sq (n₃ : ℤ) a₃].Perm
          (sqList a b c e₁ e₂) ∧ a ∈ sqUnits ∧ b ∈ sqUnits ∧ c ∈ sqUnits ∧
          (a * b * c) % 8 = u % 8 ∧ 1 ≤ e₁ ∧ e₁ ≤ e₂ ∧ 1 + e₁ + e₂ = h := by
      intro p q r a b c hp hp1 hq hqr ha hb hc habc hh
      subst hp1
      exact ⟨a, b, c, q, r, by simpa [sqList] using hp, ha, hb, hc, habc, hq, hqr, hh⟩
    have hperm := perm3_of_le (DyBlock.sq (n₁ : ℤ) a₁) (.sq (n₂ : ℤ) a₂) (.sq (n₃ : ℤ) a₃)
      (fun x' y' z' => [DyBlock.sq (n₁ : ℤ) a₁, .sq (n₂ : ℤ) a₂, .sq (n₃ : ℤ) a₃].Perm [x', y', z'])
      fun _ _ _ h => h
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hperm
    rcases le_total n₁ n₂ with h12 | h12 <;> rcases le_total n₂ n₃ with h23 | h23 <;>
      rcases le_total n₁ n₃ with h13 | h13
    all_goals first
      | exact goal n₁ n₂ n₃ a₁ a₂ a₃ p1 (by omega) (by omega) (by omega) ha₁ ha₂ ha₃ hunit' (by omega)
      | exact goal n₂ n₁ n₃ a₂ a₁ a₃ p2 (by omega) (by omega) (by omega) ha₂ ha₁ ha₃
          (by rw [← hunit']; ring_nf) (by omega)
      | exact goal n₁ n₃ n₂ a₁ a₃ a₂ p3 (by omega) (by omega) (by omega) ha₁ ha₃ ha₂
          (by rw [← hunit']; ring_nf) (by omega)
      | exact goal n₃ n₁ n₂ a₃ a₁ a₂ p4 (by omega) (by omega) (by omega) ha₃ ha₁ ha₂
          (by rw [← hunit']; ring_nf) (by omega)
      | exact goal n₂ n₃ n₁ a₂ a₃ a₁ p5 (by omega) (by omega) (by omega) ha₂ ha₃ ha₁
          (by rw [← hunit']; ring_nf) (by omega)
      | exact goal n₃ n₂ n₁ a₃ a₂ a₁ p6 (by omega) (by omega) (by omega) ha₃ ha₂ ha₁
          (by rw [← hunit']; ring_nf) (by omega)
  · have := dim_bounds x; have := dim_bounds y; have := dim_bounds z; have := dim_bounds t
    have : dyDim l ≥ 0 := Nat.zero_le _
    simp [dyDim] at hn; omega

theorem mem_admSet_binList {h : ℕ} {u c w : ℤ} {m e : ℕ} (hc : c = -1 ∨ c = 3) (hw : w ∈ sqUnits)
    (hu : (c * w) % 8 = u % 8) (hh : 2 * m + e = h) (he : 1 ≤ e) (hp : m = 0 ∨ e = 1) :
    binList c w m e ∈ admSet h u := by
  have hw' : w = 1 ∨ w = 3 ∨ w = 5 ∨ w = 7 := by simpa [sqUnits] using hw
  have hv : ∀ b ∈ binList c w m e, b.Valid := by
    intro b hb
    simp only [binList, binBlock, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · split_ifs <;> trivial
    · exact hw'
  have h0 : ∀ b ∈ binList c w m e, 0 ≤ blockExp b := by
    intro b hb
    simp only [binList, binBlock, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · split_ifs <;> simp [blockExp]
    · simp [blockExp]
  have hev : ∀ b ∈ binList c w m e, ¬ IsOddUnimodBlock b := by
    intro b hb
    simp only [binList, binBlock, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · split_ifs <;> simp [IsOddUnimodBlock]
    · simp [IsOddUnimodBlock]; omega
  refine mem_admSet_iff.2 ⟨hv, h0, ?_, hev, (isPrimBlocks_iff hv h0 hev).2 ?_, ?_, ?_⟩
  · simp [binList, binBlock, dyDim]; split_ifs <;> rfl
  · rcases hp with rfl | rfl
    · exact ⟨binBlock c 0, by simp [binList], by unfold binBlock; split_ifs <;> simp [IsPrimBlock]⟩
    · exact ⟨.sq 1 w, by simp [binList], by simp [IsPrimBlock]⟩
  · simp only [valSum, binList, binBlock]; split_ifs <;> simp [DyBlock.dim, blockExp] <;> omega
  · simp only [unitProd, binList, binBlock]
    rcases hc with rfl | rfl
    · simpa [blockUnit] using hu
    · simpa [blockUnit] using hu

theorem mem_admSet_sqList {h : ℕ} {u a b c : ℤ} {e₁ e₂ : ℕ} (ha : a ∈ sqUnits) (hb : b ∈ sqUnits)
    (hc : c ∈ sqUnits) (hu : (a * b * c) % 8 = u % 8) (h1 : 1 ≤ e₁) (h2 : 1 ≤ e₂) (hh : 1 + e₁ + e₂ = h) :
    sqList a b c e₁ e₂ ∈ admSet h u := by
  have hv : ∀ x ∈ sqList a b c e₁ e₂, x.Valid := by
    intro x hx
    simp only [sqList, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · simpa [sqUnits, DyBlock.Valid] using ha
    · simpa [sqUnits, DyBlock.Valid] using hb
    · simpa [sqUnits, DyBlock.Valid] using hc
  have h0 : ∀ x ∈ sqList a b c e₁ e₂, 0 ≤ blockExp x := by
    intro x hx
    simp only [sqList, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [blockExp]
  have hev : ∀ x ∈ sqList a b c e₁ e₂, ¬ IsOddUnimodBlock x := by
    intro x hx
    simp only [sqList, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [IsOddUnimodBlock] <;> omega
  refine mem_admSet_iff.2 ⟨hv, h0, by simp [sqList, dyDim, DyBlock.dim], hev,
    (isPrimBlocks_iff hv h0 hev).2 ⟨.sq 1 a, by simp [sqList], by simp [IsPrimBlock]⟩, ?_, ?_⟩
  · simp [valSum, sqList, DyBlock.dim, blockExp]; omega
  · simpa [unitProd, sqList, blockUnit, mul_assoc] using hu

/-! ### Class sums -/

/-- **A class-weighted sum is a sum over representatives.** For an equivalence relation $R$, a function $g$ constant on
the classes in $S$, and a set $T \subseteq S$ of representatives (every element of $S$ is equivalent to one, and
distinct ones are inequivalent), $\sum_{a\in S} g(a)/\#\{a' \in S : a\,R\,a'\} = \sum_{t \in T} g(t)$. -/
theorem sum_div_card_eq_sum {α : Type*} [DecidableEq α] (S T : Finset α) (R : α → α → Prop) [DecidableRel R]
    (hR : Equivalence R) (g : α → ℝ) (hg : ∀ a ∈ S, ∀ b ∈ S, R a b → g a = g b) (hTS : T ⊆ S)
    (hcov : ∀ a ∈ S, ∃ t ∈ T, R a t) (huniq : ∀ t ∈ T, ∀ t' ∈ T, R t t' → t = t') :
    ∑ a ∈ S, g a / ((S.filter (R a)).card : ℝ) = ∑ t ∈ T, g t := by
  have hS : S = T.biUnion fun t => S.filter fun a => R a t := by
    ext a
    constructor
    · intro ha
      obtain ⟨t, ht, hat⟩ := hcov a ha
      exact Finset.mem_biUnion.2 ⟨t, ht, Finset.mem_filter.2 ⟨ha, hat⟩⟩
    · intro h
      obtain ⟨t, _, h⟩ := Finset.mem_biUnion.1 h
      exact (Finset.mem_filter.1 h).1
  rw [Finset.sum_congr hS (fun _ _ => rfl), Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun t ht => ?_
    have hcl : ∀ a ∈ S.filter (fun a => R a t), S.filter (R a) = S.filter fun a => R a t := by
      intro a ha
      have hat := (Finset.mem_filter.1 ha).2
      ext a'
      simp only [Finset.mem_filter]
      exact and_congr_right fun _ => ⟨fun h => hR.trans (hR.symm h) hat, fun h => hR.trans hat (hR.symm h)⟩
    rw [Finset.sum_congr rfl fun a ha => by
      rw [hcl a ha, hg a (Finset.mem_filter.1 ha).1 t (hTS ht) (Finset.mem_filter.1 ha).2]]
    rw [Finset.sum_const, nsmul_eq_mul]
    have hpos : ((S.filter fun a => R a t).card : ℝ) ≠ 0 := by
      have : t ∈ S.filter fun a => R a t := Finset.mem_filter.2 ⟨hTS ht, hR.refl t⟩
      exact_mod_cast (Finset.card_pos.2 ⟨t, this⟩).ne'
    field_simp
  · intro t ht t' ht' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro a ha ha'
    exact hne (huniq t ht t' ht' (hR.trans (hR.symm (Finset.mem_filter.1 ha).2) (Finset.mem_filter.1 ha').2))

/-- The relation "the symbols are related by sign walking and oddity fusion" on block lists. -/
def SymEquiv (D D' : List DyBlock) : Prop := MoveEquiv (blockSymbol D) (blockSymbol D')

theorem symEquiv_equivalence : Equivalence SymEquiv :=
  ⟨fun D => Relation.EqvGen.refl _, fun h => Relation.EqvGen.symm _ _ h,
    fun h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂⟩

theorem massWt_eq_of_moveEquiv {h : ℕ} {u : ℤ} {D D' : List DyBlock} (hm : SymEquiv D D') :
    massWt h u D = massWt h u D' := by
  unfold massWt; rw [pMassTwo_moveEquiv hm]

theorem exists_two_place : ∃ v : HeightOneSpectrum (𝓞 ℚ), (2 : 𝓞 ℚ) ∈ v.asIdeal := by
  have hdu : ¬ IsUnit (2 : 𝓞 ℚ) := fun h => by
    have := h.map (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ)
    rw [map_ofNat] at this
    rcases Int.isUnit_iff.1 this with h' | h' <;> norm_num at h'
  have hI : Ideal.span {(2 : 𝓞 ℚ)} ≠ ⊤ := fun h => hdu (Ideal.span_singleton_eq_top.mp h)
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hI
  have hne : M ≠ ⊥ := (Ideal.bot_lt_of_maximal M (RingOfIntegers.not_isField ℚ)).ne'
  exact ⟨⟨M, hM.isPrime, hne⟩, hle (Ideal.subset_span rfl)⟩

theorem hasseQ_eq_of_moveEquiv {h : ℕ} {u : ℤ} {D D' : List DyBlock} (hD : D ∈ admSet h u)
    (hD' : D' ∈ admSet h u) (hm : SymEquiv D D') : hasseQ D = hasseQ D' := by
  obtain ⟨v, h2⟩ := exists_two_place
  obtain ⟨hv, h0, hn, hev, -⟩ := mem_admSet_iff.1 hD
  obtain ⟨hv', h0', hn', hev', -⟩ := mem_admSet_iff.1 hD'
  have hg := (genusOf_eq_iff v h2 hv h0 hn hev hv' h0' hn' hev').2 hm
  rw [← hasse_genusOf v h2 hv h0 hn hev, ← hasse_genusOf v h2 hv' h0' hn' hev', hg]

open Classical in
/-- **The sums of `TernaryDyadicMassCount` as sums over class representatives.** -/
theorem classSum_eq {h : ℕ} {u : ℤ} (T : Finset (List DyBlock)) (g : List DyBlock → ℝ)
    (hg : ∀ D ∈ admSet h u, ∀ D' ∈ admSet h u, SymEquiv D D' → g D = g D') (hTS : T ⊆ admSet h u)
    (hcov : ∀ D ∈ admSet h u, ∃ t ∈ T, SymEquiv D t) (huniq : ∀ t ∈ T, ∀ t' ∈ T, SymEquiv t t' → t = t') :
    ∑ D ∈ admSet h u, g D / (classCount h u D : ℝ) = ∑ t ∈ T, g t := by
  have e : ∀ D, classCount h u D = ((admSet h u).filter (SymEquiv D)).card := by
    intro D; unfold classCount SymEquiv; congr 1
  simp only [e]
  exact sum_div_card_eq_sum _ T SymEquiv symEquiv_equivalence g hg hTS hcov huniq

end QuadFormsKB.Dyadic7
