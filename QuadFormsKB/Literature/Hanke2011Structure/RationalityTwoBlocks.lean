/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Dyadic7Blocks
import QuadFormsKB.Literature.Hanke2011Structure.RationalityTwoSymbol

/-!
# Paper 6, Theorem 5.4 at $p = 2$: block decompositions, cut and shifted

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Thm. 5.4, proof, p. 24.

Combinatorics of the 2-adic block decompositions (`Cassels.DyBlock`: $2^eux^2$, $2^e\cdot2xy$,
$2^e(2x^2+2xy+2y^2)$) of an even Hessian matrix, used for the dyadic case of Theorem 5.4:

* `lowL c D`, `highL c D`: the blocks of exponent $e \le c$, resp. $e > c$; their 2-adic symbols are the parts of the
  symbol of $D$ below and above the cut (`blockSymbol_lowL`, `blockSymbol_highL`), and the symbol of a concatenation
  separated at $c$ is glued (`blockSymbol_append`);
* `shiftL D`: every exponent raised by one (the form $Q \mapsto 2Q$); its symbol is the shifted symbol
  (`blockSymbol_shiftL`);
* determinant data (`dyDim`, `valSum`, `unitProd`) of concatenations and shifts, and the rank as the sum of the
  dimensions of the constituents (`dyDim_eq_sum`);
* the Hasse invariant `hasseQ` of a concatenation (`hasseQ_append`: the product of the two Hasse invariants and of a
  sign depending only on the valuations, ranks and unit classes, `crossSign`) and its invariance under a double shift
  (`hasseQ_shiftL_two`);
* primitivity: the form $Q_D$ is primitive iff some block is $2^0\cdot2xy$, $2^0(2x^2+2xy+2y^2)$ or $2^1ux^2$
  (`isPrimBlocks_iff`).

Indices are 0-based.
-/

open Finset Matrix

namespace QuadFormsKB.Hanke2011Structure.RatTwo

open QuadFormsKB.ConwaySloane QuadFormsKB.ConwaySloane.Mass QuadFormsKB.Dyadic7 Cassels QuadFormsKB.HilbertLocal

/-- **Admissible block lists**: valid units, nonnegative exponents, no block $2^0ux^2$ (the Hessian is even). -/
def AdmL (D : List DyBlock) : Prop :=
  (∀ b ∈ D, b.Valid) ∧ (∀ b ∈ D, 0 ≤ blockExp b) ∧ (∀ b ∈ D, ¬ IsOddUnimodBlock b)

/-- The blocks of exponent $e \le c$. -/
def lowL (c : ℕ) (D : List DyBlock) : List DyBlock := D.filter fun b => decide (blockExp b ≤ (c : ℤ))

/-- The blocks of exponent $e > c$. -/
def highL (c : ℕ) (D : List DyBlock) : List DyBlock := D.filter fun b => decide ((c : ℤ) < blockExp b)

/-- A block with its exponent raised by one. -/
def shift1 : DyBlock → DyBlock
  | .sq e u => .sq (e + 1) u
  | .hyp e => .hyp (e + 1)
  | .ell e => .ell (e + 1)

/-- Every exponent raised by one (the form $Q_D \mapsto 2Q_D$). -/
def shiftL (D : List DyBlock) : List DyBlock := D.map shift1

@[simp] theorem blockExp_shift1 (b : DyBlock) : blockExp (shift1 b) = blockExp b + 1 := by cases b <;> rfl
@[simp] theorem dim_shift1 (b : DyBlock) : (shift1 b).dim = b.dim := by cases b <;> rfl
@[simp] theorem blockSign_shift1 (b : DyBlock) : blockSign (shift1 b) = blockSign b := by cases b <;> rfl
@[simp] theorem blockOddity_shift1 (b : DyBlock) : blockOddity (shift1 b) = blockOddity b := by cases b <;> rfl
@[simp] theorem blockUnit_shift1 (b : DyBlock) : blockUnit (shift1 b) = blockUnit b := by cases b <;> rfl
theorem isSqBlock_shift1 (b : DyBlock) : IsSqBlock (shift1 b) ↔ IsSqBlock b := by cases b <;> rfl
theorem valid_shift1 (b : DyBlock) : (shift1 b).Valid ↔ b.Valid := by cases b <;> rfl

/-! ### Membership and admissibility -/

theorem mem_lowL {c : ℕ} {D : List DyBlock} {b : DyBlock} : b ∈ lowL c D ↔ b ∈ D ∧ blockExp b ≤ c := by
  simp [lowL]

theorem mem_highL {c : ℕ} {D : List DyBlock} {b : DyBlock} : b ∈ highL c D ↔ b ∈ D ∧ (c : ℤ) < blockExp b := by
  simp [highL]

theorem AdmL.lowL {c : ℕ} {D : List DyBlock} (h : AdmL D) : AdmL (lowL c D) :=
  ⟨fun b hb => h.1 b (mem_lowL.1 hb).1, fun b hb => h.2.1 b (mem_lowL.1 hb).1,
    fun b hb => h.2.2 b (mem_lowL.1 hb).1⟩

theorem AdmL.highL {c : ℕ} {D : List DyBlock} (h : AdmL D) : AdmL (highL c D) :=
  ⟨fun b hb => h.1 b (mem_highL.1 hb).1, fun b hb => h.2.1 b (mem_highL.1 hb).1,
    fun b hb => h.2.2 b (mem_highL.1 hb).1⟩

theorem AdmL.append {A B : List DyBlock} (hA : AdmL A) (hB : AdmL B) : AdmL (A ++ B) := by
  refine ⟨fun b hb => ?_, fun b hb => ?_, fun b hb => ?_⟩ <;> rcases List.mem_append.1 hb with h | h
  exacts [hA.1 b h, hB.1 b h, hA.2.1 b h, hB.2.1 b h, hA.2.2 b h, hB.2.2 b h]

theorem AdmL.shiftL {D : List DyBlock} (h : AdmL D) : AdmL (shiftL D) := by
  refine ⟨fun b hb => ?_, fun b hb => ?_, fun b hb => ?_⟩ <;>
    obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
  · exact (valid_shift1 b').2 (h.1 b' hb')
  · rw [blockExp_shift1]; have := h.2.1 b' hb'; omega
  · have := h.2.1 b' hb'
    cases b' with
    | sq e u => simp only [shift1, IsOddUnimodBlock]; simp only [blockExp] at this; omega
    | hyp e => exact id
    | ell e => exact id

/-! ### Symbols of cut, glued and shifted lists -/

/-- The blocks of exponent $k$. -/
def filterEq (k : ℕ) (D : List DyBlock) : List DyBlock := D.filter fun b => decide (blockExp b = (k : ℤ))

theorem blockSymbol_congr {D D' : List DyBlock} {k : ℕ} (h : filterEq k D = filterEq k D') :
    blockSymbol D k = blockSymbol D' k := by
  unfold blockSymbol
  simp only [filterEq] at h
  rw [h]

theorem blockSymbol_of_nil {D : List DyBlock} {k : ℕ} (h : filterEq k D = []) :
    blockSymbol D k = TwoFactor.trivial := by
  have : blockSymbol D k = blockSymbol [] k := blockSymbol_congr (by rw [h]; rfl)
  rw [this]; rfl

theorem filterEq_lowL (c k : ℕ) (D : List DyBlock) :
    filterEq k (lowL c D) = if k ≤ c then filterEq k D else [] := by
  unfold filterEq lowL
  rw [List.filter_filter]
  split_ifs with hk
  · refine List.filter_congr fun b _ => ?_
    by_cases hb : blockExp b = (k : ℤ)
    · simp [hb, show (k : ℤ) ≤ c by exact_mod_cast hk]
    · simp [hb]
  · rw [List.filter_eq_nil_iff]
    intro b _ hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    have : (k : ℤ) ≤ c := hb.1 ▸ hb.2
    exact hk (by exact_mod_cast this)

theorem filterEq_highL (c k : ℕ) (D : List DyBlock) :
    filterEq k (highL c D) = if k ≤ c then [] else filterEq k D := by
  unfold filterEq highL
  rw [List.filter_filter]
  split_ifs with hk
  · rw [List.filter_eq_nil_iff]
    intro b _ hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    have : (c : ℤ) < k := hb.1 ▸ hb.2
    have : c < k := by exact_mod_cast this
    omega
  · refine List.filter_congr fun b _ => ?_
    by_cases hb : blockExp b = (k : ℤ)
    · simp [hb, show (c : ℤ) < k by exact_mod_cast (show c < k by omega)]
    · simp [hb]

theorem blockSymbol_lowL (c : ℕ) (D : List DyBlock) : blockSymbol (lowL c D) = lowS c (blockSymbol D) := by
  funext k
  unfold lowS glueS
  split_ifs with hk
  · exact blockSymbol_congr (by rw [filterEq_lowL, if_pos hk])
  · exact blockSymbol_of_nil (by rw [filterEq_lowL, if_neg hk])

theorem blockSymbol_highL (c : ℕ) (D : List DyBlock) : blockSymbol (highL c D) = highS c (blockSymbol D) := by
  funext k
  unfold highS glueS
  split_ifs with hk
  · exact blockSymbol_of_nil (by rw [filterEq_highL, if_pos hk])
  · exact blockSymbol_congr (by rw [filterEq_highL, if_neg hk])

/-- **The symbol of a concatenation separated at $c$ is glued at $c$.** -/
theorem blockSymbol_append {c : ℕ} {A B : List DyBlock} (hA : ∀ b ∈ A, blockExp b ≤ c)
    (hB : ∀ b ∈ B, (c : ℤ) < blockExp b) : blockSymbol (A ++ B) = glueS c (blockSymbol A) (blockSymbol B) := by
  funext k
  unfold glueS
  split_ifs with hk
  · refine blockSymbol_congr ?_
    unfold filterEq
    have hnil : List.filter (fun b => decide (blockExp b = (k : ℤ))) B = [] :=
      List.filter_eq_nil_iff.2 (fun b hb hbk => by
        have h1 := hB b hb
        simp only [decide_eq_true_eq] at hbk
        rw [hbk] at h1
        have : c < k := by exact_mod_cast h1
        omega)
    rw [List.filter_append, hnil, List.append_nil]
  · refine blockSymbol_congr ?_
    unfold filterEq
    have hnil : List.filter (fun b => decide (blockExp b = (k : ℤ))) A = [] :=
      List.filter_eq_nil_iff.2 (fun b hb hbk => by
        have h1 := hA b hb
        simp only [decide_eq_true_eq] at hbk
        rw [hbk] at h1
        have : k ≤ c := by exact_mod_cast h1
        omega)
    rw [List.filter_append, hnil, List.nil_append]

theorem lowL_append_highL (c : ℕ) (D : List DyBlock) :
    blockSymbol (lowL c D ++ highL c D) = blockSymbol D := by
  rw [blockSymbol_append (c := c) (fun b hb => (mem_lowL.1 hb).2) (fun b hb => (mem_highL.1 hb).2),
    blockSymbol_lowL, blockSymbol_highL, glueS_low_high]

/-- **The symbol of a shifted list is the shifted symbol.** -/
theorem blockSymbol_shiftL {D : List DyBlock} (h0 : ∀ b ∈ D, 0 ≤ blockExp b) :
    blockSymbol (shiftL D) = shS (blockSymbol D) := by
  funext k
  cases k with
  | zero =>
    refine blockSymbol_of_nil (List.filter_eq_nil_iff.2 fun b hb hbk => ?_)
    obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
    simp only [blockExp_shift1, decide_eq_true_eq] at hbk
    have := h0 b' hb'
    push_cast at hbk
    omega
  | succ k =>
    rw [shS_succ]
    have e : filterEq (k + 1) (shiftL D) = (filterEq k D).map shift1 := by
      unfold filterEq shiftL
      rw [List.filter_map]
      congr 1
      refine List.filter_congr fun b _ => ?_
      simp only [Function.comp, blockExp_shift1]
      push_cast
      simp
    unfold blockSymbol
    simp only [filterEq] at e
    rw [e]
    simp only [List.map_map, Function.comp_def, dim_shift1, blockSign_shift1, blockOddity_shift1, List.any_map]
    congr 2
    simp [isSqBlock_shift1]

/-! ### Rank, valuation and unit of concatenations and shifts -/

theorem dyDim_append : ∀ (A B : List DyBlock), dyDim (A ++ B) = dyDim A + dyDim B
  | [], B => by simp [dyDim]
  | b :: A, B => by simp only [List.cons_append, dyDim, dyDim_append A B]; ring

theorem valSum_append (A B : List DyBlock) : valSum (A ++ B) = valSum A + valSum B := by
  simp [valSum]

theorem unitProd_append (A B : List DyBlock) : unitProd (A ++ B) = unitProd A * unitProd B := by
  simp [unitProd]

theorem dyDim_shiftL : ∀ (D : List DyBlock), dyDim (shiftL D) = dyDim D
  | [] => rfl
  | b :: D => by simp only [shiftL, List.map_cons, dyDim, dim_shift1]; rw [← shiftL, dyDim_shiftL D]

theorem dyDim_eq_sum_dim : ∀ (D : List DyBlock), dyDim D = (D.map DyBlock.dim).sum
  | [] => rfl
  | b :: D => by simp [dyDim, dyDim_eq_sum_dim D]

theorem valSum_shiftL {D : List DyBlock} (h0 : ∀ b ∈ D, 0 ≤ blockExp b) :
    valSum (shiftL D) = valSum D + dyDim D := by
  induction D with
  | nil => rfl
  | cons b D ih =>
    have hb := h0 b (List.mem_cons_self ..)
    have ih' := ih fun c hc => h0 c (List.mem_cons_of_mem _ hc)
    simp only [valSum, shiftL, List.map_cons, List.sum_cons, dim_shift1, blockExp_shift1, dyDim] at ih' ⊢
    rw [ih', show (blockExp b + 1).toNat = (blockExp b).toNat + 1 by omega]
    ring

theorem unitProd_shiftL (D : List DyBlock) : unitProd (shiftL D) = unitProd D := by
  simp [unitProd, shiftL, Function.comp_def]

/-- The rank is the sum of the dimensions of the constituents of the symbol, below any bound of the exponents. -/
theorem dyDim_eq_sum {D : List DyBlock} (h0 : ∀ b ∈ D, 0 ≤ blockExp b) {N : ℕ}
    (hN : ∀ b ∈ D, blockExp b < N) : dyDim D = ∑ k ∈ range N, (blockSymbol D k).dim := by
  induction D with
  | nil => simp [dyDim, blockSymbol]
  | cons b D ih =>
    have hb0 := h0 b (List.mem_cons_self ..)
    have hbN := hN b (List.mem_cons_self ..)
    rw [dyDim, ih (fun c hc => h0 c (List.mem_cons_of_mem _ hc)) (fun c hc => hN c (List.mem_cons_of_mem _ hc))]
    have e : ∀ k, (blockSymbol (b :: D) k).dim = (if blockExp b = (k : ℤ) then b.dim else 0) +
        (blockSymbol D k).dim := by
      intro k
      simp only [blockSymbol, List.filter_cons]
      split_ifs with h1 h2 h2
      · simp
      · simp at h1; exact absurd h1 h2
      · simp at h1; exact absurd h2 h1
      · simp
    simp only [e, Finset.sum_add_distrib]
    congr 1
    obtain ⟨m, hm⟩ : ∃ m : ℕ, blockExp b = m := ⟨(blockExp b).toNat, by omega⟩
    have hmN : m < N := by rw [hm] at hbN; exact_mod_cast hbN
    rw [Finset.sum_eq_single m]
    · simp [hm]
    · intro k _ hk; rw [if_neg]; rw [hm]; exact_mod_cast fun (h : m = k) => hk h.symm
    · intro h; exact absurd (Finset.mem_range.2 hmN) h

/-! ### Hasse invariants -/

theorem hasseList_append : ∀ (l₁ l₂ : List (ℕ × ZMod 8)),
    hasseList (l₁ ++ l₂) = hasseList l₁ * hasseList l₂ * (l₁.map fun a => (l₂.map (hilb2 a)).prod).prod
  | [], l₂ => by simp [hasseList]
  | a :: l₁, l₂ => by
    simp only [List.cons_append, hasseList, List.map_append, List.prod_append, hasseList_append l₁ l₂,
      List.map_cons, List.prod_cons]
    ring

/-- The sums $\sum\alpha$, $\sum\varepsilon(u)$, $\sum\omega(u)$ over a list of entries $(\alpha, u)$. -/
def sA (l : List (ℕ × ZMod 8)) : ℕ := (l.map Prod.fst).sum
/-- See `sA`. -/
def sE (l : List (ℕ × ZMod 8)) : ℕ := (l.map fun a => twoEps a.2).sum
/-- See `sA`. -/
def sW (l : List (ℕ × ZMod 8)) : ℕ := (l.map fun a => twoOmega a.2).sum

theorem prod_neg_one_pow {α : Type*} (l : List α) (f : α → ℕ) :
    (l.map fun a => ((-1 : ℤ) ^ f a)).prod = (-1) ^ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, pow_add]

theorem cross_prod_eq (l₁ l₂ : List (ℕ × ZMod 8)) :
    (l₁.map fun a => (l₂.map (hilb2 a)).prod).prod =
      (-1) ^ (sE l₁ * sE l₂ + sA l₁ * sW l₂ + sA l₂ * sW l₁) := by
  have h1 : ∀ a, (l₂.map (hilb2 a)).prod =
      (-1) ^ (twoEps a.2 * sE l₂ + a.1 * sW l₂ + sA l₂ * twoOmega a.2) := by
    intro a
    unfold hilb2
    rw [prod_neg_one_pow l₂ (fun b => twoEps a.2 * twoEps b.2 + a.1 * twoOmega b.2 + b.1 * twoOmega a.2)]
    congr 1
    simp only [sE, sW, sA, List.sum_map_add, List.sum_map_mul_left, List.sum_map_mul_right]
  simp only [h1]
  rw [prod_neg_one_pow]
  congr 1
  simp only [sE, sW, sA, List.sum_map_add, List.sum_map_mul_left, List.sum_map_mul_right]

theorem neg_one_pow_congr {a b : ℕ} (h : a % 2 = b % 2) : ((-1 : ℤ) ^ a) = (-1) ^ b := by
  rw [← Nat.mod_add_div a 2, ← Nat.mod_add_div b 2, h, pow_add, pow_add, pow_mul, pow_mul]
  simp

/-- The entries of a block list. -/
def entries (D : List DyBlock) : List (ℕ × ZMod 8) := D.flatMap Dyadic7.blockDiag

theorem entries_append (A B : List DyBlock) : entries (A ++ B) = entries A ++ entries B := by
  simp [entries]

theorem eps_mul (x y : ZMod 8) (hx : x = 1 ∨ x = 3 ∨ x = 5 ∨ x = 7) (hy : y = 1 ∨ y = 3 ∨ y = 5 ∨ y = 7) :
    twoEps (x * y) % 2 = (twoEps x + twoEps y) % 2 ∧ twoOmega (x * y) % 2 = (twoOmega x + twoOmega y) % 2 ∧
      (x * y = 1 ∨ x * y = 3 ∨ x * y = 5 ∨ x * y = 7) := by
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> decide

theorem blockUnit_odd8 (b : DyBlock) (hb : b.Valid) :
    ((blockUnit b : ℤ) : ZMod 8) = 1 ∨ ((blockUnit b : ℤ) : ZMod 8) = 3 ∨ ((blockUnit b : ℤ) : ZMod 8) = 5 ∨
      ((blockUnit b : ℤ) : ZMod 8) = 7 := by
  cases b with
  | sq e u => rcases hb with rfl | rfl | rfl | rfl <;> simp [blockUnit] <;> decide
  | hyp e => simp [blockUnit] <;> decide
  | ell e => simp [blockUnit] <;> decide

theorem valSum_cons (b : DyBlock) (D : List DyBlock) :
    valSum (b :: D) = b.dim * (blockExp b).toNat + valSum D := by
  simp [valSum]

theorem tE1 : twoEps (1 : ZMod 8) = 0 := by decide
theorem tE3 : twoEps (3 : ZMod 8) = 1 := by decide
theorem tE7 : twoEps (-1 : ZMod 8) = 1 := by decide
theorem tW1 : twoOmega (1 : ZMod 8) = 0 := by decide
theorem tW3 : twoOmega (3 : ZMod 8) = 1 := by decide
theorem tW7 : twoOmega (-1 : ZMod 8) = 0 := by decide

/-- The parities of $\sum\alpha$, $\sum\varepsilon$, $\sum\omega$ over the entries of an admissible list are those of
$\mathrm{val} + \dim$, $\varepsilon(\mathrm{unit})$, $\omega(\mathrm{unit})$. -/
theorem entries_parity {D : List DyBlock} (hD : AdmL D) :
    sA (entries D) % 2 = (valSum D + dyDim D) % 2 ∧
      sE (entries D) % 2 = twoEps ((unitProd D : ℤ) : ZMod 8) % 2 ∧
      sW (entries D) % 2 = twoOmega ((unitProd D : ℤ) : ZMod 8) % 2 ∧
      (((unitProd D : ℤ) : ZMod 8) = 1 ∨ ((unitProd D : ℤ) : ZMod 8) = 3 ∨ ((unitProd D : ℤ) : ZMod 8) = 5 ∨
        ((unitProd D : ℤ) : ZMod 8) = 7) := by
  induction D with
  | nil => simp [entries, sA, sE, sW, valSum, dyDim, unitProd]; decide
  | cons b D ih =>
    have hD' : AdmL D := ⟨fun c hc => hD.1 c (List.mem_cons_of_mem _ hc),
      fun c hc => hD.2.1 c (List.mem_cons_of_mem _ hc), fun c hc => hD.2.2 c (List.mem_cons_of_mem _ hc)⟩
    obtain ⟨i1, i2, i3, i4⟩ := ih hD'
    have hb := hD.1 b (List.mem_cons_self ..)
    have hb0 := hD.2.1 b (List.mem_cons_self ..)
    have hU : unitProd (b :: D) = blockUnit b * unitProd D := by simp [unitProd]
    rw [hU]
    push_cast
    obtain ⟨m1, m2, m3⟩ := eps_mul _ _ (blockUnit_odd8 b hb) i4
    have he : entries (b :: D) = Dyadic7.blockDiag b ++ entries D := by simp [entries]
    simp only [he, sA, sE, sW, List.map_append, List.sum_append] at i1 i2 i3 ⊢
    refine ⟨?_, ?_, ?_, m3⟩
    · rw [valSum_cons, dyDim]
      cases b with
      | sq e u =>
        have h1 : (DyBlock.sq e u).dim = 1 := rfl
        have h2 : blockExp (DyBlock.sq e u) = e := rfl
        simp only [h1, h2, Dyadic7.blockDiag, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hb0 ⊢
        omega
      | hyp e =>
        have h1 : (DyBlock.hyp e).dim = 2 := rfl
        have h2 : blockExp (DyBlock.hyp e) = e := rfl
        simp only [h1, h2, Dyadic7.blockDiag, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hb0 ⊢
        omega
      | ell e =>
        have h1 : (DyBlock.ell e).dim = 2 := rfl
        have h2 : blockExp (DyBlock.ell e) = e := rfl
        simp only [h1, h2, Dyadic7.blockDiag, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hb0 ⊢
        omega
    · rw [m1]
      cases b with
      | sq e u =>
        rcases hb with rfl | rfl | rfl | rfl <;> simp [Dyadic7.blockDiag, blockUnit] at i2 ⊢ <;> omega
      | hyp e => simp [Dyadic7.blockDiag, blockUnit, tE1, tE3, tE7] at i2 ⊢; omega
      | ell e => simp [Dyadic7.blockDiag, blockUnit, tE1, tE3, tE7] at i2 ⊢; omega
    · rw [m2]
      cases b with
      | sq e u =>
        rcases hb with rfl | rfl | rfl | rfl <;> simp [Dyadic7.blockDiag, blockUnit] at i3 ⊢ <;> omega
      | hyp e => simp [Dyadic7.blockDiag, blockUnit, tW1, tW3, tW7] at i3 ⊢; omega
      | ell e => simp [Dyadic7.blockDiag, blockUnit, tW1, tW3, tW7] at i3 ⊢; omega

/-- **The cross sign** of two admissible lists, as a function of (valuation, rank, unit class mod 8) of each:
$(-1)^{\varepsilon_1\varepsilon_2 + (\nu_1 + n_1)\omega_2 + (\nu_2 + n_2)\omega_1}$. -/
def crossSign (ν₁ n₁ : ℕ) (u₁ : ZMod 8) (ν₂ n₂ : ℕ) (u₂ : ZMod 8) : ℤ :=
  (-1) ^ (twoEps u₁ * twoEps u₂ + (ν₁ + n₁) * twoOmega u₂ + (ν₂ + n₂) * twoOmega u₁)

/-- **The Hasse invariant of a concatenation**: $c(A \perp B) = c(A)\,c(B)\cdot$ `crossSign`. -/
theorem hasseQ_append {A B : List DyBlock} (hA : AdmL A) (hB : AdmL B) :
    hasseQ (A ++ B) = hasseQ A * hasseQ B *
      crossSign (valSum A) (dyDim A) (unitProd A) (valSum B) (dyDim B) (unitProd B) := by
  have e : hasseQ (A ++ B) = hasseList (entries A ++ entries B) := by
    rw [← entries_append]; rfl
  rw [e, hasseList_append, cross_prod_eq]
  congr 1
  unfold crossSign
  obtain ⟨a1, a2, a3, -⟩ := entries_parity hA
  obtain ⟨b1, b2, b3, -⟩ := entries_parity hB
  refine neg_one_pow_congr ?_
  exact Nat.ModEq.add (Nat.ModEq.add (Nat.ModEq.mul a2 b2) (Nat.ModEq.mul a1 b3)) (Nat.ModEq.mul b1 a3)

theorem blockDiag_shift1 {b : DyBlock} (hb : 0 ≤ blockExp b) :
    Dyadic7.blockDiag (shift1 b) = (Dyadic7.blockDiag b).map fun a => (a.1 + 1, a.2) := by
  cases b with
  | sq e u => simp only [blockExp] at hb; simp [Dyadic7.blockDiag, shift1]; omega
  | hyp e => simp only [blockExp] at hb; simp [Dyadic7.blockDiag, shift1]; omega
  | ell e => simp only [blockExp] at hb; simp [Dyadic7.blockDiag, shift1]; omega

theorem entries_shiftL {D : List DyBlock} (h0 : ∀ b ∈ D, 0 ≤ blockExp b) :
    entries (shiftL D) = (entries D).map fun a => (a.1 + 1, a.2) := by
  induction D with
  | nil => rfl
  | cons b D ih =>
    simp only [entries, shiftL, List.map_cons, List.flatMap_cons, List.map_append] at ih ⊢
    rw [blockDiag_shift1 (h0 b (List.mem_cons_self ..)), ih fun c hc => h0 c (List.mem_cons_of_mem _ hc)]

theorem hilb2_shift2 (a b : ℕ × ZMod 8) : hilb2 (a.1 + 2, a.2) (b.1 + 2, b.2) = hilb2 a b := by
  unfold hilb2
  refine neg_one_pow_congr ?_
  simp only
  have : (a.1 + 2) * twoOmega b.2 + (b.1 + 2) * twoOmega a.2 =
      a.1 * twoOmega b.2 + b.1 * twoOmega a.2 + 2 * (twoOmega b.2 + twoOmega a.2) := by ring
  rw [add_assoc, this, ← add_assoc]
  omega

theorem hasseList_shift2 : ∀ l : List (ℕ × ZMod 8), hasseList (l.map fun a => (a.1 + 2, a.2)) = hasseList l
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, hasseList, List.map_map, hasseList_shift2 l]
    congr 2
    exact List.map_congr_left fun b _ => hilb2_shift2 a b

/-- **The Hasse invariant is invariant under a double shift** ($Q \mapsto 4Q$). -/
theorem hasseQ_shiftL_two {D : List DyBlock} (h0 : ∀ b ∈ D, 0 ≤ blockExp b) :
    hasseQ (shiftL (shiftL D)) = hasseQ D := by
  have h0' : ∀ b ∈ shiftL D, 0 ≤ blockExp b := by
    intro b hb
    obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
    rw [blockExp_shift1]; have := h0 b' hb'; omega
  show hasseList (entries (shiftL (shiftL D))) = hasseList (entries D)
  rw [entries_shiftL h0', entries_shiftL h0, List.map_map]
  exact hasseList_shift2 _

/-! ### Primitivity -/

/-- A block making $Q_D$ primitive: $2^0\cdot 2xy$, $2^0(2x^2+2xy+2y^2)$ (an odd cross coefficient) or $2^1ux^2$ (an odd
square coefficient). -/
def BlockPrim : DyBlock → Prop
  | .sq e _ => e = 1
  | .hyp e => e = 0
  | .ell e => e = 0

/-- An entry of a symmetric integer matrix witnessing an odd coefficient of the form $\tfrac12x^{\mathsf T}Mx$: a diagonal
entry not divisible by $4$ or an off-diagonal entry not divisible by $2$. -/
def BadEntry {m : ℕ} (M : Matrix (Fin m) (Fin m) ℤ) : Prop :=
  ∃ i j, (i = j ∧ ¬ (4 : ℤ) ∣ M i j) ∨ (i ≠ j ∧ ¬ (2 : ℤ) ∣ M i j)

theorem badEntry_orthSum {a b : ℕ} (F : Matrix (Fin a) (Fin a) ℤ) (G : Matrix (Fin b) (Fin b) ℤ) :
    BadEntry (orthSumMat F G) ↔ BadEntry F ∨ BadEntry G := by
  unfold BadEntry orthSumMat
  constructor
  · rintro ⟨i, j, h⟩
    obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      (finSumFinEquiv.injective).eq_iff] at h
    rcases x with x | x <;> rcases y with y | y
    · left; refine ⟨x, y, ?_⟩; simpa [Matrix.fromBlocks_apply₁₁] using h
    · simp [Matrix.fromBlocks_apply₁₂] at h
    · simp [Matrix.fromBlocks_apply₂₁] at h
    · right; refine ⟨x, y, ?_⟩; simpa [Matrix.fromBlocks_apply₂₂] using h
  · rintro (⟨x, y, h⟩ | ⟨x, y, h⟩)
    · refine ⟨finSumFinEquiv (Sum.inl x), finSumFinEquiv (Sum.inl y), ?_⟩
      simpa [Matrix.reindex_apply, (finSumFinEquiv.injective).eq_iff] using h
    · refine ⟨finSumFinEquiv (Sum.inr x), finSumFinEquiv (Sum.inr y), ?_⟩
      simpa [Matrix.reindex_apply, (finSumFinEquiv.injective).eq_iff] using h

theorem two_pow_mul_odd_dvd {k : ℕ} {u : ℤ} (hu : ¬ (2 : ℤ) ∣ u) (m : ℕ) :
    (2 : ℤ) ^ m ∣ 2 ^ k * u ↔ m ≤ k := by
  constructor
  · intro h
    by_contra hmk
    have h1 : (2 : ℤ) ^ (k + 1) ∣ 2 ^ k * u := (pow_dvd_pow 2 (by omega)).trans h
    rw [pow_succ] at h1
    exact hu ((mul_dvd_mul_iff_left (pow_ne_zero k two_ne_zero)).1 h1)
  · intro h; exact (pow_dvd_pow 2 h).mul_right u

theorem badEntry_fin_one (M : Matrix (Fin 1) (Fin 1) ℤ) : BadEntry M ↔ ¬ (4 : ℤ) ∣ M 0 0 := by
  simp [BadEntry, Fin.exists_fin_one]

theorem badEntry_fin_two (M : Matrix (Fin 2) (Fin 2) ℤ) :
    BadEntry M ↔ ¬ (4 : ℤ) ∣ M 0 0 ∨ ¬ (4 : ℤ) ∣ M 1 1 ∨ ¬ (2 : ℤ) ∣ M 0 1 ∨ ¬ (2 : ℤ) ∣ M 1 0 := by
  simp only [BadEntry, Fin.exists_fin_two, Fin.isValue, true_and, ne_eq, Fin.reduceEq, not_false_eq_true,
    false_and, or_false, false_or, not_true_eq_false]
  tauto

theorem badEntry_block (b : DyBlock) (hb : b.Valid) (h0 : 0 ≤ blockExp b) (hev : ¬ IsOddUnimodBlock b) :
    BadEntry (blockMatInt b) ↔ BlockPrim b := by
  have two_dvd_pow : ∀ k : ℕ, (2 : ℤ) ∣ 2 ^ k ↔ k ≠ 0 := by
    intro k
    have := two_pow_mul_odd_dvd (k := k) (u := 1) (by decide) 1
    simp only [pow_one, mul_one] at this
    rw [this]; omega
  have four_dvd_pow : ∀ k : ℕ, (4 : ℤ) ∣ 2 ^ (k + 1) ↔ k ≠ 0 := by
    intro k
    have := two_pow_mul_odd_dvd (k := k + 1) (u := 1) (by decide) 2
    simp only [mul_one] at this
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, this]; omega
  cases b with
  | sq e u =>
    simp only [blockExp] at h0
    have he : e ≠ 0 := hev
    have hu : ¬ (2 : ℤ) ∣ u := by rcases hb with rfl | rfl | rfl | rfl <;> decide
    have key : ¬ (4 : ℤ) ∣ 2 ^ e.toNat * u ↔ e = 1 := by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, two_pow_mul_odd_dvd hu]; omega
    refine (badEntry_fin_one _).trans ?_
    exact key
  | hyp e =>
    simp only [blockExp] at h0
    refine (badEntry_fin_two _).trans ?_
    show (¬ (4 : ℤ) ∣ 0 ∨ ¬ (4 : ℤ) ∣ 0 ∨ ¬ (2 : ℤ) ∣ 2 ^ e.toNat ∨ ¬ (2 : ℤ) ∣ 2 ^ e.toNat) ↔ e = 0
    simp only [dvd_zero, not_true_eq_false, false_or, two_dvd_pow, not_not, or_self]
    omega
  | ell e =>
    simp only [blockExp] at h0
    refine (badEntry_fin_two _).trans ?_
    show (¬ (4 : ℤ) ∣ 2 ^ (e.toNat + 1) ∨ ¬ (4 : ℤ) ∣ 2 ^ (e.toNat + 1) ∨ ¬ (2 : ℤ) ∣ 2 ^ e.toNat ∨
      ¬ (2 : ℤ) ∣ 2 ^ e.toNat) ↔ e = 0
    simp only [four_dvd_pow, two_dvd_pow, not_not, or_self, ne_eq]
    omega

theorem badEntry_dyMatInt : ∀ (D : List DyBlock), AdmL D → (BadEntry (dyMatInt D) ↔ ∃ b ∈ D, BlockPrim b)
  | [], _ => by
    constructor
    · rintro ⟨i, _⟩
      exact absurd i.2 (by simp [dyDim])
    · rintro ⟨x, hx, _⟩
      exact absurd hx (by simp)
  | b :: D, hD => by
    have hD' : AdmL D := ⟨fun c hc => hD.1 c (List.mem_cons_of_mem _ hc),
      fun c hc => hD.2.1 c (List.mem_cons_of_mem _ hc), fun c hc => hD.2.2 c (List.mem_cons_of_mem _ hc)⟩
    show BadEntry (orthSumMat (blockMatInt b) (dyMatInt D)) ↔ _
    rw [badEntry_orthSum, badEntry_block b (hD.1 b (List.mem_cons_self ..)) (hD.2.1 b (List.mem_cons_self ..))
      (hD.2.2 b (List.mem_cons_self ..)), badEntry_dyMatInt D hD']
    constructor
    · rintro (h | ⟨x, hx, h⟩)
      · exact ⟨b, List.mem_cons_self .., h⟩
      · exact ⟨x, List.mem_cons_of_mem _ hx, h⟩
    · rintro ⟨x, hx, h⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Or.inl h
      · exact Or.inr ⟨x, hx, h⟩

/-- **Primitivity of $Q_D$**: some coefficient of $Q_D$ is odd iff some block is $2^0\cdot2xy$,
$2^0(2x^2+2xy+2y^2)$ or $2^1ux^2$. -/
theorem isPrimBlocks_iff {D : List DyBlock} (hD : AdmL D) : IsPrimBlocks D ↔ ∃ b ∈ D, BlockPrim b := by
  rw [← badEntry_dyMatInt D hD]
  have hM : hessZ (dyDim D) D = dyMatInt D := by
    rw [hessZ_of rfl]; ext i j; simp
  have hsymm : ∀ i j, dyMatInt D i j = dyMatInt D j i := fun i j => by
    have := congrFun (congrFun (transpose_dyMatInt D) j) i
    simpa [Matrix.transpose_apply] using this
  have hev := even_dyMatInt_diag D hD.2.1 hD.2.2
  unfold IsPrimBlocks BadEntry formZ
  simp only [QuadForm.ofUpper, Matrix.of_apply, hM]
  constructor
  · rintro ⟨i, j, h⟩
    by_cases hij : i ≤ j
    · rw [if_pos hij] at h
      by_cases hij' : i = j
      · subst hij'
        rw [if_pos rfl] at h
        refine ⟨i, i, Or.inl ⟨rfl, fun h4 => h ?_⟩⟩
        obtain ⟨m, hm⟩ := h4
        exact ⟨m, by omega⟩
      · rw [if_neg hij'] at h
        exact ⟨i, j, Or.inr ⟨hij', h⟩⟩
    · rw [if_neg hij] at h; exact absurd (dvd_zero _) h
  · rintro ⟨i, j, (⟨rfl, h⟩ | ⟨hij, h⟩)⟩
    · refine ⟨i, i, ?_⟩
      rw [if_pos le_rfl, if_pos rfl]
      intro h2
      obtain ⟨m, hm⟩ := h2
      obtain ⟨k, hk⟩ := hev i
      exact h ⟨m, by omega⟩
    · rcases le_or_gt i j with hle | hlt
      · refine ⟨i, j, ?_⟩
        rw [if_pos hle, if_neg hij]; exact h
      · refine ⟨j, i, ?_⟩
        rw [if_pos hlt.le, if_neg (Ne.symm hij), ← hsymm]; exact h

end QuadFormsKB.Hanke2011Structure.RatTwo
