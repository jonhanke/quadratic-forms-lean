/-
# Conway–Sloane, Ch. 15, §7.6: the canonical 2-adic symbol

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §7.6, p. 382
(`conwaysloane1999`).

Conway–Sloane: by sign walking at most one minus sign remains in each train, placed on the earliest
nonzero-dimensional form of the train; by oddity fusion only the total oddity of each compartment is recorded. The
result is unique and is the canonical symbol: two forms are 2-adically equivalent iff their canonical symbols agree.

**Defines** (for a 2-adic symbol $\sigma$ whose forms are of type II beyond some scale, `EventuallyTypeII`)
* `trainStart`, `trainEnd`: the first and last scale of the train of $2^k$; `canonPos`: the earliest
  nonzero-dimensional form of the train (the last form of the train if all have dimension $0$, which happens for valid
  symbols only for a single zero-dimensional form, whose sign is $+$);
* `trainOdd`: the train of $2^k$ contains an odd number of minus signs;
* `compStart`, `compEnd`: the first and last scale of the compartment of a type I form;
* `canonical σ hσ`: the canonical symbol: same dimensions and types, signs $+$ except a $-$ at `canonPos` of each train
  with `trainOdd`, oddity $0$ at the type I forms other than the first of their compartment, and at the first form the
  value that keeps the compartment invariant (that is, the compartment's total oddity after the walks).

**Proves**
* `sameInvariants_canonical`: $\sigma$ and its canonical symbol have the same invariants, so
  `moveEquiv_canonical`: they are related by sign walking and oddity fusion;
* `canonical_eq_of_sameInvariants`: the canonical symbol depends only on the invariants;
* `moveEquiv_iff_canonical_eq` (**§7.6**): $\sigma \sim \tau$ under the moves iff their canonical symbols are equal.
-/
import QuadFormsKB.Literature.ConwaySloane.Symbol

namespace QuadFormsKB.ConwaySloane

open Finset Classical

noncomputable section

/-- The forms of $\sigma$ are of type II from some scale on (true for the symbol of a form: beyond its last Jordan
constituent every constituent is zero-dimensional, of type II). -/
def EventuallyTypeII (σ : TwoSymbol) : Prop := ∃ B, ∀ k, B ≤ k → ¬ IsTypeI σ k

variable (σ : TwoSymbol)

/-! ### Trains and compartments located -/

/-- The first scale of the train of $2^k$: the largest $s \le k$ with $s = 0$ or a train boundary after $2^{s-1}$. -/
def trainStart (k : ℕ) : ℕ := Nat.findGreatest (fun s => s = 0 ∨ IsBoundary σ (s - 1)) k

/-- The first scale of the compartment of $2^k$ (for $2^k$ of type I): the largest $s \le k$ with $s = 0$ or
$2^{s-1}$ of type II. -/
def compStart (k : ℕ) : ℕ := Nat.findGreatest (fun s => s = 0 ∨ ¬ IsTypeI σ (s - 1)) k

variable {σ}

theorem EventuallyTypeII.exists_boundary (hσ : EventuallyTypeII σ) (k : ℕ) : ∃ e, k ≤ e ∧ IsBoundary σ e := by
  obtain ⟨B, hB⟩ := hσ
  exact ⟨max k B, le_max_left _ _, hB _ (le_max_right _ _), hB _ (by omega)⟩

theorem EventuallyTypeII.exists_typeII (hσ : EventuallyTypeII σ) (k : ℕ) :
    ∃ e, k ≤ e ∧ ¬ IsTypeI σ (e + 1) := by
  obtain ⟨B, hB⟩ := hσ
  exact ⟨max k B, le_max_left _ _, hB _ (by omega)⟩

/-- The last scale of the train of $2^k$: the first train boundary at or after $k$. -/
def trainEnd (hσ : EventuallyTypeII σ) (k : ℕ) : ℕ := Nat.find (hσ.exists_boundary k)

/-- The last scale of the compartment of $2^k$: the first $e \ge k$ with $2^{e+1}$ of type II. -/
def compEnd (hσ : EventuallyTypeII σ) (k : ℕ) : ℕ := Nat.find (hσ.exists_typeII k)

theorem EventuallyTypeII.exists_canonPos (hσ : EventuallyTypeII σ) (k : ℕ) :
    ∃ x, trainStart σ k ≤ x ∧ ((σ x).dim ≠ 0 ∨ x = trainEnd hσ k) :=
  ⟨trainEnd hσ k, by
    have := Nat.findGreatest_le (P := fun s => s = 0 ∨ IsBoundary σ (s - 1)) k
    have := (Nat.find_spec (hσ.exists_boundary k)).1
    exact le_trans ‹_› (by simpa [trainEnd] using this), Or.inr rfl⟩

/-- The **canonical position** of the train of $2^k$ (Conway–Sloane, §7.6, p. 382): its earliest nonzero-dimensional
form (or its last form if every form of the train is zero-dimensional). -/
def canonPos (hσ : EventuallyTypeII σ) (k : ℕ) : ℕ := Nat.find (hσ.exists_canonPos k)

/-- The train of $2^k$ contains an odd number of minus signs. -/
def trainOdd (hσ : EventuallyTypeII σ) (k : ℕ) : Prop :=
  (minusBelow σ (trainEnd hσ k + 1) + minusBelow σ (trainStart σ k)) % 2 = 1

/-- The signs of the **canonical 2-adic symbol** (Conway–Sloane, §7.6, p. 382). -/
def canonicalSign (hσ : EventuallyTypeII σ) (k : ℕ) : Sign :=
  if k = canonPos hσ k ∧ trainOdd hσ k then .minus else .plus

/-- The number of minus signs below $2^y$ in the canonical symbol. -/
def canonMinusBelow (hσ : EventuallyTypeII σ) : ℕ → ℕ
  | 0 => 0
  | y + 1 => canonMinusBelow hσ y + if canonicalSign hσ y = .minus then 1 else 0

/-- The **canonical 2-adic symbol** (Conway–Sloane, §7.6, p. 382): the dimensions and types of $\sigma$; at most one
minus sign per train, on its earliest nonzero-dimensional form; the oddity of each compartment recorded on its first
form (the value keeping the compartment invariant), $0$ on the other type I forms; type II oddities unchanged. -/
@[kb "conwaysloane1999" "Ch. 15, §7.6, p. 382"]
def canonical (hσ : EventuallyTypeII σ) : TwoSymbol := fun k =>
  { dim := (σ k).dim
    sign := canonicalSign hσ k
    type := (σ k).type
    oddity :=
      if ¬ IsTypeI σ k then (σ k).oddity
      else if k = compStart σ k then
        compartmentInvariant σ k (compEnd hσ k) -
          4 * ∑ y ∈ Icc k (compEnd hσ k + 1), (canonMinusBelow hσ y : ZMod 8)
      else 0 }

/-! ### Characterizations -/

section Spec

theorem trainStart_le (k : ℕ) : trainStart σ k ≤ k := Nat.findGreatest_le k

theorem trainStart_spec (k : ℕ) : trainStart σ k = 0 ∨ IsBoundary σ (trainStart σ k - 1) :=
  Nat.findGreatest_spec (P := fun s => s = 0 ∨ IsBoundary σ (s - 1)) (Nat.zero_le k) (Or.inl rfl)

theorem not_isBoundary_of_trainStart_le {k y : ℕ} (h₁ : trainStart σ k ≤ y) (h₂ : y < k) :
    ¬ IsBoundary σ y := fun hy =>
  Nat.findGreatest_is_greatest (P := fun s => s = 0 ∨ IsBoundary σ (s - 1)) (show trainStart σ k < y + 1 by omega)
    (by omega) (Or.inr (by simpa using hy))

theorem trainStart_eq {k s : ℕ} (hs : s ≤ k) (h0 : s = 0 ∨ IsBoundary σ (s - 1))
    (hno : ∀ y, s ≤ y → y < k → ¬ IsBoundary σ y) : trainStart σ k = s := by
  have h1 : s ≤ trainStart σ k := Nat.le_findGreatest (P := fun s => s = 0 ∨ IsBoundary σ (s - 1)) hs h0
  by_contra hne
  rcases trainStart_spec (σ := σ) k with h | h
  · omega
  · exact hno _ (by omega) (by have := trainStart_le (σ := σ) k; omega) h

theorem compStart_le (k : ℕ) : compStart σ k ≤ k := Nat.findGreatest_le k

theorem compStart_spec (k : ℕ) : compStart σ k = 0 ∨ ¬ IsTypeI σ (compStart σ k - 1) :=
  Nat.findGreatest_spec (P := fun s => s = 0 ∨ ¬ IsTypeI σ (s - 1)) (Nat.zero_le k) (Or.inl rfl)

theorem compStart_eq {k s : ℕ} (hs : s ≤ k) (h0 : s = 0 ∨ ¬ IsTypeI σ (s - 1))
    (hall : ∀ y, s ≤ y → y ≤ k → IsTypeI σ y) : compStart σ k = s := by
  have h1 : s ≤ compStart σ k := Nat.le_findGreatest (P := fun s => s = 0 ∨ ¬ IsTypeI σ (s - 1)) hs h0
  by_contra hne
  rcases compStart_spec (σ := σ) k with h | h
  · omega
  · exact h (hall _ (by omega) (by have := compStart_le (σ := σ) k; omega))

variable (hσ : EventuallyTypeII σ)

theorem le_trainEnd (k : ℕ) : k ≤ trainEnd hσ k := (Nat.find_spec (hσ.exists_boundary k)).1

theorem isBoundary_trainEnd (k : ℕ) : IsBoundary σ (trainEnd hσ k) := (Nat.find_spec (hσ.exists_boundary k)).2

theorem not_isBoundary_of_lt_trainEnd {k y : ℕ} (h₁ : k ≤ y) (h₂ : y < trainEnd hσ k) : ¬ IsBoundary σ y :=
  fun hy => Nat.find_min (hσ.exists_boundary k) h₂ ⟨h₁, hy⟩

theorem trainEnd_eq {k e : ℕ} (he : k ≤ e) (hb : IsBoundary σ e) (hno : ∀ y, k ≤ y → y < e → ¬ IsBoundary σ y) :
    trainEnd hσ k = e := by
  refine le_antisymm (Nat.find_min' _ ⟨he, hb⟩) ?_
  by_contra hlt
  exact hno _ (le_trainEnd hσ k) (by omega) (isBoundary_trainEnd hσ k)

theorem le_compEnd (k : ℕ) : k ≤ compEnd hσ k := (Nat.find_spec (hσ.exists_typeII k)).1

theorem not_isTypeI_compEnd_succ (k : ℕ) : ¬ IsTypeI σ (compEnd hσ k + 1) :=
  (Nat.find_spec (hσ.exists_typeII k)).2

theorem isTypeI_of_lt_compEnd {k y : ℕ} (h₁ : k ≤ y) (h₂ : y < compEnd hσ k) : IsTypeI σ (y + 1) := by
  by_contra hy
  exact Nat.find_min (hσ.exists_typeII k) h₂ ⟨h₁, hy⟩

theorem compEnd_eq {k e : ℕ} (he : k ≤ e) (hb : ¬ IsTypeI σ (e + 1))
    (hno : ∀ y, k ≤ y → y < e → IsTypeI σ (y + 1)) : compEnd hσ k = e := by
  refine le_antisymm (Nat.find_min' _ ⟨he, hb⟩) ?_
  by_contra hlt
  exact not_isTypeI_compEnd_succ hσ k (hno _ (le_compEnd hσ k) (by omega))

/-- All forms of the train of $2^k$ have the same train. -/
theorem trainStart_trainEnd_of_mem {k x : ℕ} (h₁ : trainStart σ k ≤ x) (h₂ : x ≤ trainEnd hσ k) :
    trainStart σ x = trainStart σ k ∧ trainEnd hσ x = trainEnd hσ k := by
  constructor
  · refine trainStart_eq h₁ (trainStart_spec k) fun y hy hyx => ?_
    rcases Nat.lt_or_ge y k with h | h
    · exact not_isBoundary_of_trainStart_le hy h
    · exact not_isBoundary_of_lt_trainEnd hσ h (by omega)
  · refine trainEnd_eq hσ h₂ (isBoundary_trainEnd hσ k) fun y hy hye => ?_
    rcases Nat.lt_or_ge y k with h | h
    · exact not_isBoundary_of_trainStart_le (by omega) h
    · exact not_isBoundary_of_lt_trainEnd hσ h hye

theorem trainStart_le_canonPos (k : ℕ) : trainStart σ k ≤ canonPos hσ k := (Nat.find_spec (hσ.exists_canonPos k)).1

theorem canonPos_le_trainEnd (k : ℕ) : canonPos hσ k ≤ trainEnd hσ k :=
  Nat.find_min' _ ⟨le_trans (trainStart_le k) (le_trainEnd hσ k), Or.inr rfl⟩

theorem canonPos_congr {k x : ℕ} (hs : trainStart σ x = trainStart σ k) (he : trainEnd hσ x = trainEnd hσ k) :
    canonPos hσ x = canonPos hσ k := by
  apply le_antisymm
  · refine Nat.find_min' _ ?_
    rw [hs, he]; exact Nat.find_spec (hσ.exists_canonPos k)
  · refine Nat.find_min' _ ?_
    rw [← hs, ← he]; exact Nat.find_spec (hσ.exists_canonPos x)

/-- For a train boundary $y$, the train of $2^y$ ends at $y$. -/
theorem trainEnd_of_isBoundary {y : ℕ} (hy : IsBoundary σ y) : trainEnd hσ y = y :=
  trainEnd_eq hσ le_rfl hy fun _ h₁ h₂ => absurd h₂ (by omega)

end Spec

/-! ### Counting minus signs -/

theorem minusBelow_add (σ : TwoSymbol) (a : ℕ) : ∀ n,
    minusBelow σ (a + n) = minusBelow σ a + ∑ i ∈ range n, if (σ (a + i)).sign = .minus then 1 else 0
  | 0 => by simp
  | n + 1 => by
    rw [← add_assoc, minusBelow, minusBelow_add σ a n, Finset.sum_range_succ, add_assoc]

theorem canonMinusBelow_add {σ : TwoSymbol} (hσ : EventuallyTypeII σ) (a : ℕ) : ∀ n,
    canonMinusBelow hσ (a + n) =
      canonMinusBelow hσ a + ∑ i ∈ range n, if canonicalSign hσ (a + i) = .minus then 1 else 0
  | 0 => by simp
  | n + 1 => by
    rw [← add_assoc, canonMinusBelow, canonMinusBelow_add hσ a n, Finset.sum_range_succ, add_assoc]

theorem minusBelow_canonical {σ : TwoSymbol} (hσ : EventuallyTypeII σ) : ∀ y,
    minusBelow (canonical hσ) y = canonMinusBelow hσ y
  | 0 => rfl
  | y + 1 => by
    simp only [minusBelow, canonMinusBelow, minusBelow_canonical hσ y]
    rfl

/-- In the canonical symbol a train contains exactly `trainOdd` minus signs. -/
theorem canonMinusBelow_train {σ : TwoSymbol} (hσ : EventuallyTypeII σ) {y : ℕ} (hy : IsBoundary σ y) :
    canonMinusBelow hσ (y + 1) = canonMinusBelow hσ (trainStart σ y) + if trainOdd hσ y then 1 else 0 := by
  have hs := trainStart_le (σ := σ) y
  have hend := trainEnd_of_isBoundary hσ hy
  obtain ⟨n, hn⟩ : ∃ n, y + 1 = trainStart σ y + n := ⟨y + 1 - trainStart σ y, by omega⟩
  rw [hn, canonMinusBelow_add]
  congr 1
  have hc₁ := trainStart_le_canonPos hσ y
  have hc₂ := canonPos_le_trainEnd hσ y
  rw [hend] at hc₂
  have key : ∀ i ∈ range n, (if canonicalSign hσ (trainStart σ y + i) = .minus then 1 else 0) =
      if i = canonPos hσ y - trainStart σ y ∧ trainOdd hσ y then 1 else 0 := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    obtain ⟨hst, hen⟩ := trainStart_trainEnd_of_mem hσ (show trainStart σ y ≤ trainStart σ y + i by omega)
      (show trainStart σ y + i ≤ trainEnd hσ y by omega)
    have hcp : canonPos hσ (trainStart σ y + i) = canonPos hσ y := canonPos_congr hσ hst hen
    have hodd : trainOdd hσ (trainStart σ y + i) ↔ trainOdd hσ y := by
      unfold trainOdd; rw [hst, hen]
    have e1 : (trainStart σ y + i = canonPos hσ (trainStart σ y + i)) ↔
        (i = canonPos hσ y - trainStart σ y) := by rw [hcp]; omega
    by_cases hx : i = canonPos hσ y - trainStart σ y
    · by_cases h : trainOdd hσ y
      · have hcs : canonicalSign hσ (trainStart σ y + i) = .minus := by
          rw [canonicalSign, if_pos ⟨e1.mpr hx, hodd.mpr h⟩]
        rw [hcs, if_pos rfl, if_pos ⟨hx, h⟩]
      · have hcs : canonicalSign hσ (trainStart σ y + i) = .plus := by
          rw [canonicalSign, if_neg (fun hc => h (hodd.mp hc.2))]
        rw [hcs, if_neg (by decide), if_neg (fun hc => h hc.2)]
    · have hcs : canonicalSign hσ (trainStart σ y + i) = .plus := by
        rw [canonicalSign, if_neg (fun hc => hx (e1.mp hc.1))]
      rw [hcs, if_neg (by decide), if_neg (fun hc => hx hc.1)]
  rw [Finset.sum_congr rfl key]
  by_cases h : trainOdd hσ y
  · simp only [h, and_true]
    rw [Finset.sum_ite_eq']
    simp [show canonPos hσ y - trainStart σ y < n by omega]
  · simp [h]

theorem four_mul_eq_of_mod_two {a b : ℕ} (h : a % 2 = b % 2) : (4 * (a : ZMod 8)) = 4 * (b : ZMod 8) := by
  rw [← Nat.mod_add_div a 2, ← Nat.mod_add_div b 2, h]
  push_cast
  have : (4 * (2 : ZMod 8)) = 0 := by decide
  linear_combination (↑(a / 2) - ↑(b / 2) : ZMod 8) * this

theorem mod_two_eq_of_four_mul {a b : ℕ} (h : (4 * (a : ZMod 8)) = 4 * (b : ZMod 8)) : a % 2 = b % 2 := by
  have ha := Nat.mod_add_div a 2
  have hb := Nat.mod_add_div b 2
  have h2 : (4 * (2 : ZMod 8)) = 0 := by decide
  have e : (4 * ((a % 2 : ℕ) : ZMod 8)) = 4 * ((b % 2 : ℕ) : ZMod 8) := by
    have h' := h
    rw [← ha, ← hb] at h'
    push_cast at h'
    linear_combination h' - (↑(a / 2) - ↑(b / 2) : ZMod 8) * h2
  have := Nat.mod_lt a two_pos
  have := Nat.mod_lt b two_pos
  interval_cases (a % 2) <;> interval_cases (b % 2) <;> first | rfl | (exfalso; revert e; decide)

/-- The canonical symbol has the same sign parities below train boundaries. -/
theorem canonMinusBelow_boundary_mod_two {σ : TwoSymbol} (hσ : EventuallyTypeII σ) :
    ∀ y, IsBoundary σ y → canonMinusBelow hσ (y + 1) % 2 = minusBelow σ (y + 1) % 2 := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro hy
    have hstart : canonMinusBelow hσ (trainStart σ y) % 2 = minusBelow σ (trainStart σ y) % 2 := by
      by_cases h0 : trainStart σ y = 0
      · rw [h0]; rfl
      · rcases trainStart_spec (σ := σ) y with h | h
        · exact absurd h h0
        · have := ih (trainStart σ y - 1) (by have := trainStart_le (σ := σ) y; omega) h
          rwa [Nat.sub_add_cancel (by omega)] at this
    rw [canonMinusBelow_train hσ hy]
    have hodd : trainOdd hσ y ↔ (minusBelow σ (y + 1) + minusBelow σ (trainStart σ y)) % 2 = 1 := by
      unfold trainOdd; rw [trainEnd_of_isBoundary hσ hy]
    by_cases h : trainOdd hσ y
    · rw [if_pos h]; rw [hodd] at h; omega
    · rw [if_neg h]; rw [hodd] at h; omega

/-! ### The canonical symbol has the same invariants -/

theorem IsCompartment.compStart_eq {σ : TwoSymbol} {c₁ c₂ : ℕ} (hC : IsCompartment σ c₁ c₂) {x : ℕ}
    (h₁ : c₁ ≤ x) (h₂ : x ≤ c₂) : compStart σ x = c₁ :=
  _root_.QuadFormsKB.ConwaySloane.compStart_eq h₁ hC.2.2.1 fun y hy hyx => hC.2.1 y hy (by omega)

theorem IsCompartment.compEnd_eq {σ : TwoSymbol} (hσ : EventuallyTypeII σ) {c₁ c₂ : ℕ}
    (hC : IsCompartment σ c₁ c₂) : compEnd hσ c₁ = c₂ :=
  _root_.QuadFormsKB.ConwaySloane.compEnd_eq hσ hC.1 hC.2.2.2 fun y hy hye => hC.2.1 (y + 1) (by omega) (by omega)

/-- The compartment of a type I form that is the first of its compartment. -/
theorem isCompartment_compEnd {σ : TwoSymbol} (hσ : EventuallyTypeII σ) {k : ℕ} (hk : IsTypeI σ k)
    (hs : k = compStart σ k) : IsCompartment σ k (compEnd hσ k) := by
  refine ⟨le_compEnd hσ k, fun x hx₁ hx₂ => ?_, ?_, not_isTypeI_compEnd_succ hσ k⟩
  · rcases Nat.eq_or_lt_of_le hx₁ with rfl | hlt
    · exact hk
    · have := isTypeI_of_lt_compEnd hσ (show k ≤ x - 1 by omega) (by omega)
      rwa [Nat.sub_add_cancel (by omega)] at this
  · have := compStart_spec (σ := σ) k
    rwa [← hs] at this

theorem sameInvariants_canonical {σ : TwoSymbol} (hσ : EventuallyTypeII σ) : SameInvariants σ (canonical hσ) where
  dim_eq _ := rfl
  type_eq _ := rfl
  oddity_typeII k hk := by simp only [canonical, if_pos hk]
  boundary y hy := by
    rw [minusBelow_canonical]
    exact four_mul_eq_of_mod_two (canonMinusBelow_boundary_mod_two hσ y hy)
  compartment c₁ c₂ hC := by
    unfold compartmentInvariant
    simp only [minusBelow_canonical]
    have hmem : c₁ ∈ Icc c₁ c₂ := Finset.mem_Icc.mpr ⟨le_rfl, hC.1⟩
    rw [← Finset.add_sum_erase _ _ hmem]
    have hrest : ∑ j ∈ (Icc c₁ c₂).erase c₁, (canonical hσ j).oddity = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      obtain ⟨hne, hj'⟩ := Finset.mem_erase.mp hj
      obtain ⟨hj₁, hj₂⟩ := Finset.mem_Icc.mp hj'
      have hI : IsTypeI σ j := hC.2.1 j hj₁ hj₂
      simp only [canonical, if_neg (not_not.mpr hI), if_neg (show ¬ j = compStart σ j by
        rw [hC.compStart_eq hj₁ hj₂]; exact hne)]
    have hfirst : (canonical hσ c₁).oddity = compartmentInvariant σ c₁ c₂ -
        4 * ∑ y ∈ Icc c₁ (c₂ + 1), (canonMinusBelow hσ y : ZMod 8) := by
      have hI : IsTypeI σ c₁ := hC.2.1 c₁ le_rfl hC.1
      simp only [canonical, if_neg (not_not.mpr hI),
        if_pos (show c₁ = compStart σ c₁ from (hC.compStart_eq le_rfl hC.1).symm), hC.compEnd_eq hσ]
    rw [hrest, add_zero, hfirst]
    unfold compartmentInvariant
    ring

/-- **Every 2-adic symbol is equivalent to its canonical symbol** (Conway–Sloane, §7.6, p. 382: "Using these rules we
can arrange that there is at most one minus sign in each train …"). -/
@[kb "conwaysloane1999" "Ch. 15, §7.6, p. 382"]
theorem moveEquiv_canonical {σ : TwoSymbol} (hσ : EventuallyTypeII σ) : MoveEquiv σ (canonical hσ) := by
  obtain ⟨B, hB⟩ := hσ
  exact moveEquiv_of_sameInvariants (sameInvariants_canonical _) hB

/-! ### Uniqueness -/

section Unique

variable {σ τ : TwoSymbol} (hS : SameInvariants σ τ) (hσ : EventuallyTypeII σ) (hτ : EventuallyTypeII τ)
include hS

theorem SameInvariants.trainStart_eq (k : ℕ) : trainStart τ k = trainStart σ k :=
  _root_.QuadFormsKB.ConwaySloane.trainStart_eq (trainStart_le k)
    (by rcases trainStart_spec (σ := σ) k with h | h
        · exact Or.inl h
        · exact Or.inr ((hS.isBoundary_iff _).mpr h))
    fun y h₁ h₂ hy => not_isBoundary_of_trainStart_le h₁ h₂ ((hS.isBoundary_iff y).mp hy)

include hσ in
theorem SameInvariants.trainEnd_eq (k : ℕ) : trainEnd hτ k = trainEnd hσ k :=
  _root_.QuadFormsKB.ConwaySloane.trainEnd_eq hτ (le_trainEnd hσ k)
    ((hS.isBoundary_iff _).mpr (isBoundary_trainEnd hσ k))
    fun y h₁ h₂ hy => not_isBoundary_of_lt_trainEnd hσ h₁ h₂ ((hS.isBoundary_iff y).mp hy)

include hσ in
theorem SameInvariants.canonPos_eq (k : ℕ) : canonPos hτ k = canonPos hσ k := by
  have hs := hS.trainStart_eq k
  have he := hS.trainEnd_eq hσ hτ k
  apply le_antisymm
  · refine Nat.find_min' _ ?_
    rw [hs, he, hS.dim_eq]; exact Nat.find_spec (hσ.exists_canonPos k)
  · refine Nat.find_min' _ ?_
    rw [← hs, ← he, ← hS.dim_eq]; exact Nat.find_spec (hτ.exists_canonPos k)

theorem SameInvariants.minusBelow_trainStart_mod_two (k : ℕ) :
    minusBelow τ (trainStart σ k) % 2 = minusBelow σ (trainStart σ k) % 2 := by
  by_cases h0 : trainStart σ k = 0
  · rw [h0]; rfl
  · rcases trainStart_spec (σ := σ) k with h | h
    · exact absurd h h0
    · have := mod_two_eq_of_four_mul (hS.boundary _ h)
      rwa [Nat.sub_add_cancel (by omega)] at this

include hσ in
theorem SameInvariants.trainOdd_iff (k : ℕ) : trainOdd hτ k ↔ trainOdd hσ k := by
  unfold trainOdd
  rw [hS.trainStart_eq, hS.trainEnd_eq hσ hτ]
  have h₁ := mod_two_eq_of_four_mul (hS.boundary _ (isBoundary_trainEnd hσ k))
  have h₂ := hS.minusBelow_trainStart_mod_two k
  omega

include hσ in
theorem SameInvariants.canonicalSign_eq (k : ℕ) : canonicalSign hτ k = canonicalSign hσ k := by
  unfold canonicalSign
  rw [hS.canonPos_eq hσ hτ, ← propext (hS.trainOdd_iff hσ hτ k)]

include hσ in
theorem SameInvariants.canonMinusBelow_eq (y : ℕ) : canonMinusBelow hτ y = canonMinusBelow hσ y := by
  induction y with
  | zero => rfl
  | succ y ih => simp only [canonMinusBelow, ih, hS.canonicalSign_eq hσ hτ]

include hσ in
theorem SameInvariants.compEnd_eq (k : ℕ) : compEnd hτ k = compEnd hσ k :=
  _root_.QuadFormsKB.ConwaySloane.compEnd_eq hτ (le_compEnd hσ k)
    (by rw [hS.isTypeI_iff]; exact not_isTypeI_compEnd_succ hσ k)
    fun y h₁ h₂ => by rw [hS.isTypeI_iff]; exact isTypeI_of_lt_compEnd hσ h₁ h₂

theorem SameInvariants.compStart_eq {k : ℕ} (hk : IsTypeI σ k) (hs : k = compStart σ k) :
    compStart τ k = k := by
  refine _root_.QuadFormsKB.ConwaySloane.compStart_eq le_rfl ?_ fun y h₁ h₂ => ?_
  · have := compStart_spec (σ := σ) k
    rw [← hs] at this
    rcases this with h | h
    · exact Or.inl h
    · exact Or.inr (by rwa [hS.isTypeI_iff])
  · rw [show y = k by omega, hS.isTypeI_iff]; exact hk

include hσ in
/-- **The canonical symbol depends only on the invariants.** -/
theorem canonical_eq_of_sameInvariants : canonical hσ = canonical hτ := by
  funext k
  have hc : canonical hτ k = { canonical hτ k with } := rfl
  simp only [canonical]
  congr 1
  · exact (hS.dim_eq k).symm
  · exact (hS.canonicalSign_eq hσ hτ k).symm
  · exact (hS.type_eq k).symm
  · by_cases hI : IsTypeI σ k
    · have hIτ : IsTypeI τ k := (hS.isTypeI_iff k).mpr hI
      rw [if_neg (not_not.mpr hI), if_neg (not_not.mpr hIτ)]
      by_cases hs : k = compStart σ k
      · rw [if_pos hs, if_pos (hS.compStart_eq hI hs).symm, hS.compEnd_eq hσ hτ,
          hS.compartment _ _ (isCompartment_compEnd hσ hI hs)]
        simp only [hS.canonMinusBelow_eq hσ hτ]
      · have hsτ : ¬ k = compStart τ k := by
          intro h
          have hcomp := isCompartment_compEnd hτ hIτ h
          exact hs ((hS.isCompartment_iff _ _).mp hcomp |>.compStart_eq le_rfl
            (le_compEnd hτ k)).symm
        rw [if_neg hs, if_neg hsτ]
    · rw [if_pos hI, if_pos (fun h => hI ((hS.isTypeI_iff k).mp h)), hS.oddity_typeII k hI]

end Unique

/-- **The canonical 2-adic symbol** (Conway–Sloane, §7.6, p. 382): two 2-adic symbols are related by sign walking and
oddity fusion if and only if their canonical symbols are identical. -/
@[kb "conwaysloane1999" "Ch. 15, §7.6, p. 382"]
theorem moveEquiv_iff_canonical_eq {σ τ : TwoSymbol} (hσ : EventuallyTypeII σ) (hτ : EventuallyTypeII τ) :
    MoveEquiv σ τ ↔ canonical hσ = canonical hτ := by
  constructor
  · intro h
    exact canonical_eq_of_sameInvariants h.sameInvariants hσ hτ
  · intro h
    have h₁ := moveEquiv_canonical hσ
    have h₂ := moveEquiv_canonical hτ
    rw [h] at h₁
    exact h₁.trans _ _ _ (Relation.EqvGen.symm _ _ h₂)

end

end QuadFormsKB.ConwaySloane
