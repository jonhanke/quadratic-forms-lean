/-
# Hanke 2011, §5 and §7: Jordan block structures and partial local genus symbols

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`).

Indices are 0-based in Lean (the paper's $n_1,\dots,n_r$ are `blocks.blocks[0]`, ..., `blocks.blocks[r-1]`).

* `JordanBlockStructure n` (Definition 5.1, case $p \nmid 2$): a tuple $(n_1,\dots,n_r)$ of positive integers with
  $n_1+\cdots+n_r = n$, $r$ not specified; this is exactly Mathlib's `Composition n`. The blocks are the dimensions
  of the Jordan constituents, in order of strictly decreasing scale.
* `card_jordanBlockStructure` (Remark 5.3): there are $2^{n-1}$ of them for $n \ge 1$; in Lean `n - 1` is
  truncated subtraction, so for $n = 0$ the formula gives $2^0 = 1$, which is correct: the empty tuple is the unique
  Jordan block structure of size $0$ (the paper's $2^{n-1}$ is only meaningful for $n \ge 1$).
  `card_jordanBlockStructure_succ` is the recursion $J(n) = \sum_{i=0}^{n-1} J(i)$ (stated as
  $J(n+1) = \sum_{i=0}^{n} J(i)$), with $J(0) = J(1) = 1$.
* `PartialLocalGenusSymbol n` (Definition 5.1, case $p \mid 2$, $F_p = \mathbb{Q}_2$): a Jordan block structure
  with a separator (`Separator`: comma, semicolon, double colon) between adjacent blocks, and an optional bar on each
  even block, with the semicolon allowed only between two unbarred blocks.
* `lemma_7_1_jordanBlockStructure`, `lemma_7_1_partialLocalGenusSymbol` (Lemma 7.1): for $n=2$ there are exactly
  $2$ Jordan block structures and $5$ partial local genus symbols.
* `exampleSymbol`: the paper's example $(1; 2, 1, \bar 2, 1 :: 3)$ is a partial local genus symbol of size $10$.
-/
import Mathlib
import QuadFormsKB.Citation

namespace QuadFormsKB.Hanke2011Structure

open Finset

/-- **Jordan block structure of size $n$** (Hanke 2011, Def. 5.1, case $p \nmid 2$): a tuple $(n_1,\dots,n_r)$ of
positive integers $n_i$ with $n_1+\cdots+n_r = n$ ($r$ not specified). Implemented as Mathlib's `Composition n`;
`c.blocks` is the list $(n_1,\dots,n_r)$ (0-based in Lean), the dimensions of the Jordan constituents in order of
strictly decreasing scale. -/
@[kb "hanke2011structure" "Def. 5.1, p. 22"]
abbrev JordanBlockStructure (n : ℕ) : Type := Composition n

/-- **Remark 5.3** (Hanke 2011, p. 23): there are exactly $2^{n-1}$ Jordan block structures of size $n \ge 1$,
i.e. $|\{(n_1,\dots,n_r) : n_i \ge 1,\ \sum n_i = n\}| = 2^{n-1}$. -/
@[kb "hanke2011structure" "Rem. 5.3, p. 23"]
theorem card_jordanBlockStructure (n : ℕ) (_hn : 1 ≤ n) :
    Fintype.card (JordanBlockStructure n) = 2 ^ (n - 1) :=
  composition_card n

/-- **Remark 5.3** (Hanke 2011, p. 23), recursion: with $J(n)$ the number of Jordan block structures of size $n$,
$J(n) = \sum_{i=0}^{n-1} J(i)$ for $n \ge 1$ (here stated as $J(n+1) = \sum_{i=0}^{n} J(i)$). -/
@[kb "hanke2011structure" "Rem. 5.3, p. 23"]
theorem card_jordanBlockStructure_succ (n : ℕ) :
    Fintype.card (JordanBlockStructure (n + 1)) =
      ∑ i ∈ Finset.range (n + 1), Fintype.card (JordanBlockStructure i) := by
  simp only [JordanBlockStructure, composition_card]
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp only [Nat.add_sub_cancel]
    cases m with
    | zero => simp
    | succ k => simp [pow_succ]; ring

/-- **Remark 5.3** (Hanke 2011, p. 23), initial values: $J(0) = J(1) = 1$ (the empty tuple, resp. $(1)$). -/
@[kb "hanke2011structure" "Rem. 5.3, p. 23"]
theorem card_jordanBlockStructure_zero_one :
    Fintype.card (JordanBlockStructure 0) = 1 ∧ Fintype.card (JordanBlockStructure 1) = 1 := by
  simp [JordanBlockStructure, composition_card]

/-- A **separator** between two adjacent blocks of a partial local genus symbol (Hanke 2011, Def. 5.1(1)):
a comma `,`, a semicolon `;`, or a pair of colons `::`. -/
inductive Separator
  /-- The comma `,`. -/
  | comma
  /-- The semicolon `;` (allowed only between two unbarred blocks). -/
  | semicolon
  /-- The pair of colons `::`. -/
  | doubleColon
  deriving DecidableEq, Repr

/-- The three separators, as a `Fintype`. -/
instance : Fintype Separator :=
  ⟨{Separator.comma, Separator.semicolon, Separator.doubleColon}, by intro x; cases x <;> simp⟩

/-- **Partial local genus symbol of size $n$** (Hanke 2011, Def. 5.1, case $p \mid 2$, $F_p = \mathbb{Q}_2$):
a Jordan block structure $(n_1,\dots,n_r)$ of size $n$ in which
1. each of the $r-1$ separators between adjacent blocks is `,`, `;` or `::`;
2. each even $n_i$ may carry a bar $\bar n_i$ (odd blocks may not);
3. the separator `;` may appear only between two adjacent unbarred numbers.

*Remark 5.2 (not formalized):* these are the data of Conway–Sloane 2-adic genus symbols without the sign and
oddity: `::` separates trains, barred numbers are type II blocks, `;` separates compartments.

Fields (all 0-based): `blocks` is $(n_1,\dots,n_r)$; `seps` has length $r-1$ and `seps[i]` is the separator between
blocks $i$ and $i+1$; `bars` has length $r$ and `bars[i] = true` means block $i$ is barred. -/
@[kb "hanke2011structure" "Def. 5.1, p. 22"]
structure PartialLocalGenusSymbol (n : ℕ) where
  /-- The underlying Jordan block structure $(n_1,\dots,n_r)$. -/
  blocks : JordanBlockStructure n
  /-- The separators between adjacent blocks. -/
  seps : List Separator
  /-- Which blocks carry a bar. -/
  bars : List Bool
  /-- There is one separator between each pair of adjacent blocks: $r-1$ in total. -/
  seps_length : seps.length = blocks.length - 1
  /-- There is one bar flag per block. -/
  bars_length : bars.length = blocks.length
  /-- Condition (2): only even blocks may be barred. -/
  bar_even : ∀ i : ℕ, bars[i]? = some true → ∃ b ∈ blocks.blocks[i]?, Even b
  /-- Condition (3): a semicolon at position $i$ requires blocks $i$ and $i+1$ both unbarred. -/
  semicolon_unbarred : ∀ i : ℕ, seps[i]? = some Separator.semicolon →
    bars[i]? = some false ∧ bars[i + 1]? = some false

namespace PartialLocalGenusSymbol

variable {n : ℕ}

/-- Raw data of a symbol, before imposing conditions (2) and (3): a composition, a vector of separators and a vector
of bar flags of the correct lengths. A finite type. -/
abbrev Data (n : ℕ) : Type :=
  Σ c : Composition n, List.Vector Separator (c.length - 1) × List.Vector Bool c.length

/-- Conditions (2) and (3) of Def. 5.1 on raw data. -/
def Valid {n : ℕ} (d : Data n) : Prop :=
  (∀ i : ℕ, d.2.2.1[i]? = some true → ∃ b ∈ d.1.blocks[i]?, Even b) ∧
  (∀ i : ℕ, d.2.1.1[i]? = some Separator.semicolon →
    d.2.2.1[i]? = some false ∧ d.2.2.1[i + 1]? = some false)

instance {n : ℕ} (d : Data n) : Decidable (Valid d) := by
  have hs : d.2.1.1.length ≤ d.1.length := by rw [d.2.1.2]; omega
  have hb : d.2.2.1.length = d.1.length := d.2.2.2
  refine decidable_of_iff
    ((∀ i < d.1.length + 1, d.2.2.1[i]? = some true → ∃ b ∈ d.1.blocks[i]?, Even b) ∧
     (∀ i < d.1.length + 1, d.2.1.1[i]? = some Separator.semicolon →
       d.2.2.1[i]? = some false ∧ d.2.2.1[i + 1]? = some false)) ?_
  unfold Valid
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · by_cases hlt : i < d.1.length + 1
      · exact h1 i hlt hi
      · rw [List.getElem?_eq_none (by omega)] at hi
        simp at hi
    · by_cases hlt : i < d.1.length + 1
      · exact h2 i hlt hi
      · rw [List.getElem?_eq_none (by omega)] at hi
        simp at hi
  · rintro ⟨h1, h2⟩
    exact ⟨fun i _ hi => h1 i hi, fun i _ hi => h2 i hi⟩

/-- Symbols of size $n$ are exactly the valid raw data. -/
def equivValid {n : ℕ} : PartialLocalGenusSymbol n ≃ {d : Data n // Valid d} where
  toFun s := ⟨⟨s.blocks, ⟨s.seps, s.seps_length⟩, ⟨s.bars, s.bars_length⟩⟩,
    s.bar_even, s.semicolon_unbarred⟩
  invFun d := ⟨d.1.1, d.1.2.1.1, d.1.2.2.1, d.1.2.1.2, d.1.2.2.2, d.2.1, d.2.2⟩
  left_inv s := rfl
  right_inv := by
    rintro ⟨⟨c, ⟨s, hs⟩, ⟨b, hb⟩⟩, hv⟩
    rfl

instance : Fintype (PartialLocalGenusSymbol n) :=
  Fintype.ofEquiv _ equivValid.symm

end PartialLocalGenusSymbol

/-- **Lemma 7.1** (Hanke 2011, p. 27), first half: for $n=2$ there are exactly two Jordan block structures,
$\{(2), (1,1)\}$. -/
@[kb "hanke2011structure" "Lemma 7.1, p. 27"]
theorem lemma_7_1_jordanBlockStructure : Fintype.card (JordanBlockStructure 2) = 2 := by
  simpa using composition_card 2

/-- The two compositions of $2$, $(2)$ and $(1,1)$, are distinct. -/
theorem composition_two_ne :
    Composition.single 2 (by norm_num) ≠ Composition.ones 2 := by
  intro h
  have := congrArg Composition.length h
  simp at this

/-- The compositions of $2$ are exactly $(2)$ and $(1,1)$. -/
theorem univ_composition_two : (Finset.univ : Finset (Composition 2)) =
    {Composition.single 2 (by norm_num), Composition.ones 2} := by
  symm
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [Finset.card_univ, composition_card, Finset.card_pair composition_two_ne]
  norm_num

/-- **Lemma 7.1** (Hanke 2011, p. 27), second half: for $n=2$ there are exactly five partial local genus symbols,
$\{(\bar 2), (2), (1,1), (1;1), (1::1)\}$. -/
@[kb "hanke2011structure" "Lemma 7.1, p. 27"]
theorem lemma_7_1_partialLocalGenusSymbol : Fintype.card (PartialLocalGenusSymbol 2) = 5 := by
  rw [Fintype.card_congr PartialLocalGenusSymbol.equivValid, Fintype.card_subtype, Finset.card_filter,
    ← Finset.univ_sigma_univ, Finset.sum_sigma, univ_composition_two, Finset.sum_pair composition_two_ne]
  decide +kernel

/-- The paper's example $(1; 2, 1, \bar 2, 1 :: 3)$ (Hanke 2011, Def. 5.1, p. 22) is a partial local genus symbol
of size $10$. -/
@[kb "hanke2011structure" "Def. 5.1, p. 22"]
def exampleSymbol : PartialLocalGenusSymbol 10 where
  blocks := ⟨[1, 2, 1, 2, 1, 3], by decide, by decide⟩
  seps := [.semicolon, .comma, .comma, .comma, .doubleColon]
  bars := [false, false, false, true, false, false]
  seps_length := by decide
  bars_length := by decide
  bar_even := by
    intro i h
    rcases i with _ | _ | _ | _ | _ | _ | i <;> simp_all
  semicolon_unbarred := by
    intro i h
    rcases i with _ | _ | _ | _ | _ | i <;> simp_all

end QuadFormsKB.Hanke2011Structure
