/-
# Hanke 2011, Remark 5.2: partial local genus symbols versus Conway–Sloane 2-adic symbols

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), Remark 5.2, p. 22; J. H. Conway and N. J. A. Sloane, *Sphere
Packings, Lattices and Groups*, Ch. 15, §7, pp. 378–384 (bib key `conwaysloane1999`).

**The remark.** The partial local genus symbols of Def. 5.1 (for $p = 2$, $F_p = \mathbb Q_2$) are the Conway–Sloane
2-adic symbols with the signs and oddities forgotten: `::` separates trains, a barred number $\bar n_i$ is a type II
Jordan block of dimension $n_i$ (it separates compartments iff it lies between odd, i.e. type I, blocks of one
train), and `;` separates compartments (but not trains) between type I blocks whose scales differ by a factor of $4$.

**Conventions.** Scales are $2^k$, $k \in \mathbb N$ (0-based); the blocks of a partial symbol are listed in
increasing $k$ (strictly decreasing scale ideal). A 2-adic symbol is `ConwaySloane.TwoSymbol = ℕ → TwoFactor`.
*Valid* means supported below $2^N$ (`TwoSymbol.SupportedBelow`) and every constituent satisfies the existence
conditions (32)–(35) of Conway–Sloane (`TwoFactor.Exists`): a zero-dimensional constituent is of type II with sign
$+$, a type II constituent has even dimension and oddity $0$, etc.

**Defines**
* `sepOf σ k k'`: the separator written between the nonzero constituents at the scales $2^k < 2^{k'}$
  (comma if $k' = k+1$ and not both type II; semicolon if $k' = k+2$ and both type I; double colon otherwise);
* `suppList σ N`: the scales $k < N$ of the nonzero-dimensional constituents, increasing;
* `toPartial σ N hv hn`: the partial local genus symbol of a valid 2-adic symbol (signs and oddities forgotten);
* `SameTrain σ k k'`, `SameCompartment σ k k'`: the scales $2^k \le 2^{k'}$ lie in one train, resp. one compartment
  (shown equivalent to the library's `trainStart`, `compStart`, `IsCompartment`).

**Proves**
* `toPartial_congr`: `toPartial` does not see signs or oddities; `toPartial_noBarredComma`: its image never has a
  comma between two barred blocks;
* `sepOf_doubleColon_iff`, `sepOf_semicolon_iff`, `sepOf_comma_iff`, `sepOf_semicolon_gap` (**the dictionary**):
  for consecutive nonzero constituents, `::` $\iff$ different trains; `;` $\iff$ same train, both type I, different
  compartments (and then $k' = k + 2$); `,` $\iff$ same train and (same compartment or not both type I);
  `toPartial_seps_getElem?` ties these to the actual separators of `toPartial`;
  `not_sameCompartment_iff` (two type I scales are in different compartments iff a type II or zero-dimensional
  constituent lies between them), `barred_separates_compartments`;
* `exists_toPartial_eq` (**surjectivity**, corrected): a partial local genus symbol is `toPartial` of a valid
  2-adic symbol iff it has no comma between two barred blocks (`toPartial_noBarredComma`);
* `toPartial_not_injective`, `toPartial_eq_imp` (**the precise sense of "bijective"**).

*Clarification*: the correspondence is bijective onto 2-adic
symbols without signs and oddities modulo translating trains (the absolute scales and the gaps between trains are
forgotten), and its image consists of the partial local genus symbols without a comma between two barred blocks.

**Discrepancy with the remark (found by the formalization).** Def. 5.1 allows a comma between two barred
blocks, e.g. $(\bar 2, \bar 2)$. Two type II Jordan blocks at adjacent scales $2^k$, $2^{k+1}$ are in different
trains in Conway–Sloane's sense (a train boundary is a pair of adjacent type II forms), so the corresponding
Conway–Sloane symbol is written $\bar 2 :: \bar 2$. Hence a partial symbol with a comma between two barred blocks
corresponds to no 2-adic symbol: the correspondence is onto the partial symbols *without* a comma between two
barred blocks (for $n = 2$ nothing changes: the five symbols of Lemma 7.1 all qualify).
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Hanke2011Structure.JordanSymbols
import QuadFormsKB.Literature.ConwaySloane.Existence
import QuadFormsKB.Literature.ConwaySloane.Canonical

namespace QuadFormsKB.Hanke2011Structure

open QuadFormsKB.ConwaySloane Finset

/-! ### Valid symbols, the support, and the separators -/

/-- A 2-adic symbol $\sigma$ is **valid with support below $2^N$** if all constituents of scale $\ge 2^N$ are the
trivial one ($q^{+0}$, type II) and every constituent satisfies the existence conditions (32)–(35) of
Conway–Sloane (`TwoFactor.Exists`). -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, (32)–(35), p. 383"]
def TwoSymbolValid (σ : TwoSymbol) (N : ℕ) : Prop :=
  σ.SupportedBelow N ∧ ∀ k, (σ k).Exists

/-- The scales $k < N$ at which the constituent of $\sigma$ is nonzero-dimensional, in increasing order
(0-based: the scale is $2^k$). -/
def suppList (σ : TwoSymbol) (N : ℕ) : List ℕ :=
  (List.range N).filter fun k => decide (0 < (σ k).dim)

/-- The separator between the nonzero constituents at the scales $2^k < 2^{k'}$ (Hanke 2011, Rem. 5.2):
a comma if $k' = k+1$ and the two are not both of type II; a semicolon if $k' = k+2$ and both are of type I
(their scale ideals differ by a factor of $4$); a double colon otherwise. -/
@[kb "hanke2011structure" "Rem. 5.2, p. 22"]
def sepOf (σ : TwoSymbol) (k k' : ℕ) : Separator :=
  if k' = k + 1 ∧ (IsTypeI σ k ∨ IsTypeI σ k') then Separator.comma
  else if k' = k + 2 ∧ IsTypeI σ k ∧ IsTypeI σ k' then Separator.semicolon
  else Separator.doubleColon

/-- The separators between consecutive entries of a list of scales. -/
def sepsOf (σ : TwoSymbol) : List ℕ → List Separator
  | a :: b :: t => sepOf σ a b :: sepsOf σ (b :: t)
  | _ => []

theorem length_sepsOf (σ : TwoSymbol) : ∀ l : List ℕ, (sepsOf σ l).length = l.length - 1
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
    simp only [sepsOf, List.length_cons]
    rw [length_sepsOf σ (b :: t)]
    simp

theorem sepsOf_getElem? (σ : TwoSymbol) : ∀ (l : List ℕ) (i : ℕ),
    (sepsOf σ l)[i]? = (l[i]?).bind fun a => (l[i + 1]?).map fun b => sepOf σ a b
  | [], i => by simp [sepsOf]
  | [a], i => by
    rcases i with _ | i <;> simp [sepsOf]
  | a :: b :: t, i => by
    rcases i with _ | i
    · simp [sepsOf]
    · simp only [sepsOf, List.getElem?_cons_succ]
      rw [sepsOf_getElem? σ (b :: t) i]
      simp

theorem sum_map_filter (f : ℕ → ℕ) : ∀ N : ℕ,
    (((List.range N).filter fun k => decide (0 < f k)).map f).sum = ∑ k ∈ range N, f k
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, Finset.sum_range_succ,
      sum_map_filter f N]
    by_cases h : 0 < f N
    · simp [h]
    · have : f N = 0 := by omega
      simp [this]

/-- The Jordan block structure of a 2-adic symbol: the dimensions of the nonzero constituents in increasing
order of the exponent $k$. -/
def blocksOf (σ : TwoSymbol) (N n : ℕ) (hn : ∑ k ∈ range N, (σ k).dim = n) : Composition n where
  blocks := (suppList σ N).map fun k => (σ k).dim
  blocks_pos := by
    intro i hi
    simp only [suppList, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
    obtain ⟨k, ⟨_, hk⟩, rfl⟩ := hi
    exact hk
  blocks_sum := by
    rw [suppList, sum_map_filter (fun k => (σ k).dim) N, hn]

theorem suppList_pairwise (σ : TwoSymbol) (N : ℕ) : (suppList σ N).Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range

theorem mem_suppList {σ : TwoSymbol} {N k : ℕ} : k ∈ suppList σ N ↔ k < N ∧ 0 < (σ k).dim := by
  simp [suppList]

/-- The (nonzero-dimensional) scales $k < k'$ are **consecutive**: no scale strictly between them carries a nonzero
constituent. -/
def Consecutive (σ : TwoSymbol) (k k' : ℕ) : Prop :=
  k < k' ∧ 0 < (σ k).dim ∧ 0 < (σ k').dim ∧ ∀ m, k < m → m < k' → (σ m).dim = 0

theorem suppList_consecutive (σ : TwoSymbol) (N : ℕ) {i a b : ℕ}
    (ha : (suppList σ N)[i]? = some a) (hb : (suppList σ N)[i + 1]? = some b) : Consecutive σ a b := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.mp hb
  have hp := List.pairwise_iff_getElem.mp (suppList_pairwise σ N)
  have hmem := fun j (hj : j < (suppList σ N).length) =>
    (mem_suppList (σ := σ)).mp (List.getElem_mem hj)
  refine ⟨hp i (i + 1) hi hi' (by omega), (hmem i hi).2, (hmem (i + 1) hi').2, fun m h1 h2 => ?_⟩
  by_contra hne
  have hm : m ∈ suppList σ N := mem_suppList.mpr ⟨by have := (hmem (i + 1) hi').1; omega, by omega⟩
  obtain ⟨j, hj, hjm⟩ := List.getElem_of_mem hm
  rcases Nat.lt_or_ge i j with h | h
  · have : i + 1 ≤ j := h
    rcases Nat.eq_or_lt_of_le this with e | e
    · subst e; omega
    · have := hp (i + 1) j hi' hj e
      omega
  · rcases Nat.eq_or_lt_of_le h with e | e
    · subst e; omega
    · have := hp j i hj hi e
      omega

/-! ### The partial local genus symbol of a 2-adic symbol -/

/-- **The partial local genus symbol of a valid 2-adic symbol** (Hanke 2011, Rem. 5.2, p. 22): list the
nonzero-dimensional constituents in increasing $k$ (scale $2^k$); the block dimensions are the $n_q$; a block is
barred iff it has type II; the separator between consecutive blocks at the scales $2^k < 2^{k'}$ is `sepOf σ k k'`.
Signs and oddities are forgotten (`toPartial_congr`). The dimension is $n = \sum_{k < N} n_{2^k}$
(hypothesis `hn`). -/
@[kb "hanke2011structure" "Rem. 5.2, p. 22"]
def toPartial (σ : TwoSymbol) (N n : ℕ) (hv : TwoSymbolValid σ N)
    (hn : ∑ k ∈ range N, (σ k).dim = n) : PartialLocalGenusSymbol n where
  blocks := blocksOf σ N n hn
  seps := sepsOf σ (suppList σ N)
  bars := (suppList σ N).map fun k => decide ((σ k).type = .II)
  seps_length := by
    rw [length_sepsOf]
    simp [blocksOf, Composition.length]
  bars_length := by
    simp [Composition.length, blocksOf]
  bar_even := by
    intro i hi
    rw [List.getElem?_map] at hi
    obtain ⟨k, hk, hk2⟩ : ∃ k, (suppList σ N)[i]? = some k ∧ (σ k).type = .II := by
      cases h : (suppList σ N)[i]? with
      | none => simp [h] at hi
      | some k => simp [h] at hi; exact ⟨k, rfl, hi⟩
    refine ⟨(σ k).dim, ?_, ?_⟩
    · simp [blocksOf, List.getElem?_map, hk]
    · by_contra hodd
      have h1 : (σ k).dim % 2 = 1 := by
        rcases Nat.even_or_odd (σ k).dim with h | h
        · exact absurd h hodd
        · exact Nat.odd_iff.mp h
      have := (hv.2 k).typeI_of_odd h1
      rw [hk2] at this
      exact absurd this (by decide)
  semicolon_unbarred := by
    intro i hi
    change (sepsOf σ (suppList σ N))[i]? = some Separator.semicolon at hi
    rw [sepsOf_getElem?] at hi
    obtain ⟨a, ha, b, hb, hab⟩ : ∃ a, (suppList σ N)[i]? = some a ∧ ∃ b, (suppList σ N)[i + 1]? = some b ∧
        sepOf σ a b = Separator.semicolon := by
      cases h : (suppList σ N)[i]? with
      | none => simp [h] at hi
      | some a =>
        cases h' : (suppList σ N)[i + 1]? with
        | none => simp [h, h'] at hi
        | some b => simp [h, h'] at hi; exact ⟨a, rfl, b, rfl, hi⟩
    have hI : IsTypeI σ a ∧ IsTypeI σ b := by
      unfold sepOf at hab
      split_ifs at hab with h1 h2
      exact ⟨h2.2.1, h2.2.2⟩
    have h1 : (σ a).type = .I := hI.1
    have h2 : (σ b).type = .I := hI.2
    constructor
    · simp [List.getElem?_map, ha, h1]
    · simp [List.getElem?_map, hb, h2]

theorem partial_ext {n : ℕ} {s t : PartialLocalGenusSymbol n} (h1 : s.blocks.blocks = t.blocks.blocks)
    (h2 : s.seps = t.seps) (h3 : s.bars = t.bars) : s = t := by
  cases s with
  | mk b1 s1 r1 _ _ _ _ =>
  cases t with
  | mk b2 s2 r2 _ _ _ _ =>
  have := Composition.ext h1
  subst this
  dsimp only at h2 h3
  subst h2
  subst h3
  rfl

/-- **Signs and oddities are forgotten**: two 2-adic symbols with the same dimensions and the same scaled types
have the same partial local genus symbol. -/
@[kb "hanke2011structure" "Rem. 5.2, p. 22"]
theorem toPartial_congr {σ τ : TwoSymbol} {N n : ℕ} (hσ : TwoSymbolValid σ N) (hτ : TwoSymbolValid τ N)
    (hσn : ∑ k ∈ range N, (σ k).dim = n) (hτn : ∑ k ∈ range N, (τ k).dim = n)
    (hdim : ∀ k, (σ k).dim = (τ k).dim) (htype : ∀ k, (σ k).type = (τ k).type) :
    toPartial σ N n hσ hσn = toPartial τ N n hτ hτn := by
  have hs : suppList σ N = suppList τ N := by simp only [suppList, hdim]
  have hI : ∀ k, IsTypeI σ k ↔ IsTypeI τ k := fun k => by simp only [IsTypeI, htype]
  have hsep : ∀ l, sepsOf σ l = sepsOf τ l := by
    intro l
    induction l with
    | nil => rfl
    | cons a t ih =>
      cases t with
      | nil => rfl
      | cons b t' =>
        simp only [sepsOf, sepOf, hI] at ih ⊢
        rw [ih]
  apply partial_ext
  · simp only [toPartial, blocksOf, hs, hdim]
  · simp only [toPartial, hs, hsep]
  · simp only [toPartial, hs, htype]

/-- No comma between two barred blocks (Hanke 2011, Def. 5.1 allows such commas, but they correspond to no
Conway–Sloane symbol: see the discrepancy in the file header). -/
def PartialLocalGenusSymbol.NoBarredComma {n : ℕ} (s : PartialLocalGenusSymbol n) : Prop :=
  ∀ i : ℕ, s.seps[i]? = some Separator.comma → ¬ (s.bars[i]? = some true ∧ s.bars[i + 1]? = some true)

theorem toPartial_seps_getElem? {σ : TwoSymbol} {N n : ℕ} (hv : TwoSymbolValid σ N)
    (hn : ∑ k ∈ range N, (σ k).dim = n) {i a b : ℕ} (ha : (suppList σ N)[i]? = some a)
    (hb : (suppList σ N)[i + 1]? = some b) :
    (toPartial σ N n hv hn).seps[i]? = some (sepOf σ a b) := by
  change (sepsOf σ (suppList σ N))[i]? = _
  rw [sepsOf_getElem?, ha, hb]
  rfl

/-- The image of `toPartial` has no comma between two barred blocks. -/
@[kb "hanke2011structure" "Rem. 5.2, p. 22"]
theorem toPartial_noBarredComma {σ : TwoSymbol} {N n : ℕ} (hv : TwoSymbolValid σ N)
    (hn : ∑ k ∈ range N, (σ k).dim = n) : (toPartial σ N n hv hn).NoBarredComma := by
  intro i hi
  change (sepsOf σ (suppList σ N))[i]? = some Separator.comma at hi
  rw [sepsOf_getElem?] at hi
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a, (suppList σ N)[i]? = some a ∧ ∃ b, (suppList σ N)[i + 1]? = some b ∧
      sepOf σ a b = Separator.comma := by
    cases h : (suppList σ N)[i]? with
    | none => simp [h] at hi
    | some a =>
      cases h' : (suppList σ N)[i + 1]? with
      | none => simp [h, h'] at hi
      | some b => simp [h, h'] at hi; exact ⟨a, rfl, b, rfl, hi⟩
  have hI : IsTypeI σ a ∨ IsTypeI σ b := by
    unfold sepOf at hab
    split_ifs at hab with h1
    exact h1.2
  rintro ⟨h1, h2⟩
  change ((suppList σ N).map fun k => decide ((σ k).type = .II))[i]? = some true at h1
  change ((suppList σ N).map fun k => decide ((σ k).type = .II))[i + 1]? = some true at h2
  simp only [List.getElem?_map, ha, hb, Option.map_some, Option.some.injEq, decide_eq_true_eq] at h1 h2
  rcases hI with h | h
  · have : (σ a).type = .I := h
    rw [this] at h1; exact absurd h1 (by decide)
  · have : (σ b).type = .I := h
    rw [this] at h2; exact absurd h2 (by decide)

/-! ### Trains and compartments (Conway–Sloane, §7.5) -/

/-- The scales $2^k \le 2^{k'}$ lie in **one train**: no train boundary after $2^m$ for $k \le m < k'$
(Conway–Sloane, §7.5, p. 381; `IsBoundary σ m` says that $2^m$ and $2^{m+1}$ are both of type II). -/
@[kb "conwaysloane1999" "Ch. 15, §7.5, p. 381 (train)"]
def SameTrain (σ : TwoSymbol) (k k' : ℕ) : Prop := ∀ m, k ≤ m → m < k' → ¬ IsBoundary σ m

/-- The scales $2^k \le 2^{k'}$ lie in **one compartment**: all forms of scales $2^x$, $k \le x \le k'$, are of
type I (Conway–Sloane, §7.5, p. 381; see `sameCompartment_iff`). -/
@[kb "conwaysloane1999" "Ch. 15, §7.5, p. 381 (compartment)"]
def SameCompartment (σ : TwoSymbol) (k k' : ℕ) : Prop := ∀ x, k ≤ x → x ≤ k' → IsTypeI σ x

/-- `SameTrain` is the library's notion: $2^k$ and $2^{k'}$ are in one train iff the train of $2^{k'}$ starts at
or before $2^k$ (`trainStart`). -/
theorem sameTrain_iff_trainStart_le (σ : TwoSymbol) {k k' : ℕ} (_h : k ≤ k') :
    SameTrain σ k k' ↔ trainStart σ k' ≤ k := by
  constructor
  · intro hs
    by_contra hlt
    push Not at hlt
    rcases trainStart_spec (σ := σ) k' with h0 | hb
    · omega
    · exact hs (trainStart σ k' - 1) (by omega) (by have := trainStart_le (σ := σ) k'; omega) hb
  · intro hs m h1 h2
    exact not_isBoundary_of_trainStart_le (by omega) h2

theorem isTypeI_of_compStart_le {σ : TwoSymbol} {k : ℕ} (hk : IsTypeI σ k) :
    ∀ d y : ℕ, y + d = k → compStart σ k ≤ y → IsTypeI σ y := by
  intro d
  induction d with
  | zero => intro y hy _; rw [show y = k by omega]; exact hk
  | succ d ih =>
    intro y hy hs
    have h1 := ih (y + 1) (by omega) (by
      by_contra hlt
      push Not at hlt
      have := compStart_le (σ := σ) k
      omega)
    by_contra hn
    have := Nat.le_findGreatest (P := fun s => s = 0 ∨ ¬ IsTypeI σ (s - 1)) (show y + 1 ≤ k by omega)
      (Or.inr (by simpa using hn))
    have h2 : y + 1 ≤ compStart σ k := this
    omega

/-- `SameCompartment` is the library's notion: for $k \le k'$ the scales $2^k$, $2^{k'}$ are in one compartment
(an `IsCompartment σ c₁ c₂` with $c_1 \le k$ and $k' \le c_2$) iff all forms between them are of type I. -/
theorem sameCompartment_iff {σ : TwoSymbol} (hσ : EventuallyTypeII σ) {k k' : ℕ} (hkk : k ≤ k') :
    SameCompartment σ k k' ↔ ∃ c₁ c₂, IsCompartment σ c₁ c₂ ∧ c₁ ≤ k ∧ k' ≤ c₂ := by
  constructor
  · intro h
    have hk : IsTypeI σ k := h k le_rfl hkk
    have hk' : IsTypeI σ k' := h k' hkk le_rfl
    refine ⟨compStart σ k, compEnd hσ k', ⟨?_, fun x hx1 hx2 => ?_, compStart_spec k,
      not_isTypeI_compEnd_succ hσ k'⟩, compStart_le k, le_compEnd hσ k'⟩
    · have := compStart_le (σ := σ) k
      have := le_compEnd hσ k'
      omega
    · by_cases hxk : x ≤ k
      · exact isTypeI_of_compStart_le hk (k - x) x (by omega) hx1
      · by_cases hxk' : x ≤ k'
        · exact h x (by omega) hxk'
        · have := isTypeI_of_lt_compEnd hσ (show k' ≤ x - 1 by omega) (by omega)
          rwa [Nat.sub_add_cancel (by omega)] at this
  · rintro ⟨c₁, c₂, hC, h1, h2⟩ x hx1 hx2
    exact hC.2.1 x (by omega) (by omega)

theorem eventuallyTypeII_of_valid {σ : TwoSymbol} {N : ℕ} (hv : TwoSymbolValid σ N) : EventuallyTypeII σ :=
  ⟨N, fun k hk => by
    unfold IsTypeI
    rw [hv.1 k hk]
    simp [TwoFactor.trivial]⟩

theorem not_isTypeI_of_dim_eq_zero {σ : TwoSymbol} (hv : ∀ k, (σ k).Exists) {m : ℕ} (h : (σ m).dim = 0) :
    ¬ IsTypeI σ m := by
  intro hI
  have h2 := ((hv m).1 h).1
  unfold IsTypeI at hI
  rw [h2] at hI
  exact absurd hI (by decide)

/-- **Same train, for consecutive nonzero constituents** at $2^k < 2^{k'}$ of a valid symbol: they lie in one
train iff $k' = k+1$ and not both are of type II, or $k' = k+2$ and both are of type I (the zero-dimensional
constituent between them is of type II). -/
theorem sameTrain_iff {σ : TwoSymbol} (hv : ∀ k, (σ k).Exists) {k k' : ℕ} (hc : Consecutive σ k k') :
    SameTrain σ k k' ↔
      (k' = k + 1 ∧ (IsTypeI σ k ∨ IsTypeI σ k')) ∨ (k' = k + 2 ∧ IsTypeI σ k ∧ IsTypeI σ k') := by
  obtain ⟨hlt, -, -, hz⟩ := hc
  have hmid : ∀ m, k < m → m < k' → ¬ IsTypeI σ m := fun m h1 h2 =>
    not_isTypeI_of_dim_eq_zero hv (hz m h1 h2)
  unfold SameTrain IsBoundary
  constructor
  · intro h
    by_cases e1 : k' = k + 1
    · left
      refine ⟨e1, ?_⟩
      by_contra hn
      push Not at hn
      exact h k le_rfl (by omega) ⟨hn.1, by rw [← e1]; exact hn.2⟩
    by_cases e2 : k' = k + 2
    · right
      refine ⟨e2, ?_, ?_⟩
      · by_contra hn
        exact h k le_rfl (by omega) ⟨hn, hmid (k + 1) (by omega) (by omega)⟩
      · by_contra hn
        exact h (k + 1) (by omega) (by omega)
          ⟨hmid (k + 1) (by omega) (by omega), by rw [show k + 1 + 1 = k' by omega]; exact hn⟩
    · exfalso
      exact h (k + 1) (by omega) (by omega)
        ⟨hmid (k + 1) (by omega) (by omega), hmid (k + 1 + 1) (by omega) (by omega)⟩
  · rintro (⟨e, hI⟩ | ⟨e, h1, h2⟩) m hm1 hm2 ⟨hb1, hb2⟩
    · have : m = k := by omega
      rw [this] at hb1 hb2
      rw [← e] at hb2
      rcases hI with h | h
      · exact hb1 h
      · exact hb2 h
    · by_cases hmk : m = k
      · rw [hmk] at hb1; exact hb1 h1
      · have : m + 1 = k' := by omega
        rw [this] at hb2
        exact hb2 h2

/-! ### The dictionary -/

/-- **Dictionary (a)**: for consecutive nonzero constituents of a valid symbol, the separator is a double colon iff
they lie in different trains. -/
@[kb "hanke2011structure" "Rem. 5.2, p. 22"]
theorem sepOf_doubleColon_iff {σ : TwoSymbol} (hv : ∀ k, (σ k).Exists) {k k' : ℕ} (hc : Consecutive σ k k') :
    sepOf σ k k' = Separator.doubleColon ↔ ¬ SameTrain σ k k' := by
  rw [sameTrain_iff hv hc]
  unfold sepOf
  by_cases hA : k' = k + 1 ∧ (IsTypeI σ k ∨ IsTypeI σ k') <;>
    by_cases hB : k' = k + 2 ∧ IsTypeI σ k ∧ IsTypeI σ k' <;> simp [hA, hB]

/-- **Dictionary (b)**: for consecutive nonzero constituents of a valid symbol, the separator is a semicolon iff
they lie in the same train, both are of type I, and they lie in different compartments. -/
@[kb "hanke2011structure" "Rem. 5.2, p. 22"]
theorem sepOf_semicolon_iff {σ : TwoSymbol} (hv : ∀ k, (σ k).Exists) {k k' : ℕ} (hc : Consecutive σ k k') :
    sepOf σ k k' = Separator.semicolon ↔
      SameTrain σ k k' ∧ IsTypeI σ k ∧ IsTypeI σ k' ∧ ¬ SameCompartment σ k k' := by
  have hmid : ∀ m, k < m → m < k' → ¬ IsTypeI σ m := fun m h1 h2 =>
    not_isTypeI_of_dim_eq_zero hv (hc.2.2.2 m h1 h2)
  rw [sameTrain_iff hv hc]
  constructor
  · intro h
    unfold sepOf at h
    split_ifs at h with h1 h2
    refine ⟨Or.inr h2, h2.2.1, h2.2.2, fun hs => hmid (k + 1) (by omega) (by omega)
      (hs (k + 1) (by omega) (by omega))⟩
  · rintro ⟨hts, hI1, hI2, hnc⟩
    rcases hts with ⟨e, _⟩ | ⟨e2, _, _⟩
    · exfalso
      apply hnc
      intro x hx1 hx2
      by_cases hxk : x = k
      · rw [hxk]; exact hI1
      · rw [show x = k' by omega]; exact hI2
    · unfold sepOf
      subst e2
      simp [hI1, hI2]

/-- **Dictionary (b'), the factor of 4**: a semicolon is written only between scales $2^k$, $2^{k+2}$ whose
scale ideals differ by the factor $4$. -/
@[kb "hanke2011structure" "Rem. 5.2, p. 22"]
theorem sepOf_semicolon_gap {σ : TwoSymbol} {k k' : ℕ} (h : sepOf σ k k' = Separator.semicolon) :
    k' = k + 2 := by
  unfold sepOf at h
  split_ifs at h with h1 h2
  exact h2.1

/-- **Dictionary (c)**: for consecutive nonzero constituents of a valid symbol, the separator is a comma iff they
lie in the same train and (are in the same compartment, or are not both of type I). -/
@[kb "hanke2011structure" "Rem. 5.2, p. 22"]
theorem sepOf_comma_iff {σ : TwoSymbol} (hv : ∀ k, (σ k).Exists) {k k' : ℕ} (hc : Consecutive σ k k') :
    sepOf σ k k' = Separator.comma ↔
      SameTrain σ k k' ∧ (SameCompartment σ k k' ∨ ¬ (IsTypeI σ k ∧ IsTypeI σ k')) := by
  have hmid : ∀ m, k < m → m < k' → ¬ IsTypeI σ m := fun m h1 h2 =>
    not_isTypeI_of_dim_eq_zero hv (hc.2.2.2 m h1 h2)
  rw [sameTrain_iff hv hc]
  constructor
  · intro h
    unfold sepOf at h
    split_ifs at h with h1
    refine ⟨Or.inl h1, ?_⟩
    by_cases hb : IsTypeI σ k ∧ IsTypeI σ k'
    · left
      intro x hx1 hx2
      by_cases hxk : x = k
      · rw [hxk]; exact hb.1
      · rw [show x = k' by omega]; exact hb.2
    · right; exact hb
  · rintro ⟨hts, hr⟩
    rcases hts with h1 | ⟨e2, hI1, hI2⟩
    · obtain ⟨e, hI⟩ := h1
      subst e
      unfold sepOf
      simp [hI]
    · exfalso
      rcases hr with hs | hn
      · exact hmid (k + 1) (by omega) (by omega) (hs (k + 1) (by omega) (by omega))
      · exact hn ⟨hI1, hI2⟩

/-- **The dictionary for `toPartial`** (Hanke 2011, Rem. 5.2, p. 22): if the blocks $i$ and $i+1$ of
`toPartial σ N n hv hn` sit at the scales $2^a < 2^b$, then the separator `s` between them satisfies
* `s` is `::` iff $a$, $b$ lie in different trains;
* `s` is `;` iff $a$, $b$ lie in one train, both are of type I (unbarred), and in different compartments;
  then $b = a + 2$ (the scales differ by a factor of $4$);
* `s` is `,` iff $a$, $b$ lie in one train and (one compartment or not both of type I). -/
@[kb "hanke2011structure" "Rem. 5.2, p. 22"]
theorem toPartial_dictionary {σ : TwoSymbol} {N n : ℕ} (hv : TwoSymbolValid σ N)
    (hn : ∑ k ∈ range N, (σ k).dim = n) {i a b : ℕ} (ha : (suppList σ N)[i]? = some a)
    (hb : (suppList σ N)[i + 1]? = some b) {s : Separator}
    (hs : (toPartial σ N n hv hn).seps[i]? = some s) :
    (s = Separator.doubleColon ↔ ¬ SameTrain σ a b) ∧
    (s = Separator.semicolon ↔ SameTrain σ a b ∧ IsTypeI σ a ∧ IsTypeI σ b ∧ ¬ SameCompartment σ a b) ∧
    (s = Separator.semicolon → b = a + 2) ∧
    (s = Separator.comma ↔ SameTrain σ a b ∧ (SameCompartment σ a b ∨ ¬ (IsTypeI σ a ∧ IsTypeI σ b))) := by
  have hc := suppList_consecutive σ N ha hb
  rw [toPartial_seps_getElem? hv hn ha hb, Option.some.injEq] at hs
  subst hs
  exact ⟨sepOf_doubleColon_iff hv.2 hc, sepOf_semicolon_iff hv.2 hc, sepOf_semicolon_gap,
    sepOf_comma_iff hv.2 hc⟩

/-- Two type I forms at $2^k < 2^{k'}$ lie in different compartments iff some form strictly between them is of
type II (a zero-dimensional constituent of a valid symbol is of type II, so it counts too). In particular a barred
block, i.e. a nonzero type II constituent, lying strictly between two type I blocks separates their compartments
(`barred_separates_compartments`), also when the three lie in one train. -/
@[kb "hanke2011structure" "Rem. 5.2, p. 22"]
theorem not_sameCompartment_iff {σ : TwoSymbol} {k k' : ℕ} (hk : IsTypeI σ k) (hk' : IsTypeI σ k')
    (hkk : k < k') : ¬ SameCompartment σ k k' ↔ ∃ x, k < x ∧ x < k' ∧ ¬ IsTypeI σ x := by
  unfold SameCompartment
  push Not
  constructor
  · rintro ⟨x, h1, h2, h3⟩
    rcases Nat.eq_or_lt_of_le h1 with e | e
    · subst e; exact absurd hk h3
    · rcases Nat.eq_or_lt_of_le h2 with e' | e'
      · subst e'; exact absurd hk' h3
      · exact ⟨x, e, e', h3⟩
  · rintro ⟨x, h1, h2, h3⟩
    exact ⟨x, h1.le, h2.le, h3⟩

/-- A barred block between two unbarred blocks of one train separates their compartments. -/
@[kb "hanke2011structure" "Rem. 5.2, p. 22"]
theorem barred_separates_compartments {σ : TwoSymbol} {k x k' : ℕ} (hk : IsTypeI σ k) (hk' : IsTypeI σ k')
    (h1 : k < x) (h2 : x < k') (hx : (σ x).type = .II) : ¬ SameCompartment σ k k' :=
  (not_sameCompartment_iff hk hk' (h1.trans h2)).mpr ⟨x, h1, h2, by unfold IsTypeI; rw [hx]; decide⟩

/-! ### Surjectivity -/

/-- The distance between the scales of two consecutive blocks used to realize a separator: $1$ for a comma,
$2$ for a semicolon (scale ideals differing by $4$), $3$ for a double colon (a gap of three scales, which
contains two adjacent zero-dimensional type II constituents and so a train boundary). -/
def gapOf : Separator → ℕ
  | .comma => 1
  | .semicolon => 2
  | .doubleColon => 3

/-- The scales of the blocks of a symbol with separators `S`, starting at `t`. -/
def posAux : ℕ → List Separator → List ℕ
  | t, [] => [t]
  | t, s :: S => t :: posAux (t + gapOf s) S

theorem length_posAux : ∀ (S : List Separator) (t : ℕ), (posAux t S).length = S.length + 1
  | [], t => rfl
  | s :: S, t => by simp [posAux, length_posAux S]

theorem posAux_ge : ∀ (S : List Separator) (t x : ℕ), x ∈ posAux t S → t ≤ x
  | [], t, x, h => by simp [posAux] at h; omega
  | s :: S, t, x, h => by
    simp only [posAux, List.mem_cons] at h
    rcases h with rfl | h
    · exact le_rfl
    · have := posAux_ge S (t + gapOf s) x h
      omega

theorem posAux_pairwise : ∀ (S : List Separator) (t : ℕ), (posAux t S).Pairwise (· < ·)
  | [], t => by simp [posAux]
  | s :: S, t => by
    simp only [posAux, List.pairwise_cons]
    refine ⟨fun x hx => ?_, posAux_pairwise S _⟩
    have := posAux_ge S (t + gapOf s) x hx
    have : 1 ≤ gapOf s := by cases s <;> simp [gapOf]
    omega

theorem posAux_getElem?_zero (S : List Separator) (t : ℕ) : (posAux t S)[0]? = some t := by
  cases S <;> simp [posAux]

theorem posAux_gap : ∀ (S : List Separator) (t i x y : ℕ), (posAux t S)[i]? = some x →
    (posAux t S)[i + 1]? = some y → ∃ s, S[i]? = some s ∧ y = x + gapOf s
  | [], t, i, x, y, hx, hy => by
    simp only [posAux] at hy
    rw [List.getElem?_eq_none (by simp)] at hy
    simp at hy
  | s :: S, t, i, x, y, hx, hy => by
    rcases i with _ | i
    · rw [posAux_getElem?_zero] at hx
      have hy' : (posAux (t + gapOf s) S)[0]? = some y := hy
      rw [posAux_getElem?_zero] at hy'
      cases hx; cases hy'
      exact ⟨s, rfl, rfl⟩
    · exact posAux_gap S (t + gapOf s) i x y hx hy

/-- The 2-adic factor of a block of dimension `d` (barred iff `b`): sign $+$; type II with oddity $0$ if barred,
type I with oddity $d \bmod 8$ otherwise. -/
def mkFactor (d : ℕ) (b : Bool) : TwoFactor :=
  if b then ⟨d, .plus, .II, 0⟩ else ⟨d, .plus, .I, (d : ZMod 8)⟩

theorem mkFactor_exists {d : ℕ} {b : Bool} (hd : 0 < d) (hb : b = true → Even d) : (mkFactor d b).Exists := by
  cases b
  · by_cases h1 : d = 1
    · subst h1; decide
    by_cases h2 : d = 2
    · subst h2; decide
    simp only [mkFactor, Bool.false_eq_true, ite_false]
    refine ⟨fun h => by change d = 0 at h; omega, fun h => by change d = 1 at h; omega,
      fun h => by change d = 2 at h; omega, ?_, fun h => by cases h⟩
    show (d : ZMod 8).val % 2 = d % 2
    rw [ZMod.val_natCast]
    omega
  · obtain ⟨m, hm⟩ := hb rfl
    simp only [mkFactor, ite_true]
    refine ⟨fun h => by change d = 0 at h; omega, fun h => by change d = 1 at h; omega,
      fun h hI => (by cases hI), ?_, fun _ => rfl⟩
    show (0 : ZMod 8).val % 2 = d % 2
    simp
    omega

/-- A 2-adic symbol with blocks `B`, bars `Bs` at the scales `pos` (zero-dimensional type II elsewhere). -/
def symOf (B : List ℕ) (Bs : List Bool) (pos : List ℕ) : TwoSymbol := fun k =>
  if pos.idxOf k < pos.length then mkFactor (B.getD (pos.idxOf k) 0) (Bs.getD (pos.idxOf k) false)
  else TwoFactor.trivial

theorem symOf_at {B : List ℕ} {Bs : List Bool} {pos : List ℕ} (hnd : pos.Nodup) {i : ℕ} (hi : i < pos.length) :
    symOf B Bs pos pos[i] = mkFactor (B.getD i 0) (Bs.getD i false) := by
  simp [symOf, hnd.idxOf_getElem i hi, hi]

theorem symOf_not_mem {B : List ℕ} {Bs : List Bool} {pos : List ℕ} {k : ℕ} (h : k ∉ pos) :
    symOf B Bs pos k = TwoFactor.trivial := by
  have := List.idxOf_eq_length_iff.mpr h
  simp [symOf, this]

theorem take_getElem?_some {l : List ℕ} {r i x : ℕ} (h : (l.take r)[i]? = some x) : l[i]? = some x := by
  rw [List.getElem?_take] at h
  split_ifs at h
  exact h

theorem isTypeI_symOf {B : List ℕ} {Bs : List Bool} {pos : List ℕ} (hnd : pos.Nodup) {i : ℕ}
    (hi : i < pos.length) : IsTypeI (symOf B Bs pos) pos[i] ↔ Bs.getD i false = false := by
  unfold IsTypeI
  rw [symOf_at hnd hi]
  cases Bs.getD i false <;> simp [mkFactor]

/-- **The key construction** for surjectivity: for positions `pos` strictly increasing, with blocks `B` positive and
barred blocks even, `symOf B Bs pos` is valid below `pos.sum + 1`, its support list is `pos`, its blocks are `B`
and its bars are `Bs`. -/
theorem symOf_spec {B : List ℕ} {Bs : List Bool} {pos : List ℕ} (hp : pos.Pairwise (· < ·))
    (hB : B.length = pos.length) (hBs : Bs.length = pos.length) (hpos : ∀ b ∈ B, 0 < b)
    (hbar : ∀ i : ℕ, Bs[i]? = some true → ∃ b ∈ B[i]?, Even b) :
    TwoSymbolValid (symOf B Bs pos) (pos.sum + 1) ∧
    suppList (symOf B Bs pos) (pos.sum + 1) = pos ∧
    (pos.map fun k => (symOf B Bs pos k).dim) = B ∧
    (pos.map fun k => decide ((symOf B Bs pos k).type = .II)) = Bs := by
  have hnd : pos.Nodup := hp.imp (fun h => h.ne)
  have hdimB : ∀ i (hi : i < pos.length), B.getD i 0 = B[i]'(by omega) := by
    intro i hi; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < B.length by omega)]
  have hbarB : ∀ i (hi : i < pos.length), Bs.getD i false = Bs[i]'(by omega) := by
    intro i hi; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < Bs.length by omega)]
  have hexists : ∀ i (hi : i < pos.length), (mkFactor (B.getD i 0) (Bs.getD i false)).Exists := by
    intro i hi
    rw [hdimB i hi, hbarB i hi]
    refine mkFactor_exists (hpos _ (List.getElem_mem _)) fun hb => ?_
    obtain ⟨b, hb1, hb2⟩ := hbar i (by rw [List.getElem?_eq_getElem (show i < Bs.length by omega), hb])
    rw [List.getElem?_eq_getElem (show i < B.length by omega)] at hb1
    simp at hb1
    rw [hb1]; exact hb2
  have hdimpos : ∀ i (hi : i < pos.length), (symOf B Bs pos pos[i]).dim = B[i]'(by omega) := by
    intro i hi
    rw [symOf_at hnd hi, hdimB i hi]
    simp only [mkFactor]; split_ifs <;> rfl
  have hmem : ∀ k, k ∈ pos → ∃ (i : ℕ) (hi : i < pos.length), pos[i] = k := fun k hk =>
    let ⟨i, hi, e⟩ := List.getElem_of_mem hk
    ⟨i, hi, e⟩
  have hex : ∀ k, (symOf B Bs pos k).Exists := by
    intro k
    by_cases hk : k ∈ pos
    · obtain ⟨i, hi, rfl⟩ := hmem k hk
      rw [symOf_at hnd hi]
      exact hexists i hi
    · rw [symOf_not_mem hk]; decide
  have hsupp : ∀ k, k ∉ pos → (symOf B Bs pos k).dim = 0 := by
    intro k hk; rw [symOf_not_mem hk]; rfl
  have hsuppEq : suppList (symOf B Bs pos) (pos.sum + 1) = pos := by
    apply List.Pairwise.eq_of_mem_iff (suppList_pairwise _ _) hp
    intro k
    rw [mem_suppList]
    constructor
    · rintro ⟨_, hk⟩
      by_contra hk'
      rw [hsupp k hk'] at hk
      omega
    · intro hk
      obtain ⟨i, hi, rfl⟩ := hmem k hk
      refine ⟨?_, ?_⟩
      · have := List.le_sum_of_mem hk; omega
      · rw [hdimpos i hi]; exact hpos _ (List.getElem_mem _)
  refine ⟨⟨?_, hex⟩, hsuppEq, ?_, ?_⟩
  · intro k hk
    apply symOf_not_mem
    intro hmk
    have := List.le_sum_of_mem hmk
    omega
  · apply List.ext_getElem (by simp [hB])
    intro i h1 h2
    simp only [List.getElem_map]
    exact hdimpos i (by simpa using h1)
  · apply List.ext_getElem (by simp [hBs])
    intro i h1 h2
    simp only [List.getElem_map]
    have hi : i < pos.length := by simpa using h1
    rw [symOf_at hnd hi, hbarB i hi]
    simp only [mkFactor]
    cases Bs[i] <;> simp

/-- **Surjectivity, corrected** (Hanke 2011, Rem. 5.2, p. 22): every partial local genus symbol without a comma
between two barred blocks is the partial symbol `toPartial σ N n hv hn` of a valid 2-adic symbol $\sigma$ (signs
$+$, oddities $d \bmod 8$ at the type I blocks of dimension $d$, scales built greedily: gap $1$ for a comma, $2$ for
a semicolon, $3$ for a double colon). The hypothesis `NoBarredComma` cannot be dropped: see
`exists_toPartial_eq_iff`, `barredCommaExample_not_toPartial` and the file header. -/
@[kb "hanke2011structure" "Rem. 5.2, p. 22"]
theorem exists_toPartial_eq {n : ℕ} (s : PartialLocalGenusSymbol n) (hs : s.NoBarredComma) :
    ∃ (σ : TwoSymbol) (N : ℕ) (hv : TwoSymbolValid σ N) (hn : ∑ k ∈ range N, (σ k).dim = n),
      toPartial σ N n hv hn = s := by
  set B := s.blocks.blocks with hBdef
  set r := B.length with hr
  set pos := (posAux 0 s.seps).take r with hposdef
  have hlen : pos.length = r := by
    rw [hposdef, List.length_take, length_posAux]
    have := s.seps_length
    change s.seps.length = B.length - 1 at this
    omega
  have hp : pos.Pairwise (· < ·) := (posAux_pairwise s.seps 0).sublist (List.take_sublist _ _)
  have hBs : s.bars.length = pos.length := by rw [hlen]; exact s.bars_length
  obtain ⟨hv, hsupp, hbl, hba⟩ := symOf_spec (B := B) (Bs := s.bars) hp hlen.symm hBs
    (fun b hb => s.blocks.blocks_pos hb) s.bar_even
  set σ := symOf B s.bars pos with hσ
  have hn : ∑ k ∈ range (pos.sum + 1), (σ k).dim = n := by
    rw [← sum_map_filter (fun k => (σ k).dim)]
    have h2 : (suppList σ (pos.sum + 1)).map (fun k => (σ k).dim) = B := by rw [hsupp]; exact hbl
    exact (congrArg List.sum h2).trans s.blocks.blocks_sum
  refine ⟨σ, pos.sum + 1, hv, hn, partial_ext ?_ ?_ ?_⟩
  · change (suppList σ (pos.sum + 1)).map (fun k => (σ k).dim) = B
    rw [hsupp]; exact hbl
  · change sepsOf σ (suppList σ (pos.sum + 1)) = s.seps
    rw [hsupp]
    apply List.ext_getElem?
    intro i
    rw [sepsOf_getElem?]
    have hnd : pos.Nodup := hp.imp (fun h => h.ne)
    have hiff : ∀ i, i + 1 < pos.length ↔ i < s.seps.length := by
      intro i
      have := s.seps_length
      change s.seps.length = B.length - 1 at this
      omega
    by_cases hi : i + 1 < pos.length
    · have hi' := (hiff i).mp hi
      have hi0 : i < pos.length := by omega
      obtain ⟨sp, hsp⟩ : ∃ sp, s.seps[i]? = some sp := ⟨_, List.getElem?_eq_getElem hi'⟩
      rw [hsp]
      have ha : pos[i]? = some pos[i] := List.getElem?_eq_getElem hi0
      have hb : pos[i + 1]? = some pos[i + 1] := List.getElem?_eq_getElem hi
      have ha' : (posAux 0 s.seps)[i]? = some pos[i] := take_getElem?_some (r := r) (by rw [← hposdef]; exact ha)
      have hb' : (posAux 0 s.seps)[i + 1]? = some pos[i + 1] :=
        take_getElem?_some (r := r) (by rw [← hposdef]; exact hb)
      obtain ⟨s', hs', hg⟩ := posAux_gap s.seps 0 i _ _ ha' hb'
      rw [hsp] at hs'
      cases hs'
      rw [ha, hb]
      simp only [Option.bind_some, Option.map_some, Option.some.injEq]
      obtain ⟨bi, hbi⟩ : ∃ bi, s.bars[i]? = some bi := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨bj, hbj⟩ : ∃ bj, s.bars[i + 1]? = some bj := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hIa : IsTypeI σ pos[i] ↔ bi = false := by
        rw [hσ, isTypeI_symOf hnd hi0]; simp [List.getD_eq_getElem?_getD, hbi]
      have hIb : IsTypeI σ pos[i + 1] ↔ bj = false := by
        rw [hσ, isTypeI_symOf hnd hi]; simp [List.getD_eq_getElem?_getD, hbj]
      cases sp with
      | comma =>
        have hg' : pos[i + 1] = pos[i] + 1 := hg
        have hnb := hs i hsp
        unfold sepOf
        rw [hg']
        have : IsTypeI σ pos[i] ∨ IsTypeI σ (pos[i] + 1) := by
          rw [← hg', hIa, hIb]
          by_contra hcon
          push Not at hcon
          apply hnb
          exact ⟨by rw [hbi, show bi = true by simpa using hcon.1],
            by rw [hbj, show bj = true by simpa using hcon.2]⟩
        simp [this]
      | semicolon =>
        have hg' : pos[i + 1] = pos[i] + 2 := hg
        obtain ⟨h1, h2⟩ := s.semicolon_unbarred i hsp
        rw [hbi] at h1; rw [hbj] at h2
        cases h1; cases h2
        unfold sepOf
        rw [hg']
        have ha2 : IsTypeI σ pos[i] := hIa.mpr rfl
        have hb2 : IsTypeI σ (pos[i] + 2) := by rw [← hg']; exact hIb.mpr rfl
        simp [ha2, hb2]
      | doubleColon =>
        have hg' : pos[i + 1] = pos[i] + 3 := hg
        unfold sepOf
        rw [hg']
        simp
    · rw [List.getElem?_eq_none (show pos.length ≤ i + 1 by omega),
        List.getElem?_eq_none (show s.seps.length ≤ i by have := hiff i; omega)]
      cases pos[i]? <;> simp
  · change (suppList σ (pos.sum + 1)).map (fun k => decide ((σ k).type = .II)) = s.bars
    rw [hsupp]; exact hba

/-- **The image of `toPartial`** (Hanke 2011, Rem. 5.2, p. 22): a partial local genus symbol comes from a valid
2-adic symbol iff it has no comma between two barred blocks. -/
@[kb "hanke2011structure" "Rem. 5.2, p. 22"]
theorem exists_toPartial_eq_iff {n : ℕ} (s : PartialLocalGenusSymbol n) :
    (∃ (σ : TwoSymbol) (N : ℕ) (hv : TwoSymbolValid σ N) (hn : ∑ k ∈ range N, (σ k).dim = n),
      toPartial σ N n hv hn = s) ↔ s.NoBarredComma := by
  constructor
  · rintro ⟨σ, N, hv, hn, rfl⟩
    exact toPartial_noBarredComma hv hn
  · exact exists_toPartial_eq s

/-- The partial local genus symbol $(\bar 2, \bar 2)$ of size $4$ (a comma between two barred blocks). It satisfies
Def. 5.1 of Hanke 2011, but corresponds to no Conway–Sloane symbol (that would be $\bar 2 :: \bar 2$). -/
def barredCommaExample : PartialLocalGenusSymbol 4 where
  blocks := ⟨[2, 2], by decide, by decide⟩
  seps := [.comma]
  bars := [true, true]
  seps_length := by decide
  bars_length := by decide
  bar_even := by
    intro i h
    rcases i with _ | _ | i <;> simp_all
  semicolon_unbarred := by
    intro i h
    rcases i with _ | i <;> simp_all

/-- **The discrepancy**: $(\bar 2, \bar 2)$ is a partial local genus symbol in the sense of Def. 5.1 but not the
partial symbol of any valid 2-adic symbol. -/
@[kb "hanke2011structure" "Rem. 5.2, p. 22"]
theorem barredCommaExample_not_toPartial :
    ¬ ∃ (σ : TwoSymbol) (N : ℕ) (hv : TwoSymbolValid σ N) (hn : ∑ k ∈ range N, (σ k).dim = 4),
      toPartial σ N 4 hv hn = barredCommaExample := by
  rw [exists_toPartial_eq_iff]
  intro h
  exact h 0 rfl ⟨rfl, rfl⟩

/-! ### Injectivity up to translation of trains -/

theorem sepOf_comma_gap {σ : TwoSymbol} {k k' : ℕ} (h : sepOf σ k k' = Separator.comma) : k' = k + 1 := by
  unfold sepOf at h
  split_ifs at h with h1
  exact h1.1

/-- **The precise sense of "bijective"** (Hanke 2011, Rem. 5.2, p. 22). If two valid 2-adic symbols have the same
partial local genus symbol, then they have the same number of nonzero constituents, the same dimensions and the
same scaled types (type II = barred) in the same order, the same separators, and the same scale difference
$k_{i+1} - k_i$ between consecutive nonzero constituents whenever that separator is not a double colon, i.e.
inside every train ($1$ for a comma, $2$ for a semicolon). Only the absolute scales and the gaps between trains
are forgotten, as are signs and oddities.

*Clarification*: the correspondence is bijective onto 2-adic
symbols without signs and oddities modulo translating trains (the absolute scales and the gaps between trains are
forgotten), and, by `exists_toPartial_eq_iff`, onto the partial local genus symbols without a comma between two
barred blocks. -/
@[kb "hanke2011structure" "Rem. 5.2, p. 22"]
theorem toPartial_eq_imp {σ τ : TwoSymbol} {N M n : ℕ} (hσ : TwoSymbolValid σ N) (hτ : TwoSymbolValid τ M)
    (hσn : ∑ k ∈ range N, (σ k).dim = n) (hτn : ∑ k ∈ range M, (τ k).dim = n)
    (h : toPartial σ N n hσ hσn = toPartial τ M n hτ hτn) :
    (suppList σ N).length = (suppList τ M).length ∧
    (∀ i a b : ℕ, (suppList σ N)[i]? = some a → (suppList τ M)[i]? = some b →
      (σ a).dim = (τ b).dim ∧ (σ a).type = (τ b).type) ∧
    (∀ i a a' b b' : ℕ, (suppList σ N)[i]? = some a → (suppList σ N)[i + 1]? = some a' →
      (suppList τ M)[i]? = some b → (suppList τ M)[i + 1]? = some b' →
      sepOf σ a a' = sepOf τ b b' ∧ (sepOf σ a a' ≠ Separator.doubleColon → a' - a = b' - b)) := by
  have hbars : (suppList σ N).map (fun k => decide ((σ k).type = .II)) =
      (suppList τ M).map (fun k => decide ((τ k).type = .II)) := congrArg PartialLocalGenusSymbol.bars h
  have hblocks : (suppList σ N).map (fun k => (σ k).dim) = (suppList τ M).map (fun k => (τ k).dim) :=
    congrArg (fun t => t.blocks.blocks) h
  refine ⟨by simpa using congrArg List.length hbars, ?_, ?_⟩
  · intro i a b ha hb
    have h1 := congrArg (fun l : List ℕ => l[i]?) hblocks
    have h2 := congrArg (fun l : List Bool => l[i]?) hbars
    simp only [List.getElem?_map, ha, hb, Option.map_some, Option.some.injEq] at h1 h2
    refine ⟨h1, ?_⟩
    cases h3 : (σ a).type <;> cases h4 : (τ b).type <;> simp_all
  · intro i a a' b b' ha ha' hb hb'
    have e1 := toPartial_seps_getElem? hσ hσn ha ha'
    have e2 := toPartial_seps_getElem? hτ hτn hb hb'
    rw [h, e2, Option.some.injEq] at e1
    have e1 := e1.symm
    refine ⟨e1, fun hne => ?_⟩
    cases hs : sepOf σ a a' with
    | comma =>
      have g1 := sepOf_comma_gap hs
      have g2 := sepOf_comma_gap (e1 ▸ hs)
      omega
    | semicolon =>
      have g1 := sepOf_semicolon_gap hs
      have g2 := sepOf_semicolon_gap (e1 ▸ hs)
      omega
    | doubleColon => exact absurd hs hne

/-! ### The correspondence is not injective -/

/-- The constituent $1_1^{+1}$ (a unit of dimension $1$, type I, oddity $1$). -/
def exFactor : TwoFactor := ⟨1, .plus, .I, 1⟩

/-- The symbol with the single constituent `exFactor` at the scale $2^j$. -/
def singleSym (j : ℕ) : TwoSymbol := fun k => if k = j then exFactor else TwoFactor.trivial

theorem singleSym_valid (j : ℕ) : TwoSymbolValid (singleSym j) (j + 1) := by
  refine ⟨fun k hk => ?_, fun k => ?_⟩
  · simp [singleSym, show k ≠ j by omega]
  · by_cases h : k = j
    · simp only [singleSym, h, ite_true]; decide
    · simp only [singleSym, h, ite_false]; decide

theorem singleSym_sum (j : ℕ) : ∑ k ∈ range (j + 1), (singleSym j k).dim = 1 := by
  rw [Finset.sum_range_succ]
  have : ∑ k ∈ range j, (singleSym j k).dim = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkj : k ≠ j := by have := Finset.mem_range.mp hk; omega
    simp [singleSym, hkj, TwoFactor.trivial]
  rw [this]
  simp [singleSym, exFactor]

/-- The symbol with `exFactor` at the scales $2^0$ and $2^g$. -/
def twoSym (g : ℕ) : TwoSymbol := fun k => if k = 0 ∨ k = g then exFactor else TwoFactor.trivial

theorem twoSym_valid (g : ℕ) : TwoSymbolValid (twoSym g) (g + 1) := by
  refine ⟨fun k hk => ?_, fun k => ?_⟩
  · simp [twoSym, show k ≠ g by omega, show k ≠ 0 by omega]
  · by_cases h : k = 0 ∨ k = g
    · simp only [twoSym, h, ite_true]; decide
    · simp only [twoSym, h, ite_false]; decide

/-- **`toPartial` is not injective** (Hanke 2011, Rem. 5.2, p. 22): translating all scales by one
($1_1^{+1}$ at $2^0$ versus at $2^1$), as well as widening the gap between two trains ($1_1^{+1}$ at $2^0$ and
$2^3$ versus at $2^0$ and $2^4$), gives different valid 2-adic symbols with the same partial local genus symbol
($(1)$, resp. $(1 :: 1)$). Hence the correspondence of the remark is a bijection only after forgetting the
absolute scales and the gaps between trains (`toPartial_eq_imp`). -/
@[kb "hanke2011structure" "Rem. 5.2, p. 22"]
theorem toPartial_not_injective :
    (∃ (σ τ : TwoSymbol) (N M : ℕ) (hσ : TwoSymbolValid σ N) (hτ : TwoSymbolValid τ M)
      (hσn : ∑ k ∈ range N, (σ k).dim = 1) (hτn : ∑ k ∈ range M, (τ k).dim = 1),
      σ ≠ τ ∧ toPartial σ N 1 hσ hσn = toPartial τ M 1 hτ hτn) ∧
    (∃ (σ τ : TwoSymbol) (N M : ℕ) (hσ : TwoSymbolValid σ N) (hτ : TwoSymbolValid τ M)
      (hσn : ∑ k ∈ range N, (σ k).dim = 2) (hτn : ∑ k ∈ range M, (τ k).dim = 2),
      σ ≠ τ ∧ toPartial σ N 2 hσ hσn = toPartial τ M 2 hτ hτn) := by
  constructor
  · refine ⟨singleSym 0, singleSym 1, 1, 2, singleSym_valid 0, singleSym_valid 1, singleSym_sum 0,
      singleSym_sum 1, ?_, partial_ext ?_ ?_ ?_⟩
    · intro h
      have := congrFun h 0
      simp only [singleSym, ite_true] at this
      exact absurd this (by decide)
    · show (suppList (singleSym 0) 1).map (fun k => (singleSym 0 k).dim) =
        (suppList (singleSym 1) 2).map (fun k => (singleSym 1 k).dim)
      decide
    · show sepsOf (singleSym 0) (suppList (singleSym 0) 1) = sepsOf (singleSym 1) (suppList (singleSym 1) 2)
      decide
    · show (suppList (singleSym 0) 1).map (fun k => decide ((singleSym 0 k).type = .II)) =
        (suppList (singleSym 1) 2).map (fun k => decide ((singleSym 1 k).type = .II))
      decide
  · refine ⟨twoSym 3, twoSym 4, 4, 5, twoSym_valid 3, twoSym_valid 4, by decide, by decide, ?_, partial_ext ?_ ?_ ?_⟩
    · intro h
      have := congrFun h 3
      revert this
      decide
    · show (suppList (twoSym 3) 4).map (fun k => (twoSym 3 k).dim) =
        (suppList (twoSym 4) 5).map (fun k => (twoSym 4 k).dim)
      decide
    · show sepsOf (twoSym 3) (suppList (twoSym 3) 4) = sepsOf (twoSym 4) (suppList (twoSym 4) 5)
      decide
    · show (suppList (twoSym 3) 4).map (fun k => decide ((twoSym 3 k).type = .II)) =
        (suppList (twoSym 4) 5).map (fun k => decide ((twoSym 4 k).type = .II))
      decide

end QuadFormsKB.Hanke2011Structure
