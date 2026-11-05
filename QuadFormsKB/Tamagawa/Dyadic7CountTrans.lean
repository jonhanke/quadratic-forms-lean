/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Dyadic7CountBlocks

/-!
# Paper 7 at $p = 2$: a set of class representatives for the admissible ternary block lists

For a Hessian valuation $h$ and a unit class $u$ we build a set `reps h u` of admissible block lists containing exactly
one list of every $\mathbb Z_2$-class (Conway–Sloane: of every class of 2-adic symbols under sign walking and oddity
fusion, `SymEquiv`):

* for every exponent pair $1 \le e_1 \le e_2$ with $1 + e_1 + e_2 = h$, the lists `sqL e₁ e₂ x`
  $= [2 a x^2, 2^{e_1} b y^2, 2^{e_2} c z^2]$, $x = (a, b, c)$, whose unit triple is the first (`enc3`) of its class
  among the triples with $abc \equiv u \pmod 8$ (`minSq`);
* for every $m$ with $m = 0$, or $h = 2m + 1$ and $m \ge 2$, the lists `binL m e x` $= [2^m\beta_c, 2^e w x^2]$,
  $e = h - 2m$, $x = (c, w)$, likewise first in their class (`minBin`).

The binary lists with $m = e = 1$ (only for $h = 3$) are equivalent to diagonal ones (an input `hS3` of `reps_cover`,
proved in the row-1 file).

**Proves.** `reps_subset` (the representatives are admissible), `reps_uniq` (no two are equivalent; the dimensions and
types of the symbols determine the exponents, `exps_eq_of_symEquiv_sq`, `exps_eq_of_symEquiv_bin`,
`not_symEquiv_sq_bin`), `reps_cover` (every admissible list is equivalent to one), `sum_reps` (a sum over `reps` as
sums over the exponents).

Indices are 0-based.
-/

open Finset

namespace QuadFormsKB.Dyadic7

open QuadFormsKB.ConwaySloane QuadFormsKB.ConwaySloane.Mass Cassels QuadFormsKB.Hanke2011Ternary

/-- The unit triples $(a, b, c)$, $a, b, c \in \{1,3,5,7\}$, with $abc \equiv u \pmod 8$. -/
def sqUnits3 (u : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  (sqUnits ×ˢ sqUnits ×ˢ sqUnits).filter fun x => (x.1 * x.2.1 * x.2.2) % 8 = u % 8

/-- The pairs $(c, w)$, $c \in \{-1, 3\}$ (the unit of the binary block), $w \in \{1,3,5,7\}$, with $cw \equiv u$. -/
def binUnits (u : ℤ) : Finset (ℤ × ℤ) :=
  (({-1, 3} : Finset ℤ) ×ˢ sqUnits).filter fun x => (x.1 * x.2) % 8 = u % 8

/-- The diagonal list with exponents $1, e_1, e_2$ and units $x$. -/
def sqL (e₁ e₂ : ℕ) (x : ℤ × ℤ × ℤ) : List DyBlock := sqList x.1 x.2.1 x.2.2 e₁ e₂

/-- The binary list with exponents $m, e$ and units $x$. -/
def binL (m e : ℕ) (x : ℤ × ℤ) : List DyBlock := binList x.1 x.2 m e

/-- An injective code of unit triples (to pick the first triple of a class). -/
def enc3 (x : ℤ × ℤ × ℤ) : ℤ := 64 * x.1 + 8 * x.2.1 + x.2.2

/-- An injective code of the pairs $(c, w)$. -/
def enc2 (x : ℤ × ℤ) : ℤ := 8 * x.1 + x.2

theorem enc3_inj {u : ℤ} {x y : ℤ × ℤ × ℤ} (hx : x ∈ sqUnits3 u) (hy : y ∈ sqUnits3 u) (h : enc3 x = enc3 y) :
    x = y := by
  simp only [sqUnits3, sqUnits, Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton] at hx hy
  obtain ⟨⟨h1, h2, h3⟩, -⟩ := hx
  obtain ⟨⟨h1', h2', h3'⟩, -⟩ := hy
  unfold enc3 at h
  obtain ⟨a, b, c⟩ := x
  obtain ⟨a', b', c'⟩ := y
  simp only at h1 h2 h3 h1' h2' h3' h
  simp only [Prod.mk.injEq]
  omega

theorem enc2_inj {u : ℤ} {x y : ℤ × ℤ} (hx : x ∈ binUnits u) (hy : y ∈ binUnits u) (h : enc2 x = enc2 y) :
    x = y := by
  simp only [binUnits, sqUnits, Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton] at hx hy
  obtain ⟨⟨h1, h2⟩, -⟩ := hx
  obtain ⟨⟨h1', h2'⟩, -⟩ := hy
  unfold enc2 at h
  obtain ⟨a, b⟩ := x
  obtain ⟨a', b'⟩ := y
  simp only at h1 h2 h1' h2' h
  simp only [Prod.mk.injEq]
  omega

open Classical

/-- The unit triples that come first (`enc3`) in their class of `sqL e₁ e₂`-lists. -/
noncomputable def minSq (u : ℤ) (e₁ e₂ : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (sqUnits3 u).filter fun x => ∀ x' ∈ sqUnits3 u, SymEquiv (sqL e₁ e₂ x') (sqL e₁ e₂ x) → enc3 x ≤ enc3 x'

/-- The unit pairs that come first (`enc2`) in their class of `binL m e`-lists. -/
noncomputable def minBin (u : ℤ) (m e : ℕ) : Finset (ℤ × ℤ) :=
  (binUnits u).filter fun x => ∀ x' ∈ binUnits u, SymEquiv (binL m e x') (binL m e x) → enc2 x ≤ enc2 x'

/-- The admissible diagonal exponent pairs $(e_1, h - 1 - e_1)$: $1 \le e_1 \le h - 1 - e_1$. -/
def SqExpOK (h e₁ : ℕ) : Prop := 1 ≤ e₁ ∧ e₁ + 1 ≤ h ∧ e₁ ≤ h - 1 - e₁

instance (h e₁ : ℕ) : Decidable (SqExpOK h e₁) := by unfold SqExpOK; infer_instance

/-- The binary exponent pairs $(m, h - 2m)$ used for representatives: $m = 0$ ($h \ge 1$), or $h = 2m + 1$, $m \ge 2$. -/
def BinExpOK (h m : ℕ) : Prop := 2 * m + 1 ≤ h ∧ (m = 0 ∨ (h = 2 * m + 1 ∧ 2 ≤ m))

instance (h m : ℕ) : Decidable (BinExpOK h m) := by unfold BinExpOK; infer_instance

/-- **The class representatives** for Hessian valuation $h$ and unit class $u$. -/
noncomputable def reps (h : ℕ) (u : ℤ) : Finset (List DyBlock) :=
  ((range h).filter (SqExpOK h)).biUnion (fun e₁ => (minSq u e₁ (h - 1 - e₁)).image (sqL e₁ (h - 1 - e₁))) ∪
    ((range h).filter (BinExpOK h)).biUnion (fun m => (minBin u m (h - 2 * m)).image (binL m (h - 2 * m)))

/-! ### Dimensions and types of the two shapes -/

theorem type_eq_I_iff (D : List DyBlock) (k : ℕ) :
    (blockSymbol D k).type = .I ↔ ∃ b ∈ D, IsSqBlock b ∧ blockExp b = k := by
  simp only [blockSymbol]
  split_ifs with h
  · simp only [true_iff]
    obtain ⟨b, hb, hb'⟩ := List.any_eq_true.1 h
    simp only [List.mem_filter, decide_eq_true_eq] at hb hb'
    exact ⟨b, hb.1, hb', hb.2⟩
  · simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro b hb hsq he
    exact h (List.any_eq_true.2 ⟨b, List.mem_filter.2 ⟨hb, by simpa using he⟩, by simpa using hsq⟩)

theorem dim_sqL (e₁ e₂ : ℕ) (x : ℤ × ℤ × ℤ) (k : ℕ) :
    (blockSymbol (sqL e₁ e₂ x) k).dim = (if 1 = k then 1 else 0) + (if e₁ = k then 1 else 0) +
      (if e₂ = k then 1 else 0) := by
  rw [dim_blockSymbol]
  simp only [sqL, sqList, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, blockExp, DyBlock.dim]
  have e1 : ((1 : ℤ) = (k : ℤ)) ↔ 1 = k := by omega
  simp only [Nat.cast_inj, e1]
  ring

theorem type_sqL (e₁ e₂ : ℕ) (x : ℤ × ℤ × ℤ) (k : ℕ) :
    (blockSymbol (sqL e₁ e₂ x) k).type = .I ↔ 1 = k ∨ e₁ = k ∨ e₂ = k := by
  rw [type_eq_I_iff]
  simp only [sqL, sqList, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
    IsSqBlock, true_and, blockExp, Nat.cast_inj]
  omega

theorem dim_binL (m e : ℕ) (x : ℤ × ℤ) (k : ℕ) :
    (blockSymbol (binL m e x) k).dim = (if m = k then 2 else 0) + (if e = k then 1 else 0) := by
  rw [dim_blockSymbol]
  simp only [binL, binList, binBlock, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  split_ifs <;> simp_all [blockExp, DyBlock.dim]

theorem type_binL (m e : ℕ) (x : ℤ × ℤ) (k : ℕ) :
    (blockSymbol (binL m e x) k).type = .I ↔ e = k := by
  rw [type_eq_I_iff]
  simp only [binL, binList, binBlock, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left]
  split_ifs <;> simp [IsSqBlock, blockExp]

theorem sum_sq_dim_sqL (e₁ e₂ : ℕ) (x : ℤ × ℤ × ℤ) (N : ℕ) (h1 : 1 < N) (h2 : e₁ < N) (h3 : e₂ < N) :
    ∑ k ∈ range N, k ^ 2 * (blockSymbol (sqL e₁ e₂ x) k).dim = 1 + e₁ ^ 2 + e₂ ^ 2 := by
  simp only [dim_sqL, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq, Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp [h1, h2, h3]

theorem exps_eq_of_symEquiv_sq {h e₁ e₁' : ℕ} {x x' : ℤ × ℤ × ℤ} (h1 : SqExpOK h e₁) (h1' : SqExpOK h e₁')
    (hm : SymEquiv (sqL e₁ (h - 1 - e₁) x) (sqL e₁' (h - 1 - e₁') x')) : e₁ = e₁' := by
  have hS := MoveEquiv.sameInvariants hm
  have hs : ∑ k ∈ range (h + 1), k ^ 2 * (blockSymbol (sqL e₁ (h - 1 - e₁) x) k).dim =
      ∑ k ∈ range (h + 1), k ^ 2 * (blockSymbol (sqL e₁' (h - 1 - e₁') x') k).dim :=
    Finset.sum_congr rfl fun k _ => by rw [hS.dim_eq k]
  unfold SqExpOK at h1 h1'
  rw [sum_sq_dim_sqL _ _ _ _ (by omega) (by omega) (by omega),
    sum_sq_dim_sqL _ _ _ _ (by omega) (by omega) (by omega)] at hs
  obtain ⟨s, hs1⟩ : ∃ s, h - 1 = s := ⟨_, rfl⟩
  have e2 : h - 1 - e₁ = s - e₁ := by omega
  have e2' : h - 1 - e₁' = s - e₁' := by omega
  rw [e2, e2'] at hs
  obtain ⟨p, hp⟩ : ∃ p, s - e₁ = p := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, s - e₁' = q := ⟨_, rfl⟩
  rw [hp, hq] at hs
  have hsum : e₁ + p = e₁' + q := by omega
  have hle : e₁ ≤ p := by omega
  have hle' : e₁' ≤ q := by omega
  have hz : ((e₁ : ℤ) - e₁') * ((e₁ : ℤ) - q) = 0 := by
    have hs' : (e₁ : ℤ) ^ 2 + p ^ 2 = (e₁' : ℤ) ^ 2 + q ^ 2 := by exact_mod_cast (by omega : e₁ ^ 2 + p ^ 2 = e₁' ^ 2 + q ^ 2)
    have hsum' : (e₁ : ℤ) + p = e₁' + q := by exact_mod_cast hsum
    have hp' : (p : ℤ) = e₁' + q - e₁ := by linarith
    rw [hp'] at hs'
    nlinarith
  rcases mul_eq_zero.1 hz with h' | h'
  · omega
  · have : e₁ = q := by omega
    omega

theorem exps_eq_of_symEquiv_bin {h m m' : ℕ} {x x' : ℤ × ℤ} (h1 : BinExpOK h m) (h1' : BinExpOK h m')
    (hm : SymEquiv (binL m (h - 2 * m) x) (binL m' (h - 2 * m') x')) : m = m' := by
  have hS := MoveEquiv.sameInvariants hm
  have ht := hS.type_eq (h - 2 * m)
  have e1 : (blockSymbol (binL m (h - 2 * m) x) (h - 2 * m)).type = .I := (type_binL _ _ _ _).2 rfl
  rw [e1, type_binL] at ht
  unfold BinExpOK at h1 h1'
  omega

theorem not_symEquiv_sq_bin {h e₁ m : ℕ} {x : ℤ × ℤ × ℤ} {y : ℤ × ℤ} (h1 : BinExpOK h m) :
    ¬ SymEquiv (sqL e₁ (h - 1 - e₁) x) (binL m (h - 2 * m) y) := by
  intro hm
  have hS := MoveEquiv.sameInvariants hm
  have hd := hS.dim_eq m
  have ht := hS.type_eq m
  rw [dim_binL] at hd
  unfold BinExpOK at h1
  have hmne : ¬ h - 2 * m = m := by omega
  rw [if_pos rfl, if_neg hmne] at hd
  have htII : (blockSymbol (binL m (h - 2 * m) y) m).type = .II := by
    cases hty : (blockSymbol (binL m (h - 2 * m) y) m).type
    · exact absurd ((type_binL _ _ _ _).1 hty) hmne
    · rfl
  rw [htII] at ht
  have hn : ¬ (1 = m ∨ e₁ = m ∨ h - 1 - e₁ = m) := fun h' => by
    rw [← type_sqL _ _ x m] at h'; rw [h'] at ht; exact absurd ht (by decide)
  rw [dim_sqL] at hd
  push Not at hn
  rw [if_neg hn.1, if_neg hn.2.1, if_neg hn.2.2] at hd
  omega

/-! ### The representatives -/

theorem mem_reps {h : ℕ} {u : ℤ} {t : List DyBlock} :
    t ∈ reps h u ↔ (∃ e₁, SqExpOK h e₁ ∧ ∃ x ∈ minSq u e₁ (h - 1 - e₁), t = sqL e₁ (h - 1 - e₁) x) ∨
      (∃ m, BinExpOK h m ∧ ∃ x ∈ minBin u m (h - 2 * m), t = binL m (h - 2 * m) x) := by
  unfold reps
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro (⟨e₁, ⟨-, he⟩, x, hx, rfl⟩ | ⟨m, ⟨-, hm⟩, x, hx, rfl⟩)
    · exact Or.inl ⟨e₁, he, x, hx, rfl⟩
    · exact Or.inr ⟨m, hm, x, hx, rfl⟩
  · rintro (⟨e₁, he, x, hx, rfl⟩ | ⟨m, hm, x, hx, rfl⟩)
    · exact Or.inl ⟨e₁, ⟨by unfold SqExpOK at he; omega, he⟩, x, hx, rfl⟩
    · exact Or.inr ⟨m, ⟨by unfold BinExpOK at hm; omega, hm⟩, x, hx, rfl⟩

theorem reps_subset (h : ℕ) (u : ℤ) : reps h u ⊆ admSet h u := by
  intro t ht
  rcases mem_reps.1 ht with ⟨e₁, he, x, hx, rfl⟩ | ⟨m, hm, x, hx, rfl⟩
  · have hx' := (Finset.mem_filter.1 hx).1
    simp only [sqUnits3, Finset.mem_filter, Finset.mem_product] at hx'
    unfold SqExpOK at he
    exact mem_admSet_sqList hx'.1.1 hx'.1.2.1 hx'.1.2.2 hx'.2 he.1 (by omega) (by omega)
  · have hx' := (Finset.mem_filter.1 hx).1
    simp only [binUnits, Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
      Finset.mem_singleton] at hx'
    unfold BinExpOK at hm
    exact mem_admSet_binList hx'.1.1 hx'.1.2 hx'.2 (by omega) (by omega) (by omega)

theorem reps_uniq (h : ℕ) (u : ℤ) : ∀ t ∈ reps h u, ∀ t' ∈ reps h u, SymEquiv t t' → t = t' := by
  intro t ht t' ht' hm
  rcases mem_reps.1 ht with ⟨e₁, he, x, hx, rfl⟩ | ⟨m, hm', x, hx, rfl⟩ <;>
    rcases mem_reps.1 ht' with ⟨e₁', he', x', hx', rfl⟩ | ⟨m', hm'', x', hx', rfl⟩
  · obtain rfl := exps_eq_of_symEquiv_sq he he' hm
    have h1 := (Finset.mem_filter.1 hx).2 x' (Finset.mem_filter.1 hx').1 (symEquiv_equivalence.symm hm)
    have h2 := (Finset.mem_filter.1 hx').2 x (Finset.mem_filter.1 hx).1 hm
    rw [enc3_inj (Finset.mem_filter.1 hx).1 (Finset.mem_filter.1 hx').1 (le_antisymm h1 h2)]
  · exact absurd hm (not_symEquiv_sq_bin hm'')
  · exact absurd (symEquiv_equivalence.symm hm) (not_symEquiv_sq_bin hm')
  · obtain rfl := exps_eq_of_symEquiv_bin hm' hm'' hm
    have h1 := (Finset.mem_filter.1 hx).2 x' (Finset.mem_filter.1 hx').1 (symEquiv_equivalence.symm hm)
    have h2 := (Finset.mem_filter.1 hx').2 x (Finset.mem_filter.1 hx).1 hm
    rw [enc2_inj (Finset.mem_filter.1 hx).1 (Finset.mem_filter.1 hx').1 (le_antisymm h1 h2)]

theorem exists_minSq (u : ℤ) (e₁ e₂ : ℕ) {x : ℤ × ℤ × ℤ} (hx : x ∈ sqUnits3 u) :
    ∃ x₀ ∈ minSq u e₁ e₂, SymEquiv (sqL e₁ e₂ x) (sqL e₁ e₂ x₀) := by
  classical
  set C := (sqUnits3 u).filter fun x' => SymEquiv (sqL e₁ e₂ x') (sqL e₁ e₂ x)
  have hC : C.Nonempty := ⟨x, Finset.mem_filter.2 ⟨hx, symEquiv_equivalence.refl _⟩⟩
  obtain ⟨x₀, hx₀, hmin⟩ := C.exists_min_image enc3 hC
  obtain ⟨hx₀u, hx₀x⟩ := Finset.mem_filter.1 hx₀
  refine ⟨x₀, Finset.mem_filter.2 ⟨hx₀u, fun x' hx' hrel => hmin x' (Finset.mem_filter.2 ⟨hx',
    symEquiv_equivalence.trans hrel hx₀x⟩)⟩, symEquiv_equivalence.symm hx₀x⟩

theorem exists_minBin (u : ℤ) (m e : ℕ) {x : ℤ × ℤ} (hx : x ∈ binUnits u) :
    ∃ x₀ ∈ minBin u m e, SymEquiv (binL m e x) (binL m e x₀) := by
  classical
  set C := (binUnits u).filter fun x' => SymEquiv (binL m e x') (binL m e x)
  have hC : C.Nonempty := ⟨x, Finset.mem_filter.2 ⟨hx, symEquiv_equivalence.refl _⟩⟩
  obtain ⟨x₀, hx₀, hmin⟩ := C.exists_min_image enc2 hC
  obtain ⟨hx₀u, hx₀x⟩ := Finset.mem_filter.1 hx₀
  refine ⟨x₀, Finset.mem_filter.2 ⟨hx₀u, fun x' hx' hrel => hmin x' (Finset.mem_filter.2 ⟨hx',
    symEquiv_equivalence.trans hrel hx₀x⟩)⟩, symEquiv_equivalence.symm hx₀x⟩

/-- **Every admissible list is equivalent to a representative**, given that the binary lists with $m = e = 1$ are
equivalent to diagonal ones (`hS3`, Hessian valuation $3$). -/
theorem reps_cover (h : ℕ) (u : ℤ)
    (hS3 : ∀ x ∈ binUnits u, ∃ y ∈ sqUnits3 u, SymEquiv (binL 1 1 x) (sqL 1 1 y)) :
    ∀ D ∈ admSet h u, ∃ t ∈ reps h u, SymEquiv D t := by
  intro D hD
  rcases exists_sorted_of_mem_admSet hD with
    ⟨c, w, m, e, hp, hc, hw, hu, hh, he, hpe⟩ | ⟨a, b, c, e₁, e₂, hp, ha, hb, hc, hu, h1, h12, hh⟩
  · have hDx : SymEquiv D (binL m e (c, w)) := by
      unfold SymEquiv; rw [blockSymbol_perm hp]; exact symEquiv_equivalence.refl _
    have hx : (c, w) ∈ binUnits u := by
      simp only [binUnits, Finset.mem_filter, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨⟨hc, hw⟩, hu⟩
    by_cases h11 : m = 1 ∧ e = 1
    · obtain ⟨rfl, rfl⟩ := h11
      obtain ⟨y, hy, hxy⟩ := hS3 _ hx
      obtain ⟨y₀, hy₀, hyy⟩ := exists_minSq u 1 1 hy
      have hh3 : h = 3 := by omega
      subst hh3
      exact ⟨sqL 1 1 y₀, mem_reps.2 (Or.inl ⟨1, by decide, y₀, hy₀, rfl⟩),
        symEquiv_equivalence.trans hDx (symEquiv_equivalence.trans hxy hyy)⟩
    · have hok : BinExpOK h m := ⟨by omega, by omega⟩
      have he' : e = h - 2 * m := by omega
      subst he'
      obtain ⟨x₀, hx₀, hxx⟩ := exists_minBin u m (h - 2 * m) hx
      exact ⟨binL m (h - 2 * m) x₀, mem_reps.2 (Or.inr ⟨m, hok, x₀, hx₀, rfl⟩),
        symEquiv_equivalence.trans hDx hxx⟩
  · have hDx : SymEquiv D (sqL e₁ e₂ (a, b, c)) := by
      unfold SymEquiv; rw [blockSymbol_perm hp]; exact symEquiv_equivalence.refl _
    have hx : (a, b, c) ∈ sqUnits3 u := by
      simp only [sqUnits3, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨ha, hb, hc⟩, hu⟩
    have hok : SqExpOK h e₁ := ⟨h1, by omega, by omega⟩
    have he' : e₂ = h - 1 - e₁ := by omega
    subst he'
    obtain ⟨x₀, hx₀, hxx⟩ := exists_minSq u e₁ (h - 1 - e₁) hx
    exact ⟨sqL e₁ (h - 1 - e₁) x₀, mem_reps.2 (Or.inl ⟨e₁, hok, x₀, hx₀, rfl⟩),
      symEquiv_equivalence.trans hDx hxx⟩

theorem sqL_injective (e₁ e₂ : ℕ) : Function.Injective (sqL e₁ e₂) := by
  intro x y hxy
  obtain ⟨a, b, c⟩ := x
  obtain ⟨a', b', c'⟩ := y
  simp only [sqL, sqList, List.cons.injEq, DyBlock.sq.injEq, true_and, and_true] at hxy
  obtain ⟨rfl, rfl, rfl⟩ := hxy
  rfl

theorem binL_injOn {u : ℤ} (m e : ℕ) {x y : ℤ × ℤ} (hx : x ∈ binUnits u) (hy : y ∈ binUnits u)
    (hxy : binL m e x = binL m e y) : x = y := by
  obtain ⟨c, w⟩ := x
  obtain ⟨c', w'⟩ := y
  simp only [binUnits, Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton] at hx hy
  simp only [binL, binList, binBlock, List.cons.injEq, DyBlock.sq.injEq, true_and, and_true] at hxy
  obtain ⟨h1, rfl⟩ := hxy
  simp only [Prod.mk.injEq, and_true]
  rcases hx.1.1 with rfl | rfl <;> rcases hy.1.1 with rfl | rfl <;> simp_all

/-- **A sum over the representatives, by exponents.** -/
theorem sum_reps (h : ℕ) (u : ℤ) (g : List DyBlock → ℝ) :
    ∑ t ∈ reps h u, g t =
      ∑ e₁ ∈ (range h).filter (SqExpOK h), ∑ x ∈ minSq u e₁ (h - 1 - e₁), g (sqL e₁ (h - 1 - e₁) x) +
      ∑ m ∈ (range h).filter (BinExpOK h), ∑ x ∈ minBin u m (h - 2 * m), g (binL m (h - 2 * m) x) := by
  unfold reps
  rw [Finset.sum_union, Finset.sum_biUnion, Finset.sum_biUnion]
  · congr 1
    · exact Finset.sum_congr rfl fun e₁ _ => Finset.sum_image fun x _ y _ hxy => sqL_injective _ _ hxy
    · exact Finset.sum_congr rfl fun m _ => Finset.sum_image fun x hx y hy hxy =>
        binL_injOn _ _ (Finset.mem_filter.1 hx).1 (Finset.mem_filter.1 hy).1 hxy
  · intro m hm m' hm' hne
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq, BinExpOK] at hm hm'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro t ht ht'
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨y, -, hy⟩ := Finset.mem_image.1 ht'
    simp only [binL, binList, List.cons.injEq, DyBlock.sq.injEq, Nat.cast_inj] at hy
    omega
  · intro e₁ _ e₁' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro t ht ht'
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨y, -, hy⟩ := Finset.mem_image.1 ht'
    simp only [sqL, sqList, List.cons.injEq, DyBlock.sq.injEq] at hy
    omega
  · rw [Finset.disjoint_left]
    intro t ht ht'
    obtain ⟨e₁, -, ht⟩ := Finset.mem_biUnion.1 ht
    obtain ⟨m, -, ht'⟩ := Finset.mem_biUnion.1 ht'
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨y, -, hy⟩ := Finset.mem_image.1 ht'
    simp [sqL, sqList, binL, binList] at hy

end QuadFormsKB.Dyadic7
