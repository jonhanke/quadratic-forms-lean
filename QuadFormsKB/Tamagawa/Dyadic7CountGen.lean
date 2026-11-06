/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Dyadic7CountFam

/-!
# Paper 7 at $p = 2$: a family of representatives with fixed exponents

A *family* (`SqFam e₁ e₂`, `BinFam m e`) fixes the exponents of the diagonal lists `sqL e₁ e₂ x`
(resp. binary lists `binL m e x`) and a window decomposition `ws` with explicit localized lists `L x`
(computable functions of the units $x$). From these data:

* `SqFam.symEquiv_iff`: two lists of the family are equivalent (sign walking, oddity fusion) iff the computable
  relation `LocRel` holds between their localized lists;
* `SqFam.minSq_eq`: the first-in-class unit triples are a computable filter;
* `SqFam.massWt_eq`: the mass weight is
  $4^{1-h}\cdot 6\cdot\mathrm{diagOfSpec}(\text{species}) \cdot 2^{e_2 - 1}\cdot 2^{n(\mathrm{I,I}) - n(\mathrm{II})}$,
  the species of the windows (`specL`) being computable;
* `sum_eq_of_map`: a sum of a function of a computable key, from the multiset of keys.

Indices are 0-based.
-/

open Finset

namespace QuadFormsKB.Dyadic7

open QuadFormsKB.ConwaySloane QuadFormsKB.ConwaySloane.Mass Cassels QuadFormsKB.Hanke2011Ternary

/-! ### Window data as lists -/

/-- `WinEq` on corresponding windows of two lists of localized block lists, with window lengths `ns`. -/
def LocRel : List ℕ → List (List DyBlock) → List (List DyBlock) → Prop
  | n :: ns, a :: as, b :: bs => WinEq (blockSymbol a) (blockSymbol b) n ∧ LocRel ns as bs
  | _, _, _ => True

instance : ∀ (ns : List ℕ) (as bs : List (List DyBlock)), Decidable (LocRel ns as bs)
  | n :: ns, a :: as, b :: bs => by
    unfold LocRel; haveI := instDecidableLocRel ns as bs; infer_instance
  | [], _, _ => by unfold LocRel; infer_instance
  | _ :: _, [], _ => by unfold LocRel; infer_instance
  | _ :: _, _ :: _, [] => by unfold LocRel; infer_instance

/-- The window lengths. -/
def winLens (ws : List (ℕ × ℕ)) : List ℕ := ws.map fun w => w.2 - w.1

/-- The species of the windows. -/
def specL : List ℕ → List (List DyBlock) → List (List Species)
  | n :: ns, a :: as => locSpecies a n :: specL ns as
  | _, _ => []

/-- The product of the diagonal factors $M_2$ of a list of species lists. -/
def diagOfSpec (l : List (List Species)) : ℚ := (l.map fun s => (s.map (Species.diagFactor 2)).prod).prod

/-- `locNII` over windows. -/
def locNIIL : List ℕ → List (List DyBlock) → ℕ
  | n :: ns, a :: as => locNII a n + locNIIL ns as
  | _, _ => 0

/-- `locNII'` over windows. -/
def locNII'L : List ℕ → List (List DyBlock) → ℕ
  | n :: ns, a :: as => locNII' a n + locNII'L ns as
  | _, _ => 0

theorem locNII_forget (L : List DyBlock) (n : ℕ) : locNII (L.map forgetUnit) n = locNII L n := by
  have hff : (L.map forgetUnit).map forgetUnit = L.map forgetUnit := by
    rw [List.map_map]; congr 1; funext b; cases b <;> rfl
  unfold locNII
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [type_eq_of_forget hff i, dim_eq_of_forget hff i]

theorem locNII'_forget (L : List DyBlock) (n : ℕ) : locNII' (L.map forgetUnit) n = locNII' L n := by
  have hff : (L.map forgetUnit).map forgetUnit = L.map forgetUnit := by
    rw [List.map_map]; congr 1; funext b; cases b <;> rfl
  unfold locNII'
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [type_eq_of_forget hff i, type_eq_of_forget hff (i + 1)]

theorem locNIIL_forget : ∀ (ns : List ℕ) (as : List (List DyBlock)),
    locNIIL ns (as.map (List.map forgetUnit)) = locNIIL ns as
  | n :: ns, a :: as => by
    show locNII _ n + locNIIL ns _ = locNII a n + locNIIL ns as
    rw [locNII_forget, locNIIL_forget ns as]
  | [], _ => rfl
  | _ :: _, [] => rfl

theorem locNII'L_forget : ∀ (ns : List ℕ) (as : List (List DyBlock)),
    locNII'L ns (as.map (List.map forgetUnit)) = locNII'L ns as
  | n :: ns, a :: as => by
    show locNII' _ n + locNII'L ns _ = locNII' a n + locNII'L ns as
    rw [locNII'_forget, locNII'L_forget ns as]
  | [], _ => rfl
  | _ :: _, [] => rfl

theorem forall_winEq_iff (ws : List (ℕ × ℕ)) (f g : ℕ × ℕ → List DyBlock) :
    (∀ w ∈ ws, WinEq (blockSymbol (f w)) (blockSymbol (g w)) (w.2 - w.1)) ↔
      LocRel (winLens ws) (ws.map f) (ws.map g) := by
  induction ws with
  | nil => simp [LocRel, winLens]
  | cons w ws ih =>
    show _ ↔ (WinEq _ _ _ ∧ LocRel (winLens ws) (ws.map f) (ws.map g))
    rw [List.forall_mem_cons, ih]

theorem prod_locDiag (ws : List (ℕ × ℕ)) (f : ℕ × ℕ → List DyBlock) :
    (ws.map fun w => locDiag (f w) (w.2 - w.1)).prod = diagOfSpec (specL (winLens ws) (ws.map f)) := by
  induction ws with
  | nil => simp [diagOfSpec, specL, winLens]
  | cons w ws ih =>
    simp only [List.map_cons, List.prod_cons, winLens, specL, diagOfSpec] at ih ⊢
    rw [ih, locDiag_eq]

theorem sum_locNII (ws : List (ℕ × ℕ)) (f : ℕ × ℕ → List DyBlock) :
    (ws.map fun w => locNII (f w) (w.2 - w.1)).sum = locNIIL (winLens ws) (ws.map f) := by
  induction ws with
  | nil => simp [locNIIL, winLens]
  | cons w ws ih => simp only [List.map_cons, List.sum_cons, winLens, locNIIL] at ih ⊢; rw [ih]

theorem sum_locNII' (ws : List (ℕ × ℕ)) (f : ℕ × ℕ → List DyBlock) :
    (ws.map fun w => locNII' (f w) (w.2 - w.1)).sum = locNII'L (winLens ws) (ws.map f) := by
  induction ws with
  | nil => simp [locNII'L, winLens]
  | cons w ws ih => simp only [List.map_cons, List.sum_cons, winLens, locNII'L] at ih ⊢; rw [ih]

theorem map_eq_map_mem {α β : Type*} {l : List α} {f g : α → β} (h : l.map f = l.map g) : ∀ a ∈ l, f a = g a := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.cons.injEq] at h
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact h.1
    · exact ih h.2 b hb

/-- A sum of a function of a key, from the multiset of keys. -/
theorem sum_eq_of_map {α β : Type*} (s : Finset α) (k : α → β) (g : β → ℝ) (M : Multiset β)
    (h : s.val.map k = M) : ∑ x ∈ s, g (k x) = (M.map g).sum := by
  rw [Finset.sum_eq_multiset_sum, ← h, Multiset.map_map]; rfl

/-! ### Exact arithmetic of the diagonal factors -/

/-- Six times the diagonal factor $M_2$ of a species of dimension $\le 3$, a natural number:
$M_2(0\pm) = 1$, $M_2(1) = 1/2$, $M_2(2+) = 1$, $M_2(2-) = 1/3$, $M_2(3) = 2/3$. -/
def natDiag (s : Species) : ℕ :=
  if s.dim = 0 then 6 else if s.dim = 1 then 3 else if s.dim = 2 then (if s.sign = .plus then 6 else 2) else 4

theorem natDiag_eq (s : Species) (hs : s.dim ≤ 3) : (natDiag s : ℚ) = 6 * s.diagFactor 2 := by
  obtain ⟨d, σ⟩ := s
  simp only at hs
  interval_cases d <;> cases σ <;>
    norm_num [natDiag, Species.diagFactor, lowerProd, Sign.toInt, Finset.prod_range_succ]

/-- The product of `natDiag` over a list of species lists. -/
def natDiagL (l : List (List Species)) : ℕ := (l.map fun s => (s.map natDiag).prod).prod

theorem natDiagL_eq : ∀ (l : List (List Species)), (∀ s ∈ l.flatten, s.dim ≤ 3) →
    (natDiagL l : ℚ) = 6 ^ l.flatten.length * diagOfSpec l
  | [], _ => by simp [natDiagL, diagOfSpec]
  | a :: l, h => by
    have ih := natDiagL_eq l fun s hs => h s (by
      obtain ⟨t, ht, hst⟩ := List.mem_flatten.1 hs
      exact List.mem_flatten.2 ⟨t, List.mem_cons_of_mem _ ht, hst⟩)
    have ha : ((a.map natDiag).prod : ℚ) = 6 ^ a.length * (a.map (Species.diagFactor 2)).prod := by
      have : ∀ s ∈ a, s.dim ≤ 3 := fun s hs => h s (List.mem_flatten.2 ⟨a, List.mem_cons_self .., hs⟩)
      clear h ih
      induction a with
      | nil => simp
      | cons s a iha =>
        simp only [List.map_cons, List.prod_cons, Nat.cast_mul, List.length_cons]
        rw [natDiag_eq s (this s (List.mem_cons_self ..)), iha fun t ht => this t (List.mem_cons_of_mem _ ht)]
        ring
    simp only [natDiagL, diagOfSpec, List.map_cons, List.prod_cons, Nat.cast_mul, List.flatten_cons,
      List.length_append] at ih ⊢
    rw [ha, ih]
    ring

/-- A sum of diagonal factors over a finite set, from natural-number data (decidable). -/
theorem sum_diagOfSpec {α : Type*} (s : Finset α) (k : α → List (List Species)) (T N : ℕ)
    (hk : ∀ x ∈ s, (∀ t ∈ (k x).flatten, t.dim ≤ 3) ∧ (k x).flatten.length = T)
    (hN : (s.val.map fun x => natDiagL (k x)).sum = N) :
    ∑ x ∈ s, ((diagOfSpec (k x) : ℚ) : ℝ) = (N : ℝ) / 6 ^ T := by
  have e : ∀ x ∈ s, ((diagOfSpec (k x) : ℚ) : ℝ) = (natDiagL (k x) : ℝ) / 6 ^ T := by
    intro x hx
    have := natDiagL_eq (k x) (hk x hx).1
    rw [(hk x hx).2] at this
    rw [eq_div_iff (by positivity)]
    have h' : ((natDiagL (k x) : ℚ) : ℝ) = ((6 ^ T * diagOfSpec (k x) : ℚ) : ℝ) := by rw [this]
    push_cast at h'
    rw [h']; ring
  rw [Finset.sum_congr rfl e, ← Finset.sum_div]
  congr 1
  rw [← hN, Finset.sum_eq_multiset_sum, Nat.cast_multiset_sum, Multiset.map_map]
  rfl

/-- The same with integer weights (Hasse invariants). -/
theorem sum_mul_diagOfSpec {α : Type*} (s : Finset α) (k : α → List (List Species)) (c : α → ℤ) (T : ℕ) (N : ℤ)
    (hk : ∀ x ∈ s, (∀ t ∈ (k x).flatten, t.dim ≤ 3) ∧ (k x).flatten.length = T)
    (hN : (s.val.map fun x => c x * natDiagL (k x)).sum = N) :
    ∑ x ∈ s, (c x : ℝ) * ((diagOfSpec (k x) : ℚ) : ℝ) = (N : ℝ) / 6 ^ T := by
  have e : ∀ x ∈ s, (c x : ℝ) * ((diagOfSpec (k x) : ℚ) : ℝ) = ((c x * natDiagL (k x) : ℤ) : ℝ) / 6 ^ T := by
    intro x hx
    have := natDiagL_eq (k x) (hk x hx).1
    rw [(hk x hx).2] at this
    rw [eq_div_iff (by positivity)]
    have h' : ((natDiagL (k x) : ℚ) : ℝ) = ((6 ^ T * diagOfSpec (k x) : ℚ) : ℝ) := by rw [this]
    push_cast at h' ⊢
    rw [h']; ring
  rw [Finset.sum_congr rfl e, ← Finset.sum_div]
  congr 1
  rw [← hN, Finset.sum_eq_multiset_sum, Int.cast_multiset_sum, Multiset.map_map]
  rfl

/-! ### Cross terms of the two shapes -/

theorem crossExp_sqL {e₁ e₂ N : ℕ} (x : ℤ × ℤ × ℤ) (h1 : 1 ≤ e₁) (h12 : e₁ ≤ e₂) (h2 : e₂ < N) :
    crossExp (fun k => (blockSymbol (sqL e₁ e₂ x) k).dim) N = 2 * (e₂ - 1) := by
  rw [crossExp_blockSymbol _ (fun b hb => by
    simp only [sqL, sqList, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp [blockExp])]
  simp only [sqL, sqList, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, blockExp, DyBlock.dim,
    Int.toNat_natCast, Int.toNat_one, mul_one]
  rcases Nat.eq_or_lt_of_le h1 with h1' | h1' <;> rcases Nat.eq_or_lt_of_le h12 with h2' | h2'
  all_goals subst_vars
  all_goals simp (disch := omega) only [if_pos, if_neg, lt_irrefl, false_and, and_false, Nat.lt_irrefl, if_false]
  all_goals omega

theorem crossExp_binL {m e N : ℕ} (x : ℤ × ℤ) (h1 : m < N) (h2 : e < N) :
    crossExp (fun k => (blockSymbol (binL m e x) k).dim) N = 2 * (max m e - min m e) := by
  rw [crossExp_blockSymbol _ (fun b hb => by
    simp only [binL, binList, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · rw [blockExp_binBlock]; omega
    · simp [blockExp])]
  simp only [binL, binList, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, blockExp_binBlock]
  simp only [blockExp, Int.toNat_natCast]
  have hd : (binBlock x.1 (m : ℤ)).dim = 2 := by unfold binBlock; split_ifs <;> rfl
  rw [hd]
  simp only [DyBlock.dim, mul_one, one_mul]
  rcases lt_trichotomy m e with h | rfl | h
  all_goals simp (disch := omega) only [if_pos, if_neg, lt_irrefl, false_and, and_false, if_false,
    max_eq_left, max_eq_right, min_eq_left, min_eq_right, max_self, min_self]
  all_goals omega

theorem sqrt_two_pow_two_mul (n : ℕ) : Real.sqrt 2 ^ (2 * n) = (2 : ℝ) ^ n := by
  rw [pow_mul, Real.sq_sqrt (by norm_num)]

/-! ### Window decompositions from computable data -/

/-- The first and last scales of every window are of type II (for localized lists `as`, window lengths `ns`). -/
def EdgeOK : List ℕ → List (List DyBlock) → Prop
  | n :: ns, a :: as => (blockSymbol a 0).type = .II ∧ (blockSymbol a (n - 1)).type = .II ∧ EdgeOK ns as
  | _, _ => True

instance : ∀ (ns : List ℕ) (as : List (List DyBlock)), Decidable (EdgeOK ns as)
  | n :: ns, a :: as => by
    unfold EdgeOK; haveI := instDecidableEdgeOK ns as; infer_instance
  | [], _ => by unfold EdgeOK; infer_instance
  | _ :: _, [] => by unfold EdgeOK; infer_instance

theorem edgeOK_iff (ws : List (ℕ × ℕ)) (f : ℕ × ℕ → List DyBlock) :
    EdgeOK (winLens ws) (ws.map f) ↔ ∀ w ∈ ws, (blockSymbol (f w) 0).type = .II ∧
      (blockSymbol (f w) (w.2 - w.1 - 1)).type = .II := by
  induction ws with
  | nil => simp [EdgeOK, winLens]
  | cons w ws ih =>
    show (_ ∧ _ ∧ EdgeOK (winLens ws) (ws.map f)) ↔ _
    rw [List.forall_mem_cons, ih, and_assoc]

theorem edgeOK_forget : ∀ (ns : List ℕ) (as : List (List DyBlock)),
    EdgeOK ns (as.map (List.map forgetUnit)) ↔ EdgeOK ns as
  | n :: ns, a :: as => by
    show (_ ∧ _ ∧ EdgeOK ns (as.map (List.map forgetUnit))) ↔ (_ ∧ _ ∧ EdgeOK ns as)
    have hff : (a.map forgetUnit).map forgetUnit = a.map forgetUnit := by
      rw [List.map_map]; congr 1; funext b; cases b <;> rfl
    rw [type_eq_of_forget hff 0, type_eq_of_forget hff (n - 1), edgeOK_forget ns as]
  | [], _ => by simp [EdgeOK]
  | _ :: _, [] => by simp [EdgeOK]

/-- **A window decomposition from computable data**: the localized lists `L`, their unit-free form `L₀` (whose window
edges are decided to be of type II), disjoint nonempty windows covering the exponents. -/
theorem winDecomp_of {D : List DyBlock} {ws : List (ℕ × ℕ)} {L L₀ : List (List DyBlock)}
    (hloc : ws.map (fun w => localize D w.1 (w.2 - w.1)) = L) (hfg : L.map (List.map forgetUnit) = L₀)
    (hedge : EdgeOK (winLens ws) L₀) (hlt : ∀ w ∈ ws, w.1 < w.2)
    (hdisj : ∀ w ∈ ws, ∀ w' ∈ ws, w ≠ w' → w.2 ≤ w'.1 ∨ w'.2 ≤ w.1)
    (hcover : ∀ b ∈ D, ∃ w ∈ ws, (w.1 : ℤ) ≤ blockExp b ∧ blockExp b < w.2) : WinDecomp D ws := by
  rw [← hfg, edgeOK_forget, ← hloc, edgeOK_iff] at hedge
  exact ⟨hlt, hdisj, hcover, fun w hw => (hedge w hw).1, fun w hw => (hedge w hw).2⟩

/-! ### Diagonal families -/

/-- **A family of diagonal representatives** with exponents $1, e_1, e_2$: windows `ws` (no repeats) forming a window
decomposition of every `sqL e₁ e₂ x`, with localized lists `L x` that differ only in their units. -/
structure SqFam (e₁ e₂ : ℕ) where
  ws : List (ℕ × ℕ)
  L : ℤ × ℤ × ℤ → List (List DyBlock)
  hnd : ws.Nodup
  hloc : ∀ x, ws.map (fun w => localize (sqL e₁ e₂ x) w.1 (w.2 - w.1)) = L x
  hdec : ∀ x, WinDecomp (sqL e₁ e₂ x) ws
  hforget : ∀ x y, (L x).map (List.map forgetUnit) = (L y).map (List.map forgetUnit)

namespace SqFam

variable {e₁ e₂ : ℕ} (F : SqFam e₁ e₂)

theorem symEquiv_iff (x y : ℤ × ℤ × ℤ) :
    SymEquiv (sqL e₁ e₂ x) (sqL e₁ e₂ y) ↔ LocRel (winLens F.ws) (F.L x) (F.L y) := by
  unfold SymEquiv
  rw [moveEquiv_iff_local (F.hdec x) (F.hdec y), forall_winEq_iff, F.hloc, F.hloc]
  intro w hw i _
  have h := F.hforget y x
  rw [← F.hloc, ← F.hloc, List.map_map, List.map_map] at h
  have hw' := map_eq_map_mem h w hw
  simp only [Function.comp] at hw'
  exact ⟨dim_eq_of_forget hw' i, type_eq_of_forget hw' i⟩

theorem minSq_eq (u : ℤ) : minSq u e₁ e₂ = (sqUnits3 u).filter fun x =>
    ∀ x' ∈ sqUnits3 u, LocRel (winLens F.ws) (F.L x') (F.L x) → enc3 x ≤ enc3 x' :=
  minSq_eq_filter (fun x y => LocRel (winLens F.ws) (F.L x) (F.L y)) fun x _ y _ => F.symEquiv_iff x y

theorem massWt_eq {h : ℕ} {u : ℤ} (hu : u ∈ sqUnits) (x : ℤ × ℤ × ℤ) (h1 : 1 ≤ e₁) (h12 : e₁ ≤ e₂)
    (hh : 1 + e₁ + e₂ = h) (hN : ∀ w ∈ F.ws, w.2 ≤ h + 1) :
    massWt h u (sqL e₁ e₂ x) = (1 / 4 : ℝ) ^ (h - 1) * 6 *
      ((diagOfSpec (specL (winLens F.ws) (F.L x)) : ℚ) : ℝ) * (2 : ℝ) ^ (e₂ - 1) *
      (2 : ℝ) ^ ((locNII'L (winLens F.ws) (F.L x) : ℤ) - (locNIIL (winLens F.ws) (F.L x) : ℤ)) := by
  have h0 : (blockSymbol (sqL e₁ e₂ x) 0).type = .II := by
    rw [blockSymbol_of_forall_ne fun b hb => by
      simp only [sqL, sqList, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl <;> simp [blockExp] <;> omega]; rfl
  rw [massWt_eq_local hu (F.hdec x) F.hnd h0 hN le_rfl (fun b hb => by
    simp only [sqL, sqList, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp [blockExp] <;> omega),
    prod_locDiag, sum_locNII, sum_locNII', F.hloc, crossExp_sqL x h1 h12 (by omega), sqrt_two_pow_two_mul]
  ring

/-- **The class-weighted mass sum of a diagonal family**, from decidable data on the first-in-class units: the window
species have dimension $\le 3$ and total length `T`, and the sum of `natDiagL` is `N`. -/
theorem sum_massWt {h : ℕ} {u : ℤ} (hu : u ∈ sqUnits) (h1 : 1 ≤ e₁) (h12 : e₁ ≤ e₂)
    (hh : 1 + e₁ + e₂ = h) (hN : ∀ w ∈ F.ws, w.2 ≤ h + 1) (L₀ : List (List DyBlock))
    (hL₀ : ∀ x, (F.L x).map (List.map forgetUnit) = L₀) (T N : ℕ)
    (hk : ∀ x ∈ minSq u e₁ e₂, (∀ t ∈ (specL (winLens F.ws) (F.L x)).flatten, t.dim ≤ 3) ∧
      (specL (winLens F.ws) (F.L x)).flatten.length = T)
    (hS : ((minSq u e₁ e₂).val.map fun x => natDiagL (specL (winLens F.ws) (F.L x))).sum = N) :
    ∑ x ∈ minSq u e₁ e₂, massWt h u (sqL e₁ e₂ x) = (1 / 4 : ℝ) ^ (h - 1) * 6 * (2 : ℝ) ^ (e₂ - 1) *
      (2 : ℝ) ^ ((locNII'L (winLens F.ws) L₀ : ℤ) - (locNIIL (winLens F.ws) L₀ : ℤ)) * ((N : ℝ) / 6 ^ T) := by
  rw [Finset.sum_congr rfl fun x _ => F.massWt_eq hu x h1 h12 hh hN]
  have hc : ∀ x, locNII'L (winLens F.ws) (F.L x) = locNII'L (winLens F.ws) L₀ ∧
      locNIIL (winLens F.ws) (F.L x) = locNIIL (winLens F.ws) L₀ := fun x => by
    rw [← hL₀ x, locNII'L_forget, locNIIL_forget]; exact ⟨rfl, rfl⟩
  simp only [hc]
  rw [← sum_diagOfSpec _ _ T N hk hS, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- **The Hasse-weighted mass sum of a diagonal family** (exponent parities `p`, `q`). -/
theorem sum_hasse_massWt {h : ℕ} {u : ℤ} (hu : u ∈ sqUnits) (h1 : 1 ≤ e₁) (h12 : e₁ ≤ e₂)
    (hh : 1 + e₁ + e₂ = h) (hN : ∀ w ∈ F.ws, w.2 ≤ h + 1) (L₀ : List (List DyBlock))
    (hL₀ : ∀ x, (F.L x).map (List.map forgetUnit) = L₀) (p q : ℕ) (hp : (e₁ + 1) % 2 = p)
    (hq : (e₂ + 1) % 2 = q) (T : ℕ) (N : ℤ)
    (hk : ∀ x ∈ minSq u e₁ e₂, (∀ t ∈ (specL (winLens F.ws) (F.L x)).flatten, t.dim ≤ 3) ∧
      (specL (winLens F.ws) (F.L x)).flatten.length = T)
    (hS : ((minSq u e₁ e₂).val.map fun x => hasseList [(0, (x.1 : ZMod 8)), (p, (x.2.1 : ZMod 8)),
      (q, (x.2.2 : ZMod 8))] * natDiagL (specL (winLens F.ws) (F.L x))).sum = N) :
    ∑ x ∈ minSq u e₁ e₂, (hasseQ (sqL e₁ e₂ x) : ℝ) * massWt h u (sqL e₁ e₂ x) =
      (1 / 4 : ℝ) ^ (h - 1) * 6 * (2 : ℝ) ^ (e₂ - 1) *
      (2 : ℝ) ^ ((locNII'L (winLens F.ws) L₀ : ℤ) - (locNIIL (winLens F.ws) L₀ : ℤ)) * ((N : ℝ) / 6 ^ T) := by
  rw [Finset.sum_congr rfl fun x _ => by rw [F.massWt_eq hu x h1 h12 hh hN, hasseQ_sqL, hp, hq]]
  have hc : ∀ x, locNII'L (winLens F.ws) (F.L x) = locNII'L (winLens F.ws) L₀ ∧
      locNIIL (winLens F.ws) (F.L x) = locNIIL (winLens F.ws) L₀ := fun x => by
    rw [← hL₀ x, locNII'L_forget, locNIIL_forget]; exact ⟨rfl, rfl⟩
  simp only [hc]
  rw [← sum_mul_diagOfSpec _ _ _ T N hk hS, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

end SqFam

/-! ### Binary families -/

/-- **A family of binary representatives** with exponents $m, e$. -/
structure BinFam (m e : ℕ) where
  ws : List (ℕ × ℕ)
  L : ℤ × ℤ → List (List DyBlock)
  hnd : ws.Nodup
  hloc : ∀ x, ws.map (fun w => localize (binL m e x) w.1 (w.2 - w.1)) = L x
  hdec : ∀ x, WinDecomp (binL m e x) ws
  hforget : ∀ x y, (L x).map (List.map forgetUnit) = (L y).map (List.map forgetUnit)

namespace BinFam

variable {m e : ℕ} (F : BinFam m e)

theorem symEquiv_iff (x y : ℤ × ℤ) :
    SymEquiv (binL m e x) (binL m e y) ↔ LocRel (winLens F.ws) (F.L x) (F.L y) := by
  unfold SymEquiv
  rw [moveEquiv_iff_local (F.hdec x) (F.hdec y), forall_winEq_iff, F.hloc, F.hloc]
  intro w hw i _
  have h := F.hforget y x
  rw [← F.hloc, ← F.hloc, List.map_map, List.map_map] at h
  have hw' := map_eq_map_mem h w hw
  simp only [Function.comp] at hw'
  exact ⟨dim_eq_of_forget hw' i, type_eq_of_forget hw' i⟩

theorem minBin_eq (u : ℤ) : minBin u m e = (binUnits u).filter fun x =>
    ∀ x' ∈ binUnits u, LocRel (winLens F.ws) (F.L x') (F.L x) → enc2 x ≤ enc2 x' :=
  minBin_eq_filter (fun x y => LocRel (winLens F.ws) (F.L x) (F.L y)) fun x _ y _ => F.symEquiv_iff x y

theorem massWt_eq {h : ℕ} {u : ℤ} (hu : u ∈ sqUnits) (x : ℤ × ℤ) (he : 1 ≤ e) (hh : 2 * m + e = h)
    (hN : ∀ w ∈ F.ws, w.2 ≤ h + 2) :
    massWt h u (binL m e x) = (1 / 4 : ℝ) ^ (h - 1) * 6 *
      ((diagOfSpec (specL (winLens F.ws) (F.L x)) : ℚ) : ℝ) * (2 : ℝ) ^ (max m e - min m e) *
      (2 : ℝ) ^ ((locNII'L (winLens F.ws) (F.L x) : ℤ) - (locNIIL (winLens F.ws) (F.L x) : ℤ)) := by
  have hexp : ∀ b ∈ binL m e x, 0 ≤ blockExp b ∧ blockExp b ≤ h := fun b hb => by
    simp only [binL, binList, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · rw [blockExp_binBlock]; omega
    · simp [blockExp]; omega
  have h0 : (blockSymbol (binL m e x) 0).type = .II := by
    cases ht : (blockSymbol (binL m e x) 0).type
    · exfalso; rw [type_binL] at ht; omega
    · rfl
  rw [massWt_eq_local hu (F.hdec x) F.hnd h0 hN (by omega) hexp, prod_locDiag, sum_locNII, sum_locNII', F.hloc,
    crossExp_binL x (by omega) (by omega), sqrt_two_pow_two_mul]
  ring

theorem sum_massWt {h : ℕ} {u : ℤ} (hu : u ∈ sqUnits) (he : 1 ≤ e) (hh : 2 * m + e = h)
    (hN : ∀ w ∈ F.ws, w.2 ≤ h + 2) (L₀ : List (List DyBlock))
    (hL₀ : ∀ x, (F.L x).map (List.map forgetUnit) = L₀) (T N : ℕ)
    (hk : ∀ x ∈ minBin u m e, (∀ t ∈ (specL (winLens F.ws) (F.L x)).flatten, t.dim ≤ 3) ∧
      (specL (winLens F.ws) (F.L x)).flatten.length = T)
    (hS : ((minBin u m e).val.map fun x => natDiagL (specL (winLens F.ws) (F.L x))).sum = N) :
    ∑ x ∈ minBin u m e, massWt h u (binL m e x) = (1 / 4 : ℝ) ^ (h - 1) * 6 * (2 : ℝ) ^ (max m e - min m e) *
      (2 : ℝ) ^ ((locNII'L (winLens F.ws) L₀ : ℤ) - (locNIIL (winLens F.ws) L₀ : ℤ)) * ((N : ℝ) / 6 ^ T) := by
  rw [Finset.sum_congr rfl fun x _ => F.massWt_eq hu x he hh hN]
  have hc : ∀ x, locNII'L (winLens F.ws) (F.L x) = locNII'L (winLens F.ws) L₀ ∧
      locNIIL (winLens F.ws) (F.L x) = locNIIL (winLens F.ws) L₀ := fun x => by
    rw [← hL₀ x, locNII'L_forget, locNIIL_forget]; exact ⟨rfl, rfl⟩
  simp only [hc]
  rw [← sum_diagOfSpec _ _ T N hk hS, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem sum_hasse_massWt {h : ℕ} {u : ℤ} (hu : u ∈ sqUnits) (he : 1 ≤ e) (hh : 2 * m + e = h)
    (hN : ∀ w ∈ F.ws, w.2 ≤ h + 2) (L₀ : List (List DyBlock))
    (hL₀ : ∀ x, (F.L x).map (List.map forgetUnit) = L₀) (p q : ℕ) (hp : m % 2 = p) (hq : (e + 1) % 2 = q)
    (T : ℕ) (N : ℤ)
    (hk : ∀ x ∈ minBin u m e, (∀ t ∈ (specL (winLens F.ws) (F.L x)).flatten, t.dim ≤ 3) ∧
      (specL (winLens F.ws) (F.L x)).flatten.length = T)
    (hS : ((minBin u m e).val.map fun x => hasseList [(p, 1), (p, if x.1 = 3 then 3 else -1),
      (q, (x.2 : ZMod 8))] * natDiagL (specL (winLens F.ws) (F.L x))).sum = N) :
    ∑ x ∈ minBin u m e, (hasseQ (binL m e x) : ℝ) * massWt h u (binL m e x) =
      (1 / 4 : ℝ) ^ (h - 1) * 6 * (2 : ℝ) ^ (max m e - min m e) *
      (2 : ℝ) ^ ((locNII'L (winLens F.ws) L₀ : ℤ) - (locNIIL (winLens F.ws) L₀ : ℤ)) * ((N : ℝ) / 6 ^ T) := by
  rw [Finset.sum_congr rfl fun x _ => by rw [F.massWt_eq hu x he hh hN, hasseQ_binL, hp, hq]]
  have hc : ∀ x, locNII'L (winLens F.ws) (F.L x) = locNII'L (winLens F.ws) L₀ ∧
      locNIIL (winLens F.ws) (F.L x) = locNIIL (winLens F.ws) L₀ := fun x => by
    rw [← hL₀ x, locNII'L_forget, locNIIL_forget]; exact ⟨rfl, rfl⟩
  simp only [hc]
  rw [← sum_mul_diagOfSpec _ _ _ T N hk hS, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

end BinFam

/-! ### Tactics for the generated family files -/

/-- No repeated windows. -/
macro "nd_tac" : tactic => `(tactic| (simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
  Prod.mk.injEq, List.nodup_nil, or_false, not_false_eq_true, and_true, and_self] <;> omega))

/-- Localized lists. -/
macro "hloc_tac" : tactic => `(tactic| (simp only [List.map_cons, List.map_nil, Nat.add_sub_cancel_left,
  Nat.sub_zero, List.cons.injEq, and_true] <;> (repeat' apply And.intro) <;> loc_tac))

/-- Nonempty windows. -/
macro "lt_tac" : tactic => `(tactic| (simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
  forall_const, and_true, implies_true] <;> omega))

/-- Disjoint windows. -/
macro "disj_tac" : tactic => `(tactic| (simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
  forall_const, and_true, implies_true, ne_eq, Prod.mk.injEq, not_true_eq_false, false_implies, true_and,
  not_and] <;> omega))

/-- The exponents lie in the windows. -/
macro "cover_tac" : tactic => `(tactic| (simp only [sqL, sqList, binL, binList, List.forall_mem_cons,
  List.not_mem_nil, IsEmpty.forall_iff, forall_const, and_true, implies_true, blockExp_binBlock,
  List.exists_mem_cons, List.mem_cons, exists_eq_or_imp, exists_eq_left, false_or, or_false,
  forall_eq_or_imp, forall_eq] <;>
  simp only [blockExp] <;> omega))

/-- Parity conditions. -/
macro "par_tac" : tactic => `(tactic| (try simp (disch := first | exact even_two_mul _ |
  exact Nat.not_even_two_mul_add_one _) only [if_pos, if_neg]))

/-- Parity conditions on parameters `2 * k`, `2 * k + 1` (also inside conjunctions). -/
macro "par2_tac" : tactic => `(tactic| (try simp only [Nat.even_add_one, even_two_mul, not_true_eq_false,
  not_false_eq_true, and_true, true_and, and_false, false_and, if_true, if_false, ite_true, ite_false]))

/-- Final real arithmetic. -/
macro "fin_tac" : tactic => `(tactic| (push_cast; (try norm_num); (try simp only [one_div, inv_pow,
  show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]); (try field_simp); (try ring_nf)))

end QuadFormsKB.Dyadic7
