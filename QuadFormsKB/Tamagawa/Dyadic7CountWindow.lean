/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.ConwaySloane.Theorem10

/-!
# Paper 7 at $p = 2$: sign walking and oddity fusion window by window

Tool for the class counts of `Dyadic7.TernaryDyadicMassCount`: deciding Conway–Sloane's equivalence of 2-adic symbols
(`ConwaySloane.MoveEquiv`, sign walking and oddity fusion, *Sphere Packings, Lattices and Groups* Ch. 15, §7.5) **locally**, on finitely many windows of
scales outside of which the two symbols agree.

**Setting.** $\sigma$, $\tau$ are 2-adic symbols (`TwoSymbol`, a function $k \mapsto$ the constituent of scale $2^k$)
with the same dimensions and types at every scale, the same oddities at the type II scales, agreeing (and of type II)
from some scale $2^N$ on. A *window* is an interval of scales $[l, r)$, given as the pair $(l, r)$.

**Defines.**
* `shiftSym σ l`: the symbol $k \mapsto \sigma(l + k)$ (the window seen from its first scale);
* `WinEq f g len`: the local form of Conway–Sloane's Theorem 10 on a window of length `len`: the numbers of minus signs
  of $f$ and $g$ on $[0, len)$ have the same parity, and the prefix invariants
  $G(j) = \sum_{k<j} t_k + 4\sum_{1 \le y \le j}(\#\text{minus signs below } 2^y)$ (`prefixInvariant`) agree at every
  $1 \le j \le len$ with $j = len$ or $f_j$ of type II.

**Proves.** `moveEquiv_iff_winEq`: if $\sigma$ and $\tau$ agree outside pairwise disjoint windows $[l_i, r_i)$, each
*train-aligned* ($l_i = 0$ or the scales $2^{l_i - 1}$, $2^{l_i}$ are of type II; the scales $2^{r_i - 1}$, $2^{r_i}$ are
of type II), then $\sigma \sim \tau$ iff `WinEq` holds on every window. This is Theorem 10 in its prefix form
(`ConwaySloane.sameInvariants_iff_prefix`) with the prefix invariants computed window by window
(`prefixInvariant_add`, `minusBelow_add`).

Indices are 0-based.
-/

namespace QuadFormsKB.Dyadic7

open QuadFormsKB.ConwaySloane Finset

/-- The symbol $k \mapsto \sigma(l + k)$: the scales from $2^l$ on, re-indexed from $0$. -/
def shiftSym (σ : TwoSymbol) (l : ℕ) : TwoSymbol := fun i => σ (l + i)

theorem minusBelow_add (σ : TwoSymbol) (l : ℕ) : ∀ j,
    minusBelow σ (l + j) = minusBelow σ l + minusBelow (shiftSym σ l) j
  | 0 => by simp [minusBelow]
  | j + 1 => by
    show minusBelow σ (l + j) + _ = minusBelow σ l + (minusBelow (shiftSym σ l) j + _)
    rw [minusBelow_add σ l j, Nat.add_assoc]
    rfl

theorem prefixInvariant_add (σ : TwoSymbol) (l : ℕ) : ∀ j,
    prefixInvariant σ (l + j) =
      prefixInvariant σ l + prefixInvariant (shiftSym σ l) j + 4 * (j : ZMod 8) * (minusBelow σ l : ZMod 8)
  | 0 => by simp [prefixInvariant]
  | j + 1 => by
    rw [show l + (j + 1) = (l + j) + 1 from rfl, prefixInvariant_succ, prefixInvariant_succ,
      prefixInvariant_add σ l j, show (l + j) + 1 = l + (j + 1) from rfl, minusBelow_add σ l (j + 1)]
    simp only [shiftSym]
    push_cast
    ring

/-- **The local condition of Theorem 10 on a window** of length `len` (Conway–Sloane, *Sphere Packings, Lattices and Groups* Ch. 15, §7.5, Thm. 10, in
prefix form): the minus signs of $f$ and $g$ on the scales $0, \dots, len - 1$ have the same parity, and the prefix
invariants of $f$ and $g$ agree at every $j \in [1, len]$ with $j = len$ or $f_j$ of type II. -/
def WinEq (f g : TwoSymbol) (len : ℕ) : Prop :=
  4 * (minusBelow f len : ZMod 8) = 4 * (minusBelow g len : ZMod 8) ∧
    ∀ j < len + 1, 1 ≤ j → (j = len ∨ (f j).type = .II) → prefixInvariant f j = prefixInvariant g j

instance (f g : TwoSymbol) (len : ℕ) : Decidable (WinEq f g len) := by
  unfold WinEq; infer_instance

theorem prefixInvariant_congr {f f' : TwoSymbol} {len : ℕ} (h : ∀ i < len, f i = f' i) :
    ∀ j ≤ len, prefixInvariant f j = prefixInvariant f' j
  | 0, _ => rfl
  | j + 1, hj => by
    rw [prefixInvariant_succ, prefixInvariant_succ, prefixInvariant_congr h j (by omega), h j (by omega),
      minusBelow_congr (fun k hk => by rw [h k (by omega)])]

/-- `WinEq` only depends on the scales $0, \dots, len - 1$ of the two symbols. -/
theorem winEq_congr {f g f' g' : TwoSymbol} {len : ℕ} (hf : ∀ i < len, f i = f' i) (hg : ∀ i < len, g i = g' i) :
    WinEq f g len ↔ WinEq f' g' len := by
  unfold WinEq
  rw [minusBelow_congr (fun k hk => by rw [hf k hk]), minusBelow_congr (σ := g) (fun k hk => by rw [hg k hk])]
  refine and_congr_right fun _ => forall_congr' fun j => imp_congr_right fun hj => imp_congr_right fun _ => ?_
  rw [prefixInvariant_congr hf j (by omega), prefixInvariant_congr hg j (by omega)]
  have ht : (j = len ∨ (f j).type = .II) ↔ (j = len ∨ (f' j).type = .II) := by
    rcases Nat.lt_or_ge j len with h | h
    · rw [hf j h]
    · simp [show j = len by omega]
  rw [ht]

/-- The point $m$ lies strictly inside the window $w = (l, r)$: $l < m < r$. -/
def StrictIn (w : ℕ × ℕ) (m : ℕ) : Prop := w.1 < m ∧ m < w.2

theorem typeII_iff_not_isTypeI (σ : TwoSymbol) (k : ℕ) : (σ k).type = .II ↔ ¬ IsTypeI σ k := by
  unfold IsTypeI; cases (σ k).type <;> simp

/-- **Sign walking and oddity fusion, window by window.** Let $\sigma$, $\tau$ be 2-adic symbols with the same
dimensions (`hdim`) and types (`htype`) at every scale and the same oddities at the type II scales (`hodd`), agreeing and
of type II from the scale $2^N$ on (`hN`). Let `ws` be a list of windows $(l, r)$ ending by $N$ (`hwN`), pairwise
disjoint (`hdisj`), train-aligned (`hal`: $l < r$; $l = 0$ or $2^{l-1}$, $2^l$ of type II; $2^{r-1}$, $2^r$ of type II),
such that $\sigma$ and $\tau$ agree at every scale outside the windows (`hout`). Then $\sigma \sim \tau$ (`MoveEquiv`)
iff `WinEq` holds on every window. -/
@[kb "conwaysloane1999" "Ch. 15, §7.5, Thm. 10, p. 381 (prefix form, window by window)"]
theorem moveEquiv_iff_winEq {σ τ : TwoSymbol} {N : ℕ} (ws : List (ℕ × ℕ))
    (hdim : ∀ k, (τ k).dim = (σ k).dim) (htype : ∀ k, (τ k).type = (σ k).type)
    (hodd : ∀ k, ¬ IsTypeI σ k → (τ k).oddity = (σ k).oddity)
    (hN : ∀ k, N ≤ k → τ k = σ k ∧ ¬ IsTypeI σ k)
    (hwN : ∀ w ∈ ws, w.2 ≤ N)
    (hout : ∀ k, (∀ w ∈ ws, ¬ (w.1 ≤ k ∧ k < w.2)) → τ k = σ k)
    (hdisj : ∀ w ∈ ws, ∀ w' ∈ ws, w ≠ w' → w.2 ≤ w'.1 ∨ w'.2 ≤ w.1)
    (hal : ∀ w ∈ ws, w.1 < w.2 ∧ (w.1 = 0 ∨ (¬ IsTypeI σ (w.1 - 1) ∧ ¬ IsTypeI σ w.1)) ∧
      ¬ IsTypeI σ (w.2 - 1) ∧ ¬ IsTypeI σ w.2) :
    MoveEquiv σ τ ↔ ∀ w ∈ ws, WinEq (shiftSym σ w.1) (shiftSym τ w.1) (w.2 - w.1) := by
  have hT : Theorem10Setting σ τ N :=
    ⟨hdim, htype, hodd, fun k hk => (hN k hk).1, fun k hk => (hN k hk).2⟩
  rw [moveEquiv_iff_sameInvariants hT.typeII_of_le, sameInvariants_iff_prefix hT]
  -- `C m`: the prefix invariants and the minus parities agree at `m`
  let C : ℕ → Prop := fun m => prefixInvariant σ m = prefixInvariant τ m ∧
    4 * (minusBelow σ m : ZMod 8) = 4 * (minusBelow τ m : ZMod 8)
  have C0 : C 0 := ⟨rfl, rfl⟩
  -- agreement at `m` propagates `C`
  have Cstep : ∀ m, C m → τ m = σ m → C (m + 1) := by
    rintro m ⟨h1, h2⟩ he
    refine ⟨?_, ?_⟩
    · rw [prefixInvariant_succ, prefixInvariant_succ, h1, he]
      simp only [minusBelow, Nat.cast_add, mul_add, h2, he]
    · simp only [minusBelow, Nat.cast_add, mul_add, h2, he]
  -- the window formulas, from a point where `C` holds
  have Cwin : ∀ l j, C l → (prefixInvariant σ (l + j) = prefixInvariant τ (l + j) ↔
      prefixInvariant (shiftSym σ l) j = prefixInvariant (shiftSym τ l) j) ∧
      (4 * (minusBelow σ (l + j) : ZMod 8) = 4 * (minusBelow τ (l + j) : ZMod 8) ↔
        4 * (minusBelow (shiftSym σ l) j : ZMod 8) = 4 * (minusBelow (shiftSym τ l) j : ZMod 8)) := by
    rintro l j ⟨h1, h2⟩
    rw [prefixInvariant_add σ l j, prefixInvariant_add τ l j, minusBelow_add σ l j, minusBelow_add τ l j, h1]
    have e : 4 * (j : ZMod 8) * (minusBelow σ l : ZMod 8) = 4 * (j : ZMod 8) * (minusBelow τ l : ZMod 8) := by
      rw [mul_comm 4 (j : ZMod 8), mul_assoc, h2, ← mul_assoc]
    rw [e]
    push_cast
    rw [mul_add, mul_add, h2]
    exact ⟨⟨fun h => by linear_combination h, fun h => by linear_combination h⟩,
      ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩⟩
  -- two adjacent type II scales: equal prefix invariants force equal minus parity
  have Cpair : ∀ m, ¬ IsTypeI σ m → prefixInvariant σ m = prefixInvariant τ m →
      prefixInvariant σ (m + 1) = prefixInvariant τ (m + 1) → C (m + 1) := by
    intro m hm h1 h2
    refine ⟨h2, ?_⟩
    rw [prefixInvariant_succ, prefixInvariant_succ, h1, hodd m hm] at h2
    linear_combination h2
  constructor
  · -- MoveEquiv ⇒ WinEq on each window
    rintro ⟨-, hG⟩ w hw
    obtain ⟨hlr, hl, hr1, hr⟩ := hal w hw
    have hGe : ∀ m, ¬ IsTypeI σ m → prefixInvariant σ m = prefixInvariant τ m := fun m hm => (hG m hm).symm
    have Cl : C w.1 := by
      by_cases hw0 : w.1 = 0
      · rw [hw0]; exact C0
      rcases hl with h0 | ⟨h1, h2⟩
      · exact absurd h0 hw0
      · have := Cpair (w.1 - 1) h1 (hGe _ h1) (by rw [Nat.sub_add_cancel (by omega)]; exact hGe _ h2)
        rwa [Nat.sub_add_cancel (by omega)] at this
    have Cr : C w.2 := by
      have := Cpair (w.2 - 1) hr1 (hGe _ hr1) (by rw [Nat.sub_add_cancel (by omega)]; exact hGe _ hr)
      rwa [Nat.sub_add_cancel (by omega)] at this
    refine ⟨?_, fun j hj h1 hj' => ?_⟩
    · have := (Cwin w.1 (w.2 - w.1) Cl).2
      rw [Nat.add_sub_cancel' hlr.le] at this
      exact this.mp Cr.2
    · refine (Cwin w.1 j Cl).1.mp (hGe _ ?_)
      rcases hj' with rfl | h
      · rw [Nat.add_sub_cancel' hlr.le]; exact hr
      · exact (typeII_iff_not_isTypeI _ _).mp h
  · -- WinEq on each window ⇒ MoveEquiv
    intro hW
    -- `C` holds at every point not strictly inside a window
    have key : ∀ m, (∀ w ∈ ws, ¬ StrictIn w m) → C m := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro hm
        rcases Nat.eq_zero_or_pos m with rfl | hpos
        · exact C0
        obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        by_cases hin : ∃ w ∈ ws, w.1 ≤ m ∧ m < w.2
        · obtain ⟨w, hw, h1, h2⟩ := hin
          have hr : m + 1 = w.2 := by
            by_contra hne
            exact hm w hw ⟨by omega, by omega⟩
          -- `C` at the start of the window
          have Cl : C w.1 := ih w.1 (by omega) fun w' hw' hs => by
            by_cases hww : w = w'
            · subst hww; exact absurd hs.1 (lt_irrefl _)
            · rcases hdisj w hw w' hw' hww with h | h
              · have := hal w hw; unfold StrictIn at hs; omega
              · unfold StrictIn at hs; omega
          obtain ⟨hp, -⟩ := hW w hw
          have hlr := (hal w hw).1
          refine ⟨?_, ?_⟩
          · have := (Cwin w.1 (w.2 - w.1) Cl).1
            rw [Nat.add_sub_cancel' hlr.le] at this
            rw [hr]
            exact this.mpr ((hW w hw).2 _ (by omega) (by omega) (Or.inl rfl))
          · have := (Cwin w.1 (w.2 - w.1) Cl).2
            rw [Nat.add_sub_cancel' hlr.le] at this
            rw [hr]
            exact this.mpr hp
        · push Not at hin
          exact Cstep m (ih m (by omega) fun w hw hs => by
            have := hin w hw; unfold StrictIn at hs; omega) (hout m fun w hw h => by have := hin w hw h.1; omega)
    refine ⟨?_, fun m hm => ?_⟩
    · exact (key N fun w hw hs => by have := hwN w hw; unfold StrictIn at hs; omega).2.symm
    · by_cases hs : ∃ w ∈ ws, StrictIn w m
      · obtain ⟨w, hw, h1, h2⟩ := hs
        have Cl : C w.1 := key w.1 fun w' hw' hs => by
          by_cases hww : w = w'
          · subst hww; exact absurd hs.1 (lt_irrefl _)
          · rcases hdisj w hw w' hw' hww with h | h
            · have := hal w hw; unfold StrictIn at hs; omega
            · unfold StrictIn at hs; omega
        have := (Cwin w.1 (m - w.1) Cl).1
        rw [Nat.add_sub_cancel' h1.le] at this
        refine (this.mpr ((hW w hw).2 (m - w.1) (by omega) (by omega) (Or.inr ?_))).symm
        rw [typeII_iff_not_isTypeI]
        unfold IsTypeI shiftSym
        rw [Nat.add_sub_cancel' h1.le]
        exact hm
      · push Not at hs
        exact (key m hs).1.symm

end QuadFormsKB.Dyadic7
