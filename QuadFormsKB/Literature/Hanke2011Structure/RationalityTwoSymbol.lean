/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.PMass

/-!
# Paper 6, Theorem 5.4 at $p = 2$: gluing 2-adic symbols across a gap

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Thm. 5.4, proof, p. 24 ("the variation of $c_J$ with the scales of the trains
comes purely from the cross product factor").

This file is purely combinatorial: it works with Conway–Sloane 2-adic symbols (`ConwaySloane.TwoSymbol`, the function
$k \mapsto$ the constituent of scale $2^k$, with dimension, sign, type and oddity), the moves of sign walking and oddity
fusion (`ConwaySloane.MoveEquiv`) and the 2-mass $m_2$ of formula (3) of Conway–Sloane 1988 (`Mass.pMassTwo`).

For a cut $c \in \mathbb N$ and two symbols $\sigma$, $\tau$, `glueS c σ τ` is the symbol equal to $\sigma$ at the scales
$2^k$, $k \le c$, and to $\tau$ at the scales $k > c$.  When $\sigma$ has no type I constituent at the scales $k \ge c$
and $\tau$ none at the scales $k \le c+1$ (in particular when there are two adjacent zero-dimensional constituents of
scales $2^c$, $2^{c+1}$ between them), no move crosses the cut:

* `moveEquiv_glue`: moves of $\sigma$ and of $\tau$ give moves of the glued symbol;
* `moveEquiv_split`: conversely, if the constituents of scales $2^c$, $2^{c+1}$ of $\sigma$ have type II, every move of
  $\sigma$ is a move of its part below the cut (`lowS`) or of its part above the cut (`highS`).

`shS σ` shifts a symbol up by one scale (inserting a zero-dimensional constituent at scale $1$).  Shifting is compatible
with the moves in both directions (`moveEquiv_shS`, `moveEquiv_of_shS`; the converse direction goes through the
invariants of Conway–Sloane's Theorem 10, `ConwaySloane.moveEquiv_iff_sameInvariants`, because a sign may walk onto the
new zero-dimensional constituent).

The 2-mass is multiplicative across such a cut up to the cross term (`pMassTwo_glue`):
$$m_2(\sigma \mathbin{|_c} \tau) = m_2(\sigma)\,m_2(\tau)\,\sqrt2^{\,\sum_{k<k'}(k'-k)\,n_k(\sigma)\,n_{k'}(\tau)},$$
and invariant under the shift (`pMassTwo_shS`).

Indices are 0-based.
-/

open Finset

namespace QuadFormsKB.Hanke2011Structure.RatTwo

open QuadFormsKB.ConwaySloane QuadFormsKB.ConwaySloane.Mass

/-! ### Gluing and cutting symbols -/

/-- The trivial symbol: every constituent zero-dimensional. -/
def trivS : TwoSymbol := fun _ => TwoFactor.trivial

/-- **Gluing at the cut $c$**: the symbol equal to $\sigma$ at the scales $2^k$, $k \le c$, and to $\tau$ at the scales
$2^k$, $k > c$. -/
def glueS (c : ℕ) (σ τ : TwoSymbol) : TwoSymbol := fun k => if k ≤ c then σ k else τ k

/-- The part of $\sigma$ at the scales $2^k$, $k \le c$ (trivial above). -/
def lowS (c : ℕ) (σ : TwoSymbol) : TwoSymbol := glueS c σ trivS

/-- The part of $\sigma$ at the scales $2^k$, $k > c$ (trivial below). -/
def highS (c : ℕ) (σ : TwoSymbol) : TwoSymbol := glueS c trivS σ

/-- $\sigma$ has no type I constituent at the scales $2^k$, $k \ge c$. -/
def NoIAbove (c : ℕ) (σ : TwoSymbol) : Prop := ∀ k, c ≤ k → ¬ IsTypeI σ k

/-- $\tau$ has no type I constituent at the scales $2^k$, $k \le c + 1$. -/
def NoIBelow (c : ℕ) (τ : TwoSymbol) : Prop := ∀ k, k ≤ c + 1 → ¬ IsTypeI τ k

/-- The constituents of scales $2^c$ and $2^{c+1}$ have type II. -/
def GapAt (c : ℕ) (σ : TwoSymbol) : Prop := ¬ IsTypeI σ c ∧ ¬ IsTypeI σ (c + 1)

theorem not_isTypeI_trivial : ¬ (TwoFactor.trivial.type = ScaledType.I) := by decide

theorem MoveEquiv.isTypeI_iff {σ τ : TwoSymbol} (h : MoveEquiv σ τ) (k : ℕ) : IsTypeI τ k ↔ IsTypeI σ k :=
  h.sameInvariants.isTypeI_iff k

theorem MoveEquiv.noIAbove {c : ℕ} {σ τ : TwoSymbol} (h : MoveEquiv σ τ) (hσ : NoIAbove c σ) : NoIAbove c τ :=
  fun k hk => by rw [MoveEquiv.isTypeI_iff h]; exact hσ k hk

theorem MoveEquiv.noIBelow {c : ℕ} {σ τ : TwoSymbol} (h : MoveEquiv σ τ) (hσ : NoIBelow c σ) : NoIBelow c τ :=
  fun k hk => by rw [MoveEquiv.isTypeI_iff h]; exact hσ k hk

theorem MoveEquiv.gapAt {c : ℕ} {σ τ : TwoSymbol} (h : MoveEquiv σ τ) (hσ : GapAt c σ) : GapAt c τ := by
  unfold GapAt; rw [MoveEquiv.isTypeI_iff h, MoveEquiv.isTypeI_iff h]; exact hσ

theorem glueS_low_high (c : ℕ) (σ : TwoSymbol) : glueS c (lowS c σ) (highS c σ) = σ := by
  funext k; unfold glueS lowS highS; by_cases hk : k ≤ c <;> simp [hk, glueS]

/-! ### Moves and gluing -/

theorem step_glue_left {c : ℕ} {σ σ' : TwoSymbol} (τ : TwoSymbol) (h : Step σ σ') (hσ : NoIAbove c σ) :
    Step (glueS c σ τ) (glueS c σ' τ) := by
  cases h with
  | walk j i hi hI =>
    have hic : i < c := by
      by_contra hc; exact hσ i (by omega) hI
    have e : glueS c (walkStep σ j i) τ = walkStep (glueS c σ τ) j i := by
      funext k
      by_cases hk : k ≤ c
      · simp [glueS, walkStep, hk]
      · have h1 : ¬ (k = j ∨ k = j + 1) := by omega
        have h2 : k ≠ i := by omega
        simp only [glueS, walkStep, hk, if_false, h1, h2]
    rw [e]
    exact Step.walk _ j i hi (by unfold IsTypeI glueS; rw [if_pos (by omega)]; exact hI)
  | fuse j a h₁ h₂ =>
    have hjc : j + 1 < c := by
      by_contra hc; exact hσ (j + 1) (by omega) h₂
    have e : glueS c (fuseStep σ j a) τ = fuseStep (glueS c σ τ) j a := by
      funext k
      by_cases hk : k ≤ c
      · simp [glueS, fuseStep, hk]
      · have h1 : k ≠ j := by omega
        have h2 : k ≠ j + 1 := by omega
        simp only [glueS, fuseStep, hk, if_false, h1, h2]
    rw [e]
    exact Step.fuse _ j a (by unfold IsTypeI glueS; rw [if_pos (by omega)]; exact h₁)
      (by unfold IsTypeI glueS; rw [if_pos (by omega)]; exact h₂)

theorem step_glue_right {c : ℕ} (σ : TwoSymbol) {τ τ' : TwoSymbol} (h : Step τ τ') (hτ : NoIBelow c τ) :
    Step (glueS c σ τ) (glueS c σ τ') := by
  cases h with
  | walk j i hi hI =>
    have hic : c + 1 < i := by
      by_contra hc; exact hτ i (by omega) hI
    have e : glueS c σ (walkStep τ j i) = walkStep (glueS c σ τ) j i := by
      funext k
      by_cases hk : k ≤ c
      · have h1 : ¬ (k = j ∨ k = j + 1) := by omega
        have h2 : k ≠ i := by omega
        simp only [glueS, walkStep, hk, if_true, h1, h2, if_false]
      · simp [glueS, walkStep, hk]
    rw [e]
    exact Step.walk _ j i hi (by unfold IsTypeI glueS; rw [if_neg (by omega)]; exact hI)
  | fuse j a h₁ h₂ =>
    have hjc : c + 1 < j := by
      by_contra hc; exact hτ j (by omega) h₁
    have e : glueS c σ (fuseStep τ j a) = fuseStep (glueS c σ τ) j a := by
      funext k
      by_cases hk : k ≤ c
      · have h1 : k ≠ j := by omega
        have h2 : k ≠ j + 1 := by omega
        simp only [glueS, fuseStep, hk, if_true, h1, h2, if_false]
      · simp [glueS, fuseStep, hk]
    rw [e]
    exact Step.fuse _ j a (by unfold IsTypeI glueS; rw [if_neg (by omega)]; exact h₁)
      (by unfold IsTypeI glueS; rw [if_neg (by omega)]; exact h₂)

theorem moveEquiv_glue_left {c : ℕ} (τ : TwoSymbol) {σ σ' : TwoSymbol} (h : MoveEquiv σ σ') :
    NoIAbove c σ → MoveEquiv (glueS c σ τ) (glueS c σ' τ) := by
  induction h with
  | rel a b hab => intro hA; exact Relation.EqvGen.rel _ _ (step_glue_left τ hab hA)
  | refl a => intro _; exact Relation.EqvGen.refl _
  | symm a b hab ih =>
    intro hB
    exact Relation.EqvGen.symm _ _ (ih (MoveEquiv.noIAbove (Relation.EqvGen.symm _ _ hab) hB))
  | trans a b d hab hbd ih₁ ih₂ =>
    intro hA
    exact Relation.EqvGen.trans _ _ _ (ih₁ hA) (ih₂ (MoveEquiv.noIAbove hab hA))

theorem moveEquiv_glue_right {c : ℕ} (σ : TwoSymbol) {τ τ' : TwoSymbol} (h : MoveEquiv τ τ') :
    NoIBelow c τ → MoveEquiv (glueS c σ τ) (glueS c σ τ') := by
  induction h with
  | rel a b hab => intro hA; exact Relation.EqvGen.rel _ _ (step_glue_right σ hab hA)
  | refl a => intro _; exact Relation.EqvGen.refl _
  | symm a b hab ih =>
    intro hB
    exact Relation.EqvGen.symm _ _ (ih (MoveEquiv.noIBelow (Relation.EqvGen.symm _ _ hab) hB))
  | trans a b d hab hbd ih₁ ih₂ =>
    intro hA
    exact Relation.EqvGen.trans _ _ _ (ih₁ hA) (ih₂ (MoveEquiv.noIBelow hab hA))

/-- **Moves of the two parts give moves of the glued symbol** (no move crosses a cut with no type I constituent at the
scales $2^c$, $2^{c+1}$). -/
theorem moveEquiv_glue {c : ℕ} {σ σ' τ τ' : TwoSymbol} (hσ : MoveEquiv σ σ') (hτ : MoveEquiv τ τ')
    (hσc : NoIAbove c σ) (hτc : NoIBelow c τ) : MoveEquiv (glueS c σ τ) (glueS c σ' τ') :=
  Relation.EqvGen.trans _ _ _ (moveEquiv_glue_left τ hσ hσc) (moveEquiv_glue_right σ' hτ hτc)

theorem step_split {c : ℕ} {σ σ' : TwoSymbol} (h : Step σ σ') (hg : GapAt c σ) :
    MoveEquiv (lowS c σ) (lowS c σ') ∧ MoveEquiv (highS c σ) (highS c σ') := by
  cases h with
  | walk j i hi hI =>
    have hic : i ≠ c ∧ i ≠ c + 1 := ⟨fun h => hg.1 (h ▸ hI), fun h => hg.2 (h ▸ hI)⟩
    by_cases hlt : i < c
    · refine ⟨?_, ?_⟩
      · have e : lowS c (walkStep σ j i) = walkStep (lowS c σ) j i := by
          funext k
          by_cases hk : k ≤ c
          · simp [lowS, glueS, walkStep, hk]
          · have h1 : ¬ (k = j ∨ k = j + 1) := by omega
            have h2 : k ≠ i := by omega
            simp only [lowS, glueS, walkStep, hk, if_false, h1, h2]
        rw [e]
        exact Relation.EqvGen.rel _ _ (Step.walk _ j i hi (by
          unfold IsTypeI lowS glueS; rw [if_pos (by omega)]; exact hI))
      · have e : highS c (walkStep σ j i) = highS c σ := by
          funext k
          by_cases hk : k ≤ c
          · simp [highS, glueS, hk]
          · have h1 : ¬ (k = j ∨ k = j + 1) := by omega
            have h2 : k ≠ i := by omega
            simp only [highS, glueS, walkStep, hk, if_false, h1, h2]
        rw [e]; exact Relation.EqvGen.refl _
    · have hgt : c + 1 < i := by omega
      refine ⟨?_, ?_⟩
      · have e : lowS c (walkStep σ j i) = lowS c σ := by
          funext k
          by_cases hk : k ≤ c
          · have h1 : ¬ (k = j ∨ k = j + 1) := by omega
            have h2 : k ≠ i := by omega
            simp only [lowS, glueS, walkStep, hk, if_true, h1, h2, if_false]
          · simp [lowS, glueS, hk]
        rw [e]; exact Relation.EqvGen.refl _
      · have e : highS c (walkStep σ j i) = walkStep (highS c σ) j i := by
          funext k
          by_cases hk : k ≤ c
          · have h1 : ¬ (k = j ∨ k = j + 1) := by omega
            have h2 : k ≠ i := by omega
            simp only [highS, glueS, walkStep, hk, if_true, h1, h2, if_false]
          · simp [highS, glueS, walkStep, hk]
        rw [e]
        exact Relation.EqvGen.rel _ _ (Step.walk _ j i hi (by
          unfold IsTypeI highS glueS; rw [if_neg (by omega)]; exact hI))
  | fuse j a h₁ h₂ =>
    have hjc : j ≠ c ∧ j ≠ c + 1 ∧ j + 1 ≠ c ∧ j + 1 ≠ c + 1 :=
      ⟨fun h => hg.1 (h ▸ h₁), fun h => hg.2 (h ▸ h₁), fun h => hg.1 (h ▸ h₂), fun h => hg.2 (h ▸ h₂)⟩
    by_cases hlt : j < c
    · have hlt' : j + 1 < c := by omega
      refine ⟨?_, ?_⟩
      · have e : lowS c (fuseStep σ j a) = fuseStep (lowS c σ) j a := by
          funext k
          by_cases hk : k ≤ c
          · simp [lowS, glueS, fuseStep, hk]
          · have h1 : k ≠ j := by omega
            have h2 : k ≠ j + 1 := by omega
            simp only [lowS, glueS, fuseStep, hk, if_false, h1, h2]
        rw [e]
        exact Relation.EqvGen.rel _ _ (Step.fuse _ j a
          (by unfold IsTypeI lowS glueS; rw [if_pos (by omega)]; exact h₁)
          (by unfold IsTypeI lowS glueS; rw [if_pos (by omega)]; exact h₂))
      · have e : highS c (fuseStep σ j a) = highS c σ := by
          funext k
          by_cases hk : k ≤ c
          · simp [highS, glueS, hk]
          · have h1 : k ≠ j := by omega
            have h2 : k ≠ j + 1 := by omega
            simp only [highS, glueS, fuseStep, hk, if_false, h1, h2]
        rw [e]; exact Relation.EqvGen.refl _
    · have hgt : c + 1 < j := by omega
      refine ⟨?_, ?_⟩
      · have e : lowS c (fuseStep σ j a) = lowS c σ := by
          funext k
          by_cases hk : k ≤ c
          · have h1 : k ≠ j := by omega
            have h2 : k ≠ j + 1 := by omega
            simp only [lowS, glueS, fuseStep, hk, if_true, h1, h2, if_false]
          · simp [lowS, glueS, hk]
        rw [e]; exact Relation.EqvGen.refl _
      · have e : highS c (fuseStep σ j a) = fuseStep (highS c σ) j a := by
          funext k
          by_cases hk : k ≤ c
          · have h1 : k ≠ j := by omega
            have h2 : k ≠ j + 1 := by omega
            simp only [highS, glueS, fuseStep, hk, if_true, h1, h2, if_false]
          · simp [highS, glueS, fuseStep, hk]
        rw [e]
        exact Relation.EqvGen.rel _ _ (Step.fuse _ j a
          (by unfold IsTypeI highS glueS; rw [if_neg (by omega)]; exact h₁)
          (by unfold IsTypeI highS glueS; rw [if_neg (by omega)]; exact h₂))

/-- **No move crosses a gap**: if the constituents of scales $2^c$, $2^{c+1}$ of $\sigma$ have type II, a chain of
moves from $\sigma$ to $\tau$ gives chains of moves between their parts below and above the cut. -/
theorem moveEquiv_split {c : ℕ} {σ τ : TwoSymbol} (h : MoveEquiv σ τ) :
    GapAt c σ → MoveEquiv (lowS c σ) (lowS c τ) ∧ MoveEquiv (highS c σ) (highS c τ) := by
  induction h with
  | rel a b hab => intro hA; exact step_split hab hA
  | refl a => intro _; exact ⟨Relation.EqvGen.refl _, Relation.EqvGen.refl _⟩
  | symm a b hab ih =>
    intro hB
    obtain ⟨h1, h2⟩ := ih (MoveEquiv.gapAt (Relation.EqvGen.symm _ _ hab) hB)
    exact ⟨Relation.EqvGen.symm _ _ h1, Relation.EqvGen.symm _ _ h2⟩
  | trans a b d hab hbd ih₁ ih₂ =>
    intro hA
    obtain ⟨h1, h2⟩ := ih₁ hA
    obtain ⟨h3, h4⟩ := ih₂ (MoveEquiv.gapAt hab hA)
    exact ⟨Relation.EqvGen.trans _ _ _ h1 h3, Relation.EqvGen.trans _ _ _ h2 h4⟩

/-! ### Shifting a symbol up by one scale -/

/-- **The shift**: $\sigma$ moved up by one scale, with a zero-dimensional constituent at scale $1$. -/
def shS (σ : TwoSymbol) : TwoSymbol := fun k => match k with
  | 0 => TwoFactor.trivial
  | k + 1 => σ k

@[simp] theorem shS_zero (σ : TwoSymbol) : shS σ 0 = TwoFactor.trivial := rfl
@[simp] theorem shS_succ (σ : TwoSymbol) (k : ℕ) : shS σ (k + 1) = σ k := rfl

theorem step_shS {σ τ : TwoSymbol} (h : Step σ τ) : Step (shS σ) (shS τ) := by
  cases h with
  | walk j i hi hI =>
    have e : shS (walkStep σ j i) = walkStep (shS σ) (j + 1) (i + 1) := by
      funext k
      cases k with
      | zero => simp only [shS_zero, walkStep]; simp
      | succ k => simp [walkStep]
    rw [e]
    exact Step.walk _ (j + 1) (i + 1) (by omega) hI
  | fuse j a h₁ h₂ =>
    have e : shS (fuseStep σ j a) = fuseStep (shS σ) (j + 1) a := by
      funext k
      cases k with
      | zero => simp only [shS_zero, fuseStep]; simp
      | succ k => simp [fuseStep]
    rw [e]
    exact Step.fuse _ (j + 1) a h₁ h₂

/-- Moves commute with the shift. -/
theorem moveEquiv_shS {σ τ : TwoSymbol} (h : MoveEquiv σ τ) : MoveEquiv (shS σ) (shS τ) := by
  induction h with
  | rel a b hab => exact Relation.EqvGen.rel _ _ (step_shS hab)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b d _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem minusBelow_shS (σ : TwoSymbol) : ∀ y, minusBelow (shS σ) (y + 1) = minusBelow σ y
  | 0 => by simp [minusBelow, TwoFactor.trivial]
  | y + 1 => by
    show minusBelow (shS σ) (y + 1) + _ = minusBelow σ y + _
    rw [minusBelow_shS σ y]
    rfl

theorem sum_Icc_succ {M : Type*} [AddCommMonoid M] (f : ℕ → M) (a b : ℕ) :
    ∑ j ∈ Icc (a + 1) (b + 1), f j = ∑ j ∈ Icc a b, f (j + 1) := by
  rw [← Finset.map_add_right_Icc a b 1, Finset.sum_map]
  rfl

theorem sameInvariants_of_shS {σ τ : TwoSymbol} (h : SameInvariants (shS σ) (shS τ)) : SameInvariants σ τ where
  dim_eq k := h.dim_eq (k + 1)
  type_eq k := h.type_eq (k + 1)
  oddity_typeII k hk := h.oddity_typeII (k + 1) hk
  boundary y hy := by
    have := h.boundary (y + 1) hy
    rwa [minusBelow_shS, minusBelow_shS] at this
  compartment c₁ c₂ hC := by
    have hC' : IsCompartment (shS σ) (c₁ + 1) (c₂ + 1) := by
      obtain ⟨h1, h2, h3, h4⟩ := hC
      refine ⟨by omega, fun x hx1 hx2 => ?_, Or.inr ?_, h4⟩
      · obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
        exact h2 x' (by omega) (by omega)
      · rw [Nat.add_sub_cancel]
        rcases c₁ with _ | c'
        · exact not_isTypeI_trivial
        · rcases h3 with h3 | h3
          · exact absurd h3 (by omega)
          · exact h3
    have := h.compartment _ _ hC'
    unfold compartmentInvariant at this ⊢
    simp only [sum_Icc_succ, minusBelow_shS, shS_succ] at this
    exact this

/-- **Unshifting**: if the shifts of $\sigma$, $\tau$ are related by moves, so are $\sigma$, $\tau$ (for $\sigma$ with
finitely many type I constituents). -/
theorem moveEquiv_of_shS {σ τ : TwoSymbol} {B : ℕ} (hB : ∀ k, B ≤ k → ¬ IsTypeI σ k)
    (h : MoveEquiv (shS σ) (shS τ)) : MoveEquiv σ τ := by
  have hB' : ∀ k, B + 1 ≤ k → ¬ IsTypeI (shS σ) k := by
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact hB k' (by omega)
  exact (moveEquiv_iff_sameInvariants hB).2 (sameInvariants_of_shS ((moveEquiv_iff_sameInvariants hB').1 h))

/-! ### The 2-mass of a glued symbol -/

theorem trivS_apply (k : ℕ) : trivS k = TwoFactor.trivial := rfl

theorem species_free_trivial {σ : TwoSymbol} {k : ℕ} (hk : σ k = TwoFactor.trivial) (hb : ¬ IsBound σ k) :
    (twoSpecies (σ k) (IsBound σ k)).diagFactor 2 = 1 := by
  rw [hk, twoSpecies_trivial_free hb]; rfl

theorem isBound_congr {σ τ : TwoSymbol} {k : ℕ} (h1 : k ≠ 0 → (IsTypeI σ (k - 1) ↔ IsTypeI τ (k - 1)))
    (h2 : IsTypeI σ (k + 1) ↔ IsTypeI τ (k + 1)) : IsBound σ k ↔ IsBound τ k := by
  unfold IsBound
  constructor
  · rintro (⟨hk, h⟩ | h)
    · exact Or.inl ⟨hk, (h1 hk).1 h⟩
    · exact Or.inr (h2.1 h)
  · rintro (⟨hk, h⟩ | h)
    · exact Or.inl ⟨hk, (h1 hk).2 h⟩
    · exact Or.inr (h2.2 h)

section Glue

variable {c N : ℕ} {σ τ : TwoSymbol}

theorem diagProdTwo_glue (hσ : ∀ k, c ≤ k → σ k = TwoFactor.trivial)
    (hτ : ∀ k, k ≤ c + 1 → τ k = TwoFactor.trivial) :
    diagProdTwo (glueS c σ τ) N = diagProdTwo σ N * diagProdTwo τ N := by
  unfold diagProdTwo
  have hh : halfFactor (glueS c σ τ) = halfFactor σ := by
    unfold halfFactor glueS; rw [if_pos (Nat.zero_le c)]
  have hh' : halfFactor τ = 1 := by
    unfold halfFactor; rw [hτ 0 (by omega)]; rfl
  rw [hh, hh', one_mul, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  have nI : ∀ (ρ : TwoSymbol) j, ρ j = TwoFactor.trivial → ¬ IsTypeI ρ j := fun ρ j h => by
    unfold IsTypeI; rw [h]; exact not_isTypeI_trivial
  by_cases hk : k ≤ c
  · -- the constituent belongs to σ; τ is trivial and free here
    have hb : IsBound (glueS c σ τ) k ↔ IsBound σ k := by
      refine isBound_congr (fun _ => ?_) ?_
      · unfold IsTypeI glueS; rw [if_pos (by omega)]
      · by_cases hk1 : k + 1 ≤ c
        · unfold IsTypeI glueS; rw [if_pos hk1]
        · have e : k + 1 = c + 1 := by omega
          rw [e]
          exact ⟨fun h => absurd h (by unfold IsTypeI glueS; rw [if_neg (by omega)]; exact nI τ _ (hτ _ le_rfl)),
            fun h => absurd h (nI σ _ (hσ _ (by omega)))⟩
    have hτk : (twoSpecies (τ k) (IsBound τ k)).diagFactor 2 = 1 := by
      refine species_free_trivial (hτ k (by omega)) ?_
      rintro (⟨-, h⟩ | h)
      · exact nI τ _ (hτ _ (by omega)) h
      · exact nI τ _ (hτ _ (by omega)) h
    rw [hτk, mul_one]
    have e : glueS c σ τ k = σ k := by unfold glueS; rw [if_pos hk]
    simp only [e]
    exact congrArg (fun s => Species.diagFactor 2 s) (twoSpecies_congr hb rfl rfl rfl)
  · have hb : IsBound (glueS c σ τ) k ↔ IsBound τ k := by
      refine isBound_congr (fun _ => ?_) ?_
      · by_cases hk1 : k - 1 ≤ c
        · have e : k - 1 = c := by omega
          rw [e]
          exact ⟨fun h => absurd h (by unfold IsTypeI glueS; rw [if_pos le_rfl]; exact nI σ _ (hσ _ le_rfl)),
            fun h => absurd h (nI τ _ (hτ _ (by omega)))⟩
        · unfold IsTypeI glueS; rw [if_neg hk1]
      · unfold IsTypeI glueS; rw [if_neg (by omega)]
    have hσk : (twoSpecies (σ k) (IsBound σ k)).diagFactor 2 = 1 := by
      refine species_free_trivial (hσ k (by omega)) ?_
      rintro (⟨-, h⟩ | h)
      · exact nI σ _ (hσ _ (by omega)) h
      · exact nI σ _ (hσ _ (by omega)) h
    rw [hσk, one_mul]
    have e : glueS c σ τ k = τ k := by unfold glueS; rw [if_neg hk]
    simp only [e]
    exact congrArg (fun s => Species.diagFactor 2 s) (twoSpecies_congr hb rfl rfl rfl)

/-- The **mixed cross exponent** $\sum_{k<k'<N}(k'-k)\,a_k\,b_{k'}$. -/
def mixExp (a b : ℕ → ℕ) (N : ℕ) : ℕ := ∑ k' ∈ range N, ∑ k ∈ range k', (k' - k) * a k * b k'

theorem crossExp_add (a b : ℕ → ℕ) (N : ℕ) (hab : ∀ k k', k < k' → b k * a k' = 0) :
    crossExp (fun k => a k + b k) N = crossExp a N + crossExp b N + mixExp a b N := by
  unfold crossExp mixExp
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have h0 := hab k k' (Finset.mem_range.1 hk)
  have : (k' - k) * (a k + b k) * (a k' + b k') =
      (k' - k) * a k * a k' + (k' - k) * b k * b k' + (k' - k) * a k * b k' + (k' - k) * (b k * a k') := by ring
  rw [this, h0, mul_zero, add_zero]

theorem crossExp_glue (hσ : ∀ k, c ≤ k → σ k = TwoFactor.trivial)
    (hτ : ∀ k, k ≤ c + 1 → τ k = TwoFactor.trivial) :
    crossExp (fun k => (glueS c σ τ k).dim) N =
      crossExp (fun k => (σ k).dim) N + crossExp (fun k => (τ k).dim) N +
        mixExp (fun k => (σ k).dim) (fun k => (τ k).dim) N := by
  have e : (fun k => (glueS c σ τ k).dim) = fun k => (σ k).dim + (τ k).dim := by
    funext k
    unfold glueS
    by_cases hk : k ≤ c
    · rw [if_pos hk, hτ k (by omega)]; rfl
    · rw [if_neg hk, hσ k (by omega)]; simp [TwoFactor.trivial]
  rw [e]
  refine crossExp_add _ _ N fun k k' hkk' => ?_
  by_cases hk : k ≤ c + 1
  · rw [hτ k hk]; simp [TwoFactor.trivial]
  · rw [hσ k' (by omega)]; simp [TwoFactor.trivial]

theorem nII_glue (hσ : ∀ k, c ≤ k → σ k = TwoFactor.trivial)
    (hτ : ∀ k, k ≤ c + 1 → τ k = TwoFactor.trivial) :
    nII (glueS c σ τ) N = nII σ N + nII τ N := by
  unfold nII
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold glueS
  by_cases hk : k ≤ c
  · rw [if_pos hk, hτ k (by omega)]; simp [TwoFactor.trivial]
  · rw [if_neg hk, hσ k (by omega)]; simp [TwoFactor.trivial]

theorem nII'_glue (hσ : ∀ k, c ≤ k → σ k = TwoFactor.trivial)
    (hτ : ∀ k, k ≤ c + 1 → τ k = TwoFactor.trivial) :
    nII' (glueS c σ τ) N = nII' σ N + nII' τ N := by
  unfold nII'
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold glueS
  have tI : TwoFactor.trivial.type = ScaledType.II := rfl
  by_cases hk : k < c
  · rw [if_pos hk.le, if_pos (show k + 1 ≤ c by omega), hτ k (by omega), tI]; simp
  · by_cases hkc : k = c
    · subst hkc
      rw [if_pos le_rfl, hσ k le_rfl, hτ k (by omega), tI]; simp
    · rw [if_neg (show ¬ k ≤ c by omega), if_neg (show ¬ k + 1 ≤ c by omega), hσ k (by omega), tI]; simp

/-- **The 2-mass across a gap** (Conway–Sloane 1988, (3)): if $\sigma$ is trivial at the scales $2^k$, $k \ge c$, and
$\tau$ at the scales $k \le c+1$, then
$m_2(\sigma\,|_c\,\tau) = m_2(\sigma)\,m_2(\tau)\,\sqrt2^{\,\sum_{k<k'<N}(k'-k)\,n_k(\sigma)\,n_{k'}(\tau)}$. -/
theorem pMassTwo_glue (hσ : ∀ k, c ≤ k → σ k = TwoFactor.trivial)
    (hτ : ∀ k, k ≤ c + 1 → τ k = TwoFactor.trivial) :
    pMassTwo (glueS c σ τ) N = pMassTwo σ N * pMassTwo τ N *
      Real.sqrt 2 ^ mixExp (fun k => (σ k).dim) (fun k => (τ k).dim) N := by
  unfold pMassTwo
  rw [diagProdTwo_glue hσ hτ, crossExp_glue hσ hτ, nII_glue hσ hτ, nII'_glue hσ hτ]
  push_cast
  rw [pow_add, pow_add, show ((nII' σ N : ℤ) + nII' τ N) - (nII σ N + nII τ N) =
    ((nII' σ N : ℤ) - nII σ N) + ((nII' τ N : ℤ) - nII τ N) by ring,
    zpow_add₀ (two_ne_zero)]
  ring

end Glue

/-! ### The 2-mass of a shifted symbol -/

theorem isBound_shS (σ : TwoSymbol) (k : ℕ) : IsBound (shS σ) (k + 1) ↔ IsBound σ k := by
  unfold IsBound
  constructor
  · rintro (⟨-, h⟩ | h)
    · cases k with
      | zero => exact absurd h not_isTypeI_trivial
      | succ k => exact Or.inl ⟨by omega, h⟩
    · exact Or.inr h
  · rintro (⟨hk, h⟩ | h)
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact Or.inl ⟨by omega, h⟩
    · exact Or.inr h

theorem diagProdTwo_shS (σ : TwoSymbol) (N : ℕ) : diagProdTwo (shS σ) (N + 1) = diagProdTwo σ N := by
  unfold diagProdTwo
  rw [Finset.prod_range_succ']
  have h0 : halfFactor (shS σ) = 1 := rfl
  have h1 : (twoSpecies (shS σ 0) (IsBound (shS σ) 0)).diagFactor 2 = halfFactor σ := by
    unfold halfFactor
    by_cases hI : (σ 0).type = ScaledType.I
    · have hb : IsBound (shS σ) 0 := Or.inr hI
      rw [shS_zero, twoSpecies_trivial_bound hb, if_pos hI]; exact table2_two.2.1
    · have hb : ¬ IsBound (shS σ) 0 := by
        rintro (⟨h, -⟩ | h)
        · exact h rfl
        · exact hI h
      rw [shS_zero, twoSpecies_trivial_free hb, if_neg hI]; rfl
  rw [h0, h1, one_mul, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [shS_succ]
  exact congrArg (fun s => Species.diagFactor 2 s) (twoSpecies_congr (isBound_shS σ k) rfl rfl rfl)

theorem crossExp_shS (σ : TwoSymbol) (N : ℕ) :
    crossExp (fun k => (shS σ k).dim) (N + 1) = crossExp (fun k => (σ k).dim) N := by
  unfold crossExp
  rw [Finset.sum_range_succ']
  simp only [Finset.range_zero, Finset.sum_empty, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_range_succ']
  simp only [shS_succ, shS_zero, TwoFactor.trivial, mul_zero, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  omega

theorem nII_shS (σ : TwoSymbol) (N : ℕ) : nII (shS σ) (N + 1) = nII σ N := by
  unfold nII
  rw [Finset.sum_range_succ']
  rfl

theorem nII'_shS (σ : TwoSymbol) (N : ℕ) : nII' (shS σ) (N + 1) = nII' σ N := by
  unfold nII'
  rw [Finset.sum_range_succ']
  rfl

/-- **The 2-mass is invariant under the shift** (the cross-product only sees differences of scales). -/
theorem pMassTwo_shS (σ : TwoSymbol) (N : ℕ) : pMassTwo (shS σ) (N + 1) = pMassTwo σ N := by
  unfold pMassTwo
  rw [diagProdTwo_shS, crossExp_shS, nII_shS, nII'_shS]

end QuadFormsKB.Hanke2011Structure.RatTwo
