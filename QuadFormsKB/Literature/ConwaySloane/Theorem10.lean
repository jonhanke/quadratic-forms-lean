/-
# Conway–Sloane, Ch. 15, Theorem 10: the printed 2-adic equivalence condition, on symbols

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §7.5, Thm. 10, p. 381
(`conwaysloane1999`).

Theorem 10 says that forms $f$, $f'$ with invariants $n_q, S_q, \varepsilon_q, t_q$ and $n'_q, S'_q, \varepsilon'_q, t'_q$
are 2-adically equivalent iff (i) $n_q = n'_q$, $S_q = S'_q$ for all $q$, and (ii) for each integer $m$ *including
negative integers* for which $f_{2^m}$ has type II,
$$\sum_{q < 2^m}(t_q - t'_q) \equiv 4\bigl(\min(a, m) + \min(b, m) + \cdots\bigr) \pmod 8,$$
where $2^a, 2^b, \dots$ are the $q$ with $\varepsilon_q \ne \varepsilon'_q$. This file states (i)–(ii) on symbol data
(`Theorem10Cond`) and proves that they are exactly the invariants of sign walking and oddity fusion
(`theorem10Cond_iff_sameInvariants`), hence equivalent to `MoveEquiv` and to equal canonical symbols. The statement
for forms (that (i)–(ii) characterize $\mathbb Z_2$-equivalence) is proved in the classification file.

*Reading.* The forms $f_{2^m}$ with $m < 0$ are zero-dimensional, of type II, so (ii) is required for every negative
$m$; for $m = -1$ it says that the number of $q$ with $\varepsilon_q \ne \varepsilon'_q$ is even (the left side is an
empty sum and the right side is $-4$ times that number). Without the negative $m$ the condition would not see the
determinant (two symbols differing only in one sign of a long compartment satisfy (ii) for all $m \ge 0$).
Oddities of type II forms are $0$ (Conway–Sloane, §7.3); here only their equality is assumed.

**Defines** `prefixInvariant` ($G(m) = \sum_{k<m}t_k + 4\sum_{1 \le y \le m}(\text{minus signs below } 2^y)$),
`Theorem10Cond`.

**Proves**
* `compartmentInvariant_eq_prefix`: the compartment invariants are differences of prefix invariants;
* `sameInvariants_iff_prefix`: the invariants of the moves are equivalent to equal sign parity overall and equal
  prefix invariants at every type II scale;
* `theorem10Cond_iff_sameInvariants`: Theorem 10's (i)–(ii) are equivalent to the invariants of the moves;
* `theorem10Cond_iff_moveEquiv`: (i)–(ii) hold iff the symbols are related by sign walking and oddity fusion.
-/
import QuadFormsKB.Literature.ConwaySloane.Canonical

namespace QuadFormsKB.ConwaySloane

open Finset

theorem four_mul_add_self (x : ZMod 8) : 4 * x + 4 * x = 0 := by
  have h : (8 : ZMod 8) = 0 := by decide
  linear_combination x * h

theorem neg_four_mul (x : ZMod 8) : -(4 * x) = 4 * x := by
  linear_combination -(four_mul_add_self x)

/-- The **prefix invariant** $G(m) = \sum_{k < m} t_k + 4\sum_{y=1}^{m}(\text{number of minus signs below } 2^y)$
(mod 8) of a 2-adic symbol. -/
def prefixInvariant (σ : TwoSymbol) : ℕ → ZMod 8
  | 0 => 0
  | m + 1 => prefixInvariant σ m + (σ m).oddity + 4 * (minusBelow σ (m + 1) : ZMod 8)

/-- A compartment invariant is a difference of prefix invariants. -/
theorem compartmentInvariant_eq_prefix (σ : TwoSymbol) (c₁ : ℕ) : ∀ c₂, c₁ ≤ c₂ + 1 →
    compartmentInvariant σ c₁ c₂ =
      prefixInvariant σ (c₂ + 1) - prefixInvariant σ c₁ + 4 * (minusBelow σ c₁ : ZMod 8)
  | 0, h => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with rfl | rfl
    · simp [compartmentInvariant, prefixInvariant, Finset.sum_Icc_succ_top]; ring
    · simp [compartmentInvariant, prefixInvariant]
  | c₂ + 1, h => by
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · -- c₁ = c₂ + 2: empty compartment
      subst h'
      simp [compartmentInvariant, prefixInvariant]
    · have ih := compartmentInvariant_eq_prefix σ c₁ c₂ (by omega)
      unfold compartmentInvariant at ih ⊢
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (show c₁ ≤ c₂ + 1 + 1 by omega)]
      rw [show (∑ k ∈ Icc c₁ c₂, (σ k).oddity) = (∑ k ∈ Icc c₁ c₂, (σ k).oddity +
          4 * ∑ y ∈ Icc c₁ (c₂ + 1), (minusBelow σ y : ZMod 8)) -
          4 * ∑ y ∈ Icc c₁ (c₂ + 1), (minusBelow σ y : ZMod 8) by ring, ih]
      simp only [prefixInvariant]
      ring

theorem prefixInvariant_succ (σ : TwoSymbol) (m : ℕ) :
    prefixInvariant σ (m + 1) = prefixInvariant σ m + (σ m).oddity + 4 * (minusBelow σ (m + 1) : ZMod 8) := rfl

/-- The hypotheses under which Theorem 10 is read: the same dimensions and types, the same (zero) oddities of type II
forms, and agreement from the scale $2^N$ on, where all forms are of type II. -/
structure Theorem10Setting (σ τ : TwoSymbol) (N : ℕ) : Prop where
  dim_eq : ∀ k, (τ k).dim = (σ k).dim
  type_eq : ∀ k, (τ k).type = (σ k).type
  oddity_typeII : ∀ k, ¬ IsTypeI σ k → (τ k).oddity = (σ k).oddity
  eq_of_le : ∀ k, N ≤ k → τ k = σ k
  typeII_of_le : ∀ k, N ≤ k → ¬ IsTypeI σ k

section Prefix

variable {σ τ : TwoSymbol} {N : ℕ} (hT : Theorem10Setting σ τ N)
include hT

theorem Theorem10Setting.isTypeI_iff (k : ℕ) : IsTypeI τ k ↔ IsTypeI σ k := by
  unfold IsTypeI; rw [hT.type_eq]

/-- Under equal types, the invariants of the moves are: equal parity of all minus signs, and equal prefix invariants
at every type II scale. -/
theorem sameInvariants_iff_prefix :
    SameInvariants σ τ ↔ (4 * (minusBelow τ N : ZMod 8)) = 4 * (minusBelow σ N : ZMod 8) ∧
      ∀ m, ¬ IsTypeI σ m → prefixInvariant τ m = prefixInvariant σ m := by
  constructor
  · intro hS
    refine ⟨?_, fun m => ?_⟩
    · have hb := hS.boundary N ⟨hT.typeII_of_le N le_rfl, hT.typeII_of_le (N + 1) (by omega)⟩
      simp only [minusBelow, Nat.cast_add, mul_add, hT.eq_of_le N le_rfl] at hb
      exact add_right_cancel hb
    · induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro hm
        classical
        have hP : ∃ c, c ≤ m ∧ ∀ x, c ≤ x → x < m → IsTypeI σ x := ⟨m, le_rfl, fun x h1 h2 => absurd h2 (by omega)⟩
        set c := Nat.find hP with hc_def
        have hc : c ≤ m ∧ ∀ x, c ≤ x → x < m → IsTypeI σ x := Nat.find_spec hP
        by_cases hc0 : c = 0
        · -- [0, m-1] is all of type I
          rcases Nat.eq_zero_or_pos m with rfl | hmpos
          · rfl
          · have hC : IsCompartment σ 0 (m - 1) := ⟨Nat.zero_le _, fun x _ h => hc.2 x (by omega) (by omega),
              Or.inl rfl, by rwa [Nat.sub_add_cancel hmpos]⟩
            have e1 := compartmentInvariant_eq_prefix σ 0 (m - 1) (by omega)
            have e2 := compartmentInvariant_eq_prefix τ 0 (m - 1) (by omega)
            rw [hS.compartment 0 (m - 1) hC, e1, Nat.sub_add_cancel hmpos] at e2
            simpa [prefixInvariant, minusBelow] using e2.symm
        · have hprev : ¬ IsTypeI σ (c - 1) := by
            intro h
            have := Nat.find_min hP (show c - 1 < c by omega)
            exact this ⟨by omega, fun x h1 h2 => by
              rcases Nat.eq_or_lt_of_le h1 with h' | h'
              · rwa [← h']
              · exact hc.2 x (by omega) h2⟩
          have ihc := ih (c - 1) (by omega) hprev
          have hsucc : prefixInvariant τ c = prefixInvariant σ c - 4 * (minusBelow σ c : ZMod 8) +
              4 * (minusBelow τ c : ZMod 8) := by
            have e := prefixInvariant_succ τ (c - 1)
            have e' := prefixInvariant_succ σ (c - 1)
            rw [Nat.sub_add_cancel (by omega)] at e e'
            rw [e, e', ihc, hS.oddity_typeII _ hprev]
            ring
          by_cases hcm : c = m
          · rw [← hcm, hsucc]
            have hm' : ¬ IsTypeI σ c := by rw [hcm]; exact hm
            have hb := hS.boundary (c - 1) ⟨hprev, by rwa [Nat.sub_add_cancel (by omega)]⟩
            rw [Nat.sub_add_cancel (by omega)] at hb
            rw [hb]; ring
          · have hC : IsCompartment σ c (m - 1) := ⟨by omega, fun x h1 h2 => hc.2 x h1 (by omega),
              Or.inr hprev, by rwa [Nat.sub_add_cancel (by omega)]⟩
            have e1 := compartmentInvariant_eq_prefix σ c (m - 1) (by omega)
            have e2 := compartmentInvariant_eq_prefix τ c (m - 1) (by omega)
            rw [hS.compartment c (m - 1) hC, e1, Nat.sub_add_cancel (by omega : 1 ≤ m), hsucc] at e2
            linear_combination -e2
  · rintro ⟨-, hG⟩
    refine ⟨hT.dim_eq, hT.type_eq, hT.oddity_typeII, fun y hy => ?_, fun c₁ c₂ hC => ?_⟩
    · have e := prefixInvariant_succ τ y
      rw [hG _ hy.2, hG _ hy.1, prefixInvariant_succ σ y, hT.oddity_typeII _ hy.1] at e
      linear_combination -e
    · rw [compartmentInvariant_eq_prefix σ c₁ c₂ (by have := hC.1; omega),
        compartmentInvariant_eq_prefix τ c₁ c₂ (by have := hC.1; omega), hG _ hC.2.2.2]
      rcases hC.2.2.1 with h0 | hprev
      · subst h0; simp [prefixInvariant, minusBelow]
      · have hpos : 0 < c₁ := by
          rcases Nat.eq_zero_or_pos c₁ with h | h
          · exfalso; exact hprev (by rw [h]; exact hC.2.1 0 (by omega) (by rw [← h]; exact hC.1))
          · exact h
        have e := prefixInvariant_succ τ (c₁ - 1)
        have e' := prefixInvariant_succ σ (c₁ - 1)
        rw [Nat.sub_add_cancel hpos] at e e'
        rw [e, e', hG _ hprev, hT.oddity_typeII _ hprev]
        ring

end Prefix

/-! ### The printed condition -/

/-- **Conditions (i) and (ii) of Theorem 10** (Conway–Sloane, §7.5, Thm. 10, p. 381) for the 2-adic symbols $\sigma$
(of $f$) and $\tau$ (of $f'$), which agree from the scale $2^N$ on: (i) $n_q = n'_q$ and $S_q = S'_q$ for all $q$;
(ii) for every integer $m$ (including negative integers) such that $f_{2^m}$ has type II,
$\sum_{q < 2^m}(t_q - t'_q) \equiv 4\sum_{\varepsilon_{2^a} \ne \varepsilon'_{2^a}}\min(a, m) \pmod 8$. For $m < 0$
the form $f_{2^m}$ is zero-dimensional, hence of type II. -/
@[kb "conwaysloane1999" "Ch. 15, §7.5, Thm. 10, p. 381"]
def Theorem10Cond (σ τ : TwoSymbol) (N : ℕ) : Prop :=
  (∀ k, (σ k).dim = (τ k).dim ∧ (σ k).type = (τ k).type) ∧
  ∀ m : ℤ, (m < 0 ∨ ¬ IsTypeI σ m.toNat) →
    ∑ k ∈ (range N).filter (fun k : ℕ => (k : ℤ) < m), ((σ k).oddity - (τ k).oddity) =
      4 * ∑ k ∈ (range N).filter (fun k => (σ k).sign ≠ (τ k).sign), (((min (k : ℤ) m : ℤ)) : ZMod 8)

/-- The number of scales $2^k$, $k < x$, at which the signs of $\sigma$ and $\tau$ differ. -/
def signDiffBelow (σ τ : TwoSymbol) : ℕ → ℕ
  | 0 => 0
  | x + 1 => signDiffBelow σ τ x + if (σ x).sign ≠ (τ x).sign then 1 else 0

theorem four_mul_signDiffBelow (σ τ : TwoSymbol) : ∀ x,
    (4 * (signDiffBelow σ τ x : ZMod 8)) = 4 * (minusBelow σ x : ZMod 8) + 4 * (minusBelow τ x : ZMod 8)
  | 0 => by simp [signDiffBelow, minusBelow]
  | x + 1 => by
    have ih := four_mul_signDiffBelow σ τ x
    simp only [signDiffBelow, minusBelow, Nat.cast_add, mul_add, ih]
    have h : (4 + 4 : ZMod 8) = 0 := by decide
    cases (σ x).sign <;> cases (τ x).sign <;> simp <;> (ring_nf; try reduce_mod_char)

section Cond

variable {σ τ : TwoSymbol} {N : ℕ} (hT : Theorem10Setting σ τ N)
include hT

theorem card_filter_signDiff_lt (x : ℕ) :
    (((range N).filter fun k => (σ k).sign ≠ (τ k).sign).filter fun k => k < x).card = signDiffBelow σ τ x := by
  induction x with
  | zero => simp [signDiffBelow]
  | succ x ih =>
    rw [signDiffBelow, ← ih]
    have e : (((range N).filter fun k => (σ k).sign ≠ (τ k).sign).filter fun k => k < x + 1) =
        (((range N).filter fun k => (σ k).sign ≠ (τ k).sign).filter fun k => k < x) ∪
          (((range N).filter fun k => (σ k).sign ≠ (τ k).sign).filter fun k => k = x) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h | h
        · exact Or.inl ⟨h1, h⟩
        · exact Or.inr ⟨h1, h⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, by omega⟩
        · exact ⟨h1, by omega⟩
    rw [e, Finset.card_union_of_disjoint (by
      rw [Finset.disjoint_filter]; intro k _ h1 h2; omega)]
    congr 1
    by_cases hx : (σ x).sign ≠ (τ x).sign
    · rw [if_pos hx]
      have hxN : x < N := by
        by_contra h
        exact hx (by rw [hT.eq_of_le x (by omega)])
      rw [Finset.card_eq_one]
      refine ⟨x, ?_⟩
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨_, rfl⟩; rfl
      · rintro rfl; exact ⟨⟨hxN, hx⟩, rfl⟩
    · rw [if_neg hx, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k hk h; subst h; exact hx (Finset.mem_filter.mp hk).2

theorem card_signDiff : ((range N).filter fun k => (σ k).sign ≠ (τ k).sign).card = signDiffBelow σ τ N := by
  rw [← card_filter_signDiff_lt hT N]
  congr 1
  ext k; simp only [Finset.mem_filter, Finset.mem_range]; tauto

/-- The two sides of (ii) at a natural number $m$, compared with the prefix invariants:
$\text{LHS} - \text{RHS} = G_\sigma(m) - G_\tau(m) - 4m\cdot\#\{\varepsilon \ne \varepsilon'\}$. -/
theorem theorem10_sides_nat : ∀ m : ℕ,
    ∑ k ∈ (range N).filter (fun k : ℕ => (k : ℤ) < (m : ℤ)), ((σ k).oddity - (τ k).oddity) -
      4 * ∑ k ∈ (range N).filter (fun k => (σ k).sign ≠ (τ k).sign), (((min (k : ℤ) (m : ℤ) : ℤ)) : ZMod 8) =
    prefixInvariant σ m - prefixInvariant τ m - 4 * m * (signDiffBelow σ τ N : ZMod 8)
  | 0 => by
    have h1 : (range N).filter (fun k : ℕ => (k : ℤ) < ((0 : ℕ) : ℤ)) = ∅ := by
      ext k; simp
    rw [h1]
    simp [prefixInvariant]
  | m + 1 => by
    have ih := theorem10_sides_nat m
    set S := (range N).filter fun k => (σ k).sign ≠ (τ k).sign with hS
    have hL : ∑ k ∈ (range N).filter (fun k : ℕ => (k : ℤ) < ((m + 1 : ℕ) : ℤ)), ((σ k).oddity - (τ k).oddity) =
        ∑ k ∈ (range N).filter (fun k : ℕ => (k : ℤ) < (m : ℤ)), ((σ k).oddity - (τ k).oddity) +
          ((σ m).oddity - (τ m).oddity) := by
      by_cases hm : m < N
      · have e : (range N).filter (fun k : ℕ => (k : ℤ) < ((m + 1 : ℕ) : ℤ)) =
            insert m ((range N).filter (fun k : ℕ => (k : ℤ) < (m : ℤ))) := by
          ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]; push_cast; omega
        rw [e, Finset.sum_insert (by simp)]; ring
      · have e : (range N).filter (fun k : ℕ => (k : ℤ) < ((m + 1 : ℕ) : ℤ)) =
            (range N).filter (fun k : ℕ => (k : ℤ) < (m : ℤ)) := by
          ext k; simp only [Finset.mem_filter, Finset.mem_range]; push_cast; omega
        rw [e, hT.eq_of_le m (by omega)]; ring
    have hmin : ∀ k ∈ S, (((min (k : ℤ) ((m + 1 : ℕ) : ℤ) : ℤ)) : ZMod 8) =
        (((min (k : ℤ) (m : ℤ) : ℤ)) : ZMod 8) + if m < k then 1 else 0 := by
      intro k _
      split_ifs with h
      · have e1 : min (k : ℤ) ((m + 1 : ℕ) : ℤ) = ((m + 1 : ℕ) : ℤ) := min_eq_right (by push_cast; omega)
        have e2 : min (k : ℤ) (m : ℤ) = m := min_eq_right (by omega)
        rw [e1, e2]; push_cast; ring
      · have e1 : min (k : ℤ) ((m + 1 : ℕ) : ℤ) = k := min_eq_left (by push_cast; omega)
        have e2 : min (k : ℤ) (m : ℤ) = k := min_eq_left (by omega)
        rw [e1, e2, add_zero]
    have hR : 4 * ∑ k ∈ S, (((min (k : ℤ) ((m + 1 : ℕ) : ℤ) : ℤ)) : ZMod 8) =
        4 * ∑ k ∈ S, (((min (k : ℤ) (m : ℤ) : ℤ)) : ZMod 8) +
          (4 * (signDiffBelow σ τ N : ZMod 8) + 4 * (signDiffBelow σ τ (m + 1) : ZMod 8)) := by
      rw [Finset.sum_congr rfl hmin, Finset.sum_add_distrib, mul_add]
      congr 1
      rw [Finset.sum_boole]
      have hsplit : (S.filter fun k => m < k).card + (S.filter fun k => k < m + 1).card = S.card := by
        rw [← Finset.card_union_of_disjoint (by rw [Finset.disjoint_filter]; intro k _ h1 h2; omega)]
        congr 1
        ext k
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> exact h1
        · intro h1
          rcases lt_or_ge m k with h | h
          · exact Or.inl ⟨h1, h⟩
          · exact Or.inr ⟨h1, by omega⟩
      rw [card_filter_signDiff_lt hT, card_signDiff hT] at hsplit
      rw [← hsplit]; push_cast
      ring_nf; reduce_mod_char
    have hP := prefixInvariant_succ σ m
    have hQ := prefixInvariant_succ τ m
    have hD := four_mul_signDiffBelow σ τ (m + 1)
    rw [hL, hR, hP, hQ]
    push_cast
    linear_combination (norm := (ring_nf; try reduce_mod_char)) ih - hD

/-- Conditions (i)–(ii) of Theorem 10 are: an even number of sign differences, and equal prefix invariants at the
type II scales. -/
theorem theorem10Cond_iff_prefix :
    Theorem10Cond σ τ N ↔ (4 * (signDiffBelow σ τ N : ZMod 8)) = 0 ∧
      ∀ m, ¬ IsTypeI σ m → prefixInvariant τ m = prefixInvariant σ m := by
  constructor
  · rintro ⟨-, h⟩
    have h1 := h (-1) (Or.inl (by norm_num))
    have hl : (range N).filter (fun k : ℕ => (k : ℤ) < -1) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun k _ => by omega
    have hr : ∀ k ∈ (range N).filter (fun k => (σ k).sign ≠ (τ k).sign),
        (((min (k : ℤ) (-1) : ℤ)) : ZMod 8) = -1 := by
      intro k _; rw [min_eq_right (by omega)]; push_cast; ring
    rw [hl, Finset.sum_empty, Finset.sum_congr rfl hr, Finset.sum_const, card_signDiff hT] at h1
    have h4 : (4 * (signDiffBelow σ τ N : ZMod 8)) = 0 := by
      have := neg_four_mul (signDiffBelow σ τ N : ZMod 8)
      simp only [nsmul_eq_mul] at h1
      linear_combination -h1 - this
    refine ⟨h4, fun m hm => ?_⟩
    have h2 := h (m : ℤ) (Or.inr (by simpa using hm))
    have e := theorem10_sides_nat hT m
    rw [h2, sub_self] at e
    have : (4 * (m : ZMod 8) * (signDiffBelow σ τ N : ZMod 8)) = 0 := by
      rw [mul_comm 4, mul_assoc, h4, mul_zero]
    rw [this, sub_zero] at e
    linear_combination e
  · rintro ⟨h4, hG⟩
    refine ⟨fun k => ⟨(hT.dim_eq k).symm, (hT.type_eq k).symm⟩, fun m hm => ?_⟩
    rcases lt_or_ge m 0 with hneg | hnn
    · have hl : (range N).filter (fun k : ℕ => (k : ℤ) < m) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun k _ => by omega
      have hr : ∀ k ∈ (range N).filter (fun k => (σ k).sign ≠ (τ k).sign),
          (((min (k : ℤ) m : ℤ)) : ZMod 8) = (m : ZMod 8) := by
        intro k _; rw [min_eq_right (by omega)]
      rw [hl, Finset.sum_empty, Finset.sum_congr rfl hr, Finset.sum_const, card_signDiff hT, nsmul_eq_mul,
        mul_comm (signDiffBelow σ τ N : ZMod 8), ← mul_assoc, mul_comm 4, mul_assoc, h4, mul_zero]
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n := ⟨m.toNat, (Int.toNat_of_nonneg hnn).symm⟩
      have hm' : ¬ IsTypeI σ n := by
        rcases hm with h | h
        · omega
        · simpa using h
      have e := theorem10_sides_nat hT n
      rw [hG n hm'] at e
      have h0 : (4 * (n : ZMod 8) * (signDiffBelow σ τ N : ZMod 8)) = 0 := by
        rw [mul_comm 4, mul_assoc, h4, mul_zero]
      exact sub_eq_zero.mp (by rw [e, h0]; ring)

/-- **Theorem 10's conditions are the invariants of the moves** (Conway–Sloane, §7.5, Thm. 10 and the rules (i), (ii)
that follow it, p. 381): conditions (i)–(ii) hold iff the symbols have the same invariants under sign walking and
oddity fusion. -/
@[kb "conwaysloane1999" "Ch. 15, §7.5, Thm. 10, p. 381"]
theorem theorem10Cond_iff_sameInvariants : Theorem10Cond σ τ N ↔ SameInvariants σ τ := by
  rw [theorem10Cond_iff_prefix hT, sameInvariants_iff_prefix hT]
  have hD := four_mul_signDiffBelow σ τ N
  constructor
  · rintro ⟨h4, hG⟩
    refine ⟨?_, hG⟩
    linear_combination -h4 + hD + four_mul_add_self (minusBelow τ N : ZMod 8)
  · rintro ⟨h4, hG⟩
    refine ⟨?_, hG⟩
    linear_combination (norm := (ring_nf; try reduce_mod_char)) hD + h4

/-- **Theorem 10, on symbols** (Conway–Sloane, §7.5, p. 381): conditions (i)–(ii) hold iff the symbols are related by
sign walking and oddity fusion, iff their canonical symbols agree. -/
@[kb "conwaysloane1999" "Ch. 15, §7.5, Thm. 10, p. 381; §7.6, p. 382"]
theorem theorem10Cond_iff_moveEquiv : Theorem10Cond σ τ N ↔ MoveEquiv σ τ := by
  rw [theorem10Cond_iff_sameInvariants hT, moveEquiv_iff_sameInvariants hT.typeII_of_le]

end Cond

end QuadFormsKB.ConwaySloane
