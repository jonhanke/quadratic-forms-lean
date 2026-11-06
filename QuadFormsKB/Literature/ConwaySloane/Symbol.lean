/-
# Conway–Sloane, Ch. 15, §7.1–7.6: $p$-adic symbols, compartments, trains, sign walking and oddity fusion

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, pp. 378–382
(bibliography key `conwaysloane1999`). This file defines the symbols as combinatorial data; the symbol of a form
(from a Jordan decomposition) and the classification theorems are in later files.

**Conventions.** Scales are $q = p^k$ with $k \in \mathbb N$ (Conway–Sloane's forms are integral, so $q \ge 1$); a
symbol is a function $k \mapsto$ (the constituent of scale $p^k$), defined for *every* $k$, including the
constituents of dimension $0$ (Conway–Sloane: "all the forms $qf_q$, even those of zero dimension", p. 381). Signs
$\varepsilon_q = \pm1$ are the type `Sign` (`plus`, `minus`); oddities are in $\mathbb Z/8$.

**Defines**
* `Sign`, `ScaledType` (types I and II, §7.3), `OddFactor`, `OddSymbol` (the $p$-adic symbol for odd $p$, the formal
  product of factors $q^{\varepsilon_qn_q}$, §7.2), `TwoFactor`, `TwoSymbol` (the 2-adic symbol, factors
  $q_{t_q}^{\varepsilon_qn_q}$ (type I) or $q^{\varepsilon_qn_q}$ (type II), §7.4), `RealSymbol` ($+^r-^s$);
* compartments and trains (`IsCompartment`, `IsTrain`, §7.5, p. 381);
* the elementary moves (`Step`): a *walk step* between adjacent scales $2^j$, $2^{j+1}$ of which at least one is of type
  I (both signs change, the oddity of a type I one of them changes by $4$) and an *oddity fusion step* between
  adjacent type I scales (an amount $c$ of oddity is moved from one to the other); `MoveEquiv` is the equivalence
  relation they generate (§7.5 (i), (ii), pp. 381–382);
* the invariants of the moves: the parities `minusBelow` at train boundaries and the compartment totals
  `compartmentInvariant` (oddity total plus $4\times$ a sign count).

**Proves**
* `Step.symm'`: every step is undone by a step;
* `Step.dim_eq`, `Step.type_eq`, `Step.minusBelow_boundary`, `Step.compartmentInvariant_eq`: the moves preserve the
  dimensions, the types, the sign parities at train boundaries and the compartment invariants;
  `MoveEquiv.invariants_eq` for the generated equivalence.

**Reading of the moves.** Conway–Sloane's sign walk between $q_1 < q_2$ in one train consists of steps between adjacent
forms, each involving one compartment; the total oddity of a compartment changes by $4$ for each step that involves
it (p. 382). A walk step here changes the oddity of one type I member of the pair by $4$; composing steps gives
exactly Conway–Sloane's walk (the oddities of the individual members are then redistributed by oddity fusion). As in
the book, intermediate symbols may contain impossible constituents (p. 382: "Transformations involving such impossible
constituents are quite legal provided the end results are meaningful").
-/
import Mathlib
import QuadFormsKB.Citation

namespace QuadFormsKB.ConwaySloane

open Finset

/-! ### Signs and types -/

/-- A sign $\varepsilon = \pm1$ (Conway–Sloane write $+$ and $-$). -/
inductive Sign
  /-- $\varepsilon = +1$. -/
  | plus
  /-- $\varepsilon = -1$. -/
  | minus
  deriving DecidableEq, Repr

namespace Sign

/-- The sign as an integer $\pm1$. -/
def toInt : Sign → ℤ
  | plus => 1
  | minus => -1

/-- Change of sign. -/
def flip : Sign → Sign
  | plus => minus
  | minus => plus

@[simp] theorem flip_flip (s : Sign) : s.flip.flip = s := by cases s <;> rfl

/-- The sign of an integer $\pm1$ (anything other than $-1$ is read as $+$). -/
def ofInt (z : ℤ) : Sign := if z = -1 then minus else plus

/-- The product of two signs. -/
def mul : Sign → Sign → Sign
  | plus, s => s
  | minus, s => s.flip

theorem toInt_mul (s t : Sign) : (s.mul t).toInt = s.toInt * t.toInt := by
  cases s <;> cases t <;> rfl

end Sign

/-- The **scaled type** of a Jordan constituent $qf_q$ at $p = 2$ (Conway–Sloane, §7.3, p. 380): type I if $qf_q$
represents an odd multiple of $q$ (an odd diagonal entry of $f_q$), type II otherwise. -/
@[kb "conwaysloane1999" "Ch. 15, §7.3, p. 380"]
inductive ScaledType
  /-- Type I: $f_q$ has an odd diagonal entry. -/
  | I
  /-- Type II: every diagonal entry of $f_q$ is even. -/
  | II
  deriving DecidableEq, Repr

/-! ### The symbols -/

/-- A factor $q^{\varepsilon_qn_q}$ of a $p$-adic symbol for odd $p$ (Conway–Sloane, §7.2, p. 379): the dimension
$n_q = \dim f_q$ and the sign $\varepsilon_q = \left(\frac{\det f_q}{p}\right)$ of the Jordan constituent $qf_q$. -/
@[kb "conwaysloane1999" "Ch. 15, §7.1–7.2, p. 379"]
structure OddFactor where
  /-- The dimension $n_q$. -/
  dim : ℕ
  /-- The sign $\varepsilon_q$. -/
  sign : Sign
  deriving DecidableEq, Repr

/-- The factor of a zero-dimensional constituent, $q^{+0}$. -/
def OddFactor.trivial : OddFactor := ⟨0, .plus⟩

/-- The **$p$-adic symbol** for odd $p$ (Conway–Sloane, §7.2, p. 379): the formal product of the factors
$q^{\varepsilon_qn_q}$, $q = p^k$; here the function $k \mapsto$ the factor of scale $p^k$ (all $k \ge 0$; the factors
of dimension $0$ are the omitted ones). Example (23), $1^{-2}3^{+5}9^{+1}27^{-3}$, is `example23`. -/
@[kb "conwaysloane1999" "Ch. 15, §7.2, p. 379"]
abbrev OddSymbol := ℕ → OddFactor

/-- A factor $q_{t_q}^{\varepsilon_qn_q}$ (type I) or $q^{\varepsilon_qn_q}$ (type II) of a 2-adic symbol
(Conway–Sloane, §7.3–7.4, p. 380): dimension $n_q$, sign $\varepsilon_q = \left(\frac{\det f_q}{2}\right)$, scaled
type $S_q$ and oddity $t_q \in \mathbb Z/8$ of the Jordan constituent $qf_q$ ($t_q = 0$ for type II). -/
@[kb "conwaysloane1999" "Ch. 15, §7.3–7.4, p. 380"]
structure TwoFactor where
  /-- The dimension $n_q$. -/
  dim : ℕ
  /-- The sign $\varepsilon_q$. -/
  sign : Sign
  /-- The scaled type $S_q$. -/
  type : ScaledType
  /-- The oddity $t_q$ (mod 8). -/
  oddity : ZMod 8
  deriving DecidableEq

/-- The factor of a zero-dimensional constituent, $q^{+0}$ (type II, oddity $0$). -/
def TwoFactor.trivial : TwoFactor := ⟨0, .plus, .II, 0⟩

/-- The **2-adic symbol** (Conway–Sloane, §7.4, p. 380): the function $k \mapsto$ the factor of scale $2^k$, for every
$k \ge 0$ (zero-dimensional constituents included). -/
@[kb "conwaysloane1999" "Ch. 15, §7.4, p. 380"]
abbrev TwoSymbol := ℕ → TwoFactor

/-- The **$(-1)$-adic symbol** $+^r-^s$ (Conway–Sloane, §7.2, p. 379): the numbers $r = n_+$ and $s = n_-$ of positive
and negative terms (Sylvester's law of inertia). -/
@[kb "conwaysloane1999" "Ch. 15, §7.1–7.2, p. 379"]
structure RealSymbol where
  /-- $r = n_+$. -/
  pos : ℕ
  /-- $s = n_-$. -/
  neg : ℕ
  deriving DecidableEq, Repr

/-- Example (23) of Conway–Sloane (p. 379): the 3-adic symbol $1^{-2}3^{+5}9^{+1}27^{-3}$. -/
@[kb "conwaysloane1999" "Ch. 15, §7.2, (23), p. 379"]
def example23 : OddSymbol
  | 0 => ⟨2, .minus⟩
  | 1 => ⟨5, .plus⟩
  | 2 => ⟨1, .plus⟩
  | 3 => ⟨3, .minus⟩
  | _ => OddFactor.trivial

/-- The example of §7.4 (p. 380): the 2-adic symbol $1^{-2}2_5^{+3}4_3^{-1}8^{+4}$, i.e.
$1_{\mathrm{II}}^{-2}2_5^{+3}4_3^{-1}8_{\mathrm{II}}^{+4}$. -/
@[kb "conwaysloane1999" "Ch. 15, §7.4, p. 380"]
def example74 : TwoSymbol
  | 0 => ⟨2, .minus, .II, 0⟩
  | 1 => ⟨3, .plus, .I, 5⟩
  | 2 => ⟨1, .minus, .I, 3⟩
  | 3 => ⟨4, .plus, .II, 0⟩
  | _ => TwoFactor.trivial

/-! ### Compartments and trains -/

section Intervals

variable (σ : TwoSymbol)

/-- The constituent of scale $2^k$ has type I. -/
def IsTypeI (k : ℕ) : Prop := (σ k).type = .I

instance (k : ℕ) : Decidable (IsTypeI σ k) := inferInstanceAs (Decidable (_ = _))

/-- A **compartment** (Conway–Sloane, §7.5, p. 381): a maximal interval $[2^{c_1}, 2^{c_2}]$ of scales in which every
form is of type I. -/
@[kb "conwaysloane1999" "Ch. 15, §7.5, p. 381 (compartment)"]
def IsCompartment (c₁ c₂ : ℕ) : Prop :=
  c₁ ≤ c₂ ∧ (∀ x, c₁ ≤ x → x ≤ c₂ → IsTypeI σ x) ∧ (c₁ = 0 ∨ ¬ IsTypeI σ (c₁ - 1)) ∧ ¬ IsTypeI σ (c₂ + 1)

/-- A **train** (Conway–Sloane, §7.5, p. 381): a maximal interval $[2^{r_1}, 2^{r_2}]$ of scales such that of any two
adjacent forms at least one has type I. -/
@[kb "conwaysloane1999" "Ch. 15, §7.5, p. 381 (train)"]
def IsTrain (r₁ r₂ : ℕ) : Prop :=
  r₁ ≤ r₂ ∧ (∀ x, r₁ ≤ x → x < r₂ → IsTypeI σ x ∨ IsTypeI σ (x + 1)) ∧
    (r₁ = 0 ∨ ¬ (IsTypeI σ (r₁ - 1) ∨ IsTypeI σ r₁)) ∧ ¬ (IsTypeI σ r₂ ∨ IsTypeI σ (r₂ + 1))

/-- A **train boundary** after scale $2^y$: the forms of scales $2^y$ and $2^{y+1}$ both have type II, so they lie in
different trains. -/
def IsBoundary (y : ℕ) : Prop := ¬ IsTypeI σ y ∧ ¬ IsTypeI σ (y + 1)

/-- The number of minus signs among the scales $2^k$ with $k < y$. -/
def minusBelow : ℕ → ℕ
  | 0 => 0
  | y + 1 => minusBelow y + if (σ y).sign = .minus then 1 else 0

/-- The **compartment invariant** of the compartment $[2^{c_1}, 2^{c_2}]$: its total oddity
$\sum_{c_1 \le j \le c_2} t_j$ plus $4\sum_{c_1 \le y \le c_2 + 1}(\text{number of minus signs below } 2^y)$, modulo 8.
Oddity fusion keeps the total oddity; a walk step changes the total oddity of the one compartment it involves by $4$
and the sign count by $\pm1$. -/
def compartmentInvariant (c₁ c₂ : ℕ) : ZMod 8 :=
  ∑ j ∈ Icc c₁ c₂, (σ j).oddity + 4 * ∑ y ∈ Icc c₁ (c₂ + 1), (minusBelow σ y : ZMod 8)

end Intervals

/-! ### The moves -/

/-- A **walk step** at $j$ (Conway–Sloane, §7.5 (ii), p. 381–382, one step of a sign walk): the signs of the forms of
scales $2^j$ and $2^{j+1}$ change, and the oddity of the form of scale $2^i$ ($i \in \{j, j+1\}$, of type I)
changes by $4$. -/
def walkStep (σ : TwoSymbol) (j i : ℕ) : TwoSymbol := fun k =>
  { dim := (σ k).dim
    sign := if k = j ∨ k = j + 1 then (σ k).sign.flip else (σ k).sign
    type := (σ k).type
    oddity := if k = i then (σ k).oddity + 4 else (σ k).oddity }

/-- An **oddity fusion step** at $j$ (Conway–Sloane, §7.5 (i), p. 381): the amount $c$ of oddity is moved from the form
of scale $2^{j+1}$ to the form of scale $2^j$ (both of type I, so in one compartment). -/
def fuseStep (σ : TwoSymbol) (j : ℕ) (c : ZMod 8) : TwoSymbol := fun k =>
  { σ k with oddity := if k = j then (σ k).oddity + c else if k = j + 1 then (σ k).oddity - c else (σ k).oddity }

/-- The **elementary moves** on 2-adic symbols (Conway–Sloane, §7.5, pp. 381–382): walk steps between adjacent forms
of which the one whose oddity changes has type I, and oddity fusion steps between adjacent type I forms. -/
@[kb "conwaysloane1999" "Ch. 15, §7.5 (i), (ii), pp. 381–382"]
inductive Step : TwoSymbol → TwoSymbol → Prop
  /-- A walk step at $j$, changing the oddity of the type I form of scale $2^i$, $i \in \{j, j+1\}$. -/
  | walk (σ : TwoSymbol) (j i : ℕ) (hi : i = j ∨ i = j + 1) (hI : IsTypeI σ i) : Step σ (walkStep σ j i)
  /-- An oddity fusion step at $j$, both forms of type I. -/
  | fuse (σ : TwoSymbol) (j : ℕ) (c : ZMod 8) (h₁ : IsTypeI σ j) (h₂ : IsTypeI σ (j + 1)) :
      Step σ (fuseStep σ j c)

/-- **Equivalence of 2-adic symbols under sign walking and oddity fusion** (Conway–Sloane, §7.5, pp. 381–382): the
equivalence relation generated by the elementary moves. -/
@[kb "conwaysloane1999" "Ch. 15, §7.5, pp. 381–382"]
def MoveEquiv : TwoSymbol → TwoSymbol → Prop := Relation.EqvGen Step

/-! ### The moves preserve the invariants -/

section Invariance

theorem walkStep_dim (σ : TwoSymbol) (j i k : ℕ) : (walkStep σ j i k).dim = (σ k).dim := rfl
theorem walkStep_type (σ : TwoSymbol) (j i k : ℕ) : (walkStep σ j i k).type = (σ k).type := rfl
theorem fuseStep_dim (σ : TwoSymbol) (j : ℕ) (c : ZMod 8) (k : ℕ) : (fuseStep σ j c k).dim = (σ k).dim := rfl
theorem fuseStep_type (σ : TwoSymbol) (j : ℕ) (c : ZMod 8) (k : ℕ) : (fuseStep σ j c k).type = (σ k).type := rfl
theorem fuseStep_sign (σ : TwoSymbol) (j : ℕ) (c : ZMod 8) (k : ℕ) : (fuseStep σ j c k).sign = (σ k).sign := rfl

theorem Step.dim_eq {σ τ : TwoSymbol} (h : Step σ τ) (k : ℕ) : (τ k).dim = (σ k).dim := by
  cases h <;> rfl

theorem Step.type_eq {σ τ : TwoSymbol} (h : Step σ τ) (k : ℕ) : (τ k).type = (σ k).type := by
  cases h <;> rfl

theorem Step.isTypeI_iff {σ τ : TwoSymbol} (h : Step σ τ) (k : ℕ) : IsTypeI τ k ↔ IsTypeI σ k := by
  unfold IsTypeI; rw [h.type_eq]

/-- The indicator of a minus sign, times $4$, after a walk step at $j$: it changes by $4$ exactly at the scales
$2^j$, $2^{j+1}$. -/
theorem four_mul_ind_walkStep (σ : TwoSymbol) (j i y : ℕ) :
    (4 * ((if (walkStep σ j i y).sign = .minus then 1 else 0 : ℕ) : ZMod 8)) =
      4 * ((if (σ y).sign = .minus then 1 else 0 : ℕ) : ZMod 8) + if y = j ∨ y = j + 1 then 4 else 0 := by
  by_cases hy : y = j ∨ y = j + 1
  · simp only [walkStep, hy, if_true]
    cases (σ y).sign <;> decide
  · simp only [walkStep, hy, if_false, add_zero]

/-- Four times the minus-sign count below $2^y$, modulo 8, after a walk step at $j$: unchanged unless $y = j + 1$,
when it changes by $4$. -/
theorem four_mul_minusBelow_walkStep (σ : TwoSymbol) (j i : ℕ) : ∀ y,
    (4 * (minusBelow (walkStep σ j i) y : ZMod 8)) =
      4 * (minusBelow σ y : ZMod 8) + if y = j + 1 then 4 else 0
  | 0 => by simp [minusBelow]
  | y + 1 => by
    have ih := four_mul_minusBelow_walkStep σ j i y
    have h := four_mul_ind_walkStep σ j i y
    simp only [minusBelow, Nat.cast_add, mul_add] at ih h ⊢
    rw [ih, h]
    have h8 : (4 + 4 : ZMod 8) = 0 := by decide
    rcases Nat.lt_trichotomy y j with hy | rfl | hy
    · simp [show y ≠ j + 1 by omega, show y ≠ j by omega, show y + 1 ≠ j + 1 by omega]
    · simp <;> abel
    · rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hy) with h' | h'
      · subst h'
        simp only [if_true, or_true, show j + 1 + 1 ≠ j + 1 by omega, if_false]
        linear_combination h8
      · simp [show y ≠ j + 1 by omega, show y ≠ j by omega, show y + 1 ≠ j + 1 by omega]

theorem walkStep_oddity (σ : TwoSymbol) (j i k : ℕ) :
    (walkStep σ j i k).oddity = (σ k).oddity + if k = i then 4 else 0 := by
  simp only [walkStep]; split_ifs <;> simp

theorem fuseStep_oddity (σ : TwoSymbol) (j : ℕ) (c : ZMod 8) (k : ℕ) :
    (fuseStep σ j c k).oddity = (σ k).oddity + ((if k = j then c else 0) - if k = j + 1 then c else 0) := by
  simp only [fuseStep]; split_ifs <;> first | (exfalso; omega) | ring

theorem minusBelow_fuseStep (σ : TwoSymbol) (j : ℕ) (c : ZMod 8) : ∀ y,
    minusBelow (fuseStep σ j c) y = minusBelow σ y
  | 0 => rfl
  | y + 1 => by simp only [minusBelow, minusBelow_fuseStep σ j c y]; rfl

/-- Two adjacent type I forms lie in the same compartment: a compartment containing one of them contains both. -/
theorem IsCompartment.mem_iff_of_typeI {σ : TwoSymbol} {c₁ c₂ : ℕ} (hC : IsCompartment σ c₁ c₂) {j : ℕ}
    (h₁ : IsTypeI σ j) (h₂ : IsTypeI σ (j + 1)) : (c₁ ≤ j ∧ j ≤ c₂) ↔ (c₁ ≤ j + 1 ∧ j + 1 ≤ c₂) := by
  obtain ⟨_, _, hl, hr⟩ := hC
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨by omega, ?_⟩
    by_contra h
    exact hr (by rwa [show c₂ = j by omega])
  · rintro ⟨ha, hb⟩
    refine ⟨?_, by omega⟩
    by_contra h
    rcases hl with hl | hl
    · omega
    · exact hl (by rwa [show c₁ - 1 = j by omega])

/-- **The moves preserve the compartment invariants** (Conway–Sloane, §7.5, pp. 381–382). -/
theorem Step.compartmentInvariant_eq {σ τ : TwoSymbol} (h : Step σ τ) {c₁ c₂ : ℕ}
    (hC : IsCompartment σ c₁ c₂) : compartmentInvariant τ c₁ c₂ = compartmentInvariant σ c₁ c₂ := by
  cases h with
  | walk j i hi hI =>
    unfold compartmentInvariant
    simp only [walkStep_oddity, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mul_sum]
    simp only [four_mul_minusBelow_walkStep, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_Icc]
    have key : (c₁ ≤ i ∧ i ≤ c₂) ↔ (c₁ ≤ j + 1 ∧ j + 1 ≤ c₂ + 1) := by
      obtain ⟨_, hin, hl, hr⟩ := hC
      constructor
      · rintro ⟨ha, hb⟩; omega
      · rintro ⟨ha, hb⟩
        rcases hi with rfl | rfl
        · refine ⟨?_, ?_⟩
          · by_contra hlt
            rcases hl with hl | hl
            · omega
            · exact hl (by rwa [show c₁ - 1 = i by omega])
          · by_contra hlt
            omega
        · refine ⟨ha, ?_⟩
          by_contra hlt
          exact hr (by rwa [show c₂ + 1 = j + 1 by omega])
    have h8 : (4 + 4 : ZMod 8) = 0 := by decide
    by_cases hk : c₁ ≤ i ∧ i ≤ c₂
    · rw [if_pos hk, if_pos (key.mp hk)]
      linear_combination h8
    · rw [if_neg hk, if_neg (fun h => hk (key.mpr h))]
      ring
  | fuse j c h₁ h₂ =>
    unfold compartmentInvariant
    simp only [fuseStep_oddity, minusBelow_fuseStep, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_Icc]
    have key := hC.mem_iff_of_typeI h₁ h₂
    by_cases hk : c₁ ≤ j ∧ j ≤ c₂
    · rw [if_pos hk, if_pos (key.mp hk)]; ring
    · rw [if_neg hk, if_neg (fun h => hk (key.mpr h))]; ring

/-- **The moves preserve the signs at train boundaries**: the parity of the number of minus signs below every train
boundary (Conway–Sloane, §7.5, p. 381: a walk stays inside a train). -/
theorem Step.minusBelow_boundary {σ τ : TwoSymbol} (h : Step σ τ) {y : ℕ} (hy : IsBoundary σ y) :
    (4 * (minusBelow τ (y + 1) : ZMod 8)) = 4 * (minusBelow σ (y + 1) : ZMod 8) := by
  cases h with
  | walk j i hi hI =>
    rw [four_mul_minusBelow_walkStep, if_neg]
    · simp
    · intro hyj
      have : y = j := by omega
      subst this
      rcases hi with rfl | rfl
      · exact hy.1 hI
      · exact hy.2 hI
  | fuse j c h₁ h₂ => rw [minusBelow_fuseStep]

/-- The moves never change the oddity of a type II form. -/
theorem Step.oddity_typeII {σ τ : TwoSymbol} (h : Step σ τ) {k : ℕ} (hk : ¬ IsTypeI σ k) :
    (τ k).oddity = (σ k).oddity := by
  cases h with
  | walk j i hi hI =>
    rw [walkStep_oddity, if_neg (by rintro rfl; exact hk hI), add_zero]
  | fuse j c h₁ h₂ =>
    rw [fuseStep_oddity, if_neg (by rintro rfl; exact hk h₁), if_neg (by rintro rfl; exact hk h₂)]
    simp

/-- **The invariants of the moves** (Conway–Sloane, §7.5): the same dimensions and types at every scale, the same
oddities of the type II forms, the same parities of minus signs below every train boundary and the same compartment
invariants. -/
@[kb "conwaysloane1999" "Ch. 15, §7.5, pp. 381–382"]
structure SameInvariants (σ τ : TwoSymbol) : Prop where
  dim_eq : ∀ k, (τ k).dim = (σ k).dim
  type_eq : ∀ k, (τ k).type = (σ k).type
  oddity_typeII : ∀ k, ¬ IsTypeI σ k → (τ k).oddity = (σ k).oddity
  boundary : ∀ y, IsBoundary σ y → (4 * (minusBelow τ (y + 1) : ZMod 8)) = 4 * (minusBelow σ (y + 1) : ZMod 8)
  compartment : ∀ c₁ c₂, IsCompartment σ c₁ c₂ → compartmentInvariant τ c₁ c₂ = compartmentInvariant σ c₁ c₂

theorem SameInvariants.refl (σ : TwoSymbol) : SameInvariants σ σ :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem SameInvariants.isTypeI_iff {σ τ : TwoSymbol} (h : SameInvariants σ τ) (k : ℕ) :
    IsTypeI τ k ↔ IsTypeI σ k := by
  unfold IsTypeI; rw [h.type_eq]

theorem SameInvariants.isBoundary_iff {σ τ : TwoSymbol} (h : SameInvariants σ τ) (y : ℕ) :
    IsBoundary τ y ↔ IsBoundary σ y := by
  unfold IsBoundary; rw [h.isTypeI_iff, h.isTypeI_iff]

theorem SameInvariants.isCompartment_iff {σ τ : TwoSymbol} (h : SameInvariants σ τ) (c₁ c₂ : ℕ) :
    IsCompartment τ c₁ c₂ ↔ IsCompartment σ c₁ c₂ := by
  unfold IsCompartment; simp only [h.isTypeI_iff]

theorem SameInvariants.symm {σ τ : TwoSymbol} (h : SameInvariants σ τ) : SameInvariants τ σ where
  dim_eq k := (h.dim_eq k).symm
  type_eq k := (h.type_eq k).symm
  oddity_typeII k hk := (h.oddity_typeII k (by rwa [← h.isTypeI_iff])).symm
  boundary y hy := (h.boundary y ((h.isBoundary_iff y).mp hy)).symm
  compartment c₁ c₂ hC := (h.compartment c₁ c₂ ((h.isCompartment_iff c₁ c₂).mp hC)).symm

theorem SameInvariants.trans {σ τ υ : TwoSymbol} (h₁ : SameInvariants σ τ) (h₂ : SameInvariants τ υ) :
    SameInvariants σ υ where
  dim_eq k := (h₂.dim_eq k).trans (h₁.dim_eq k)
  type_eq k := (h₂.type_eq k).trans (h₁.type_eq k)
  oddity_typeII k hk := (h₂.oddity_typeII k (by rwa [h₁.isTypeI_iff])).trans (h₁.oddity_typeII k hk)
  boundary y hy := (h₂.boundary y ((h₁.isBoundary_iff y).mpr hy)).trans (h₁.boundary y hy)
  compartment c₁ c₂ hC :=
    (h₂.compartment c₁ c₂ ((h₁.isCompartment_iff c₁ c₂).mpr hC)).trans (h₁.compartment c₁ c₂ hC)

theorem Step.sameInvariants {σ τ : TwoSymbol} (h : Step σ τ) : SameInvariants σ τ where
  dim_eq := h.dim_eq
  type_eq := h.type_eq
  oddity_typeII _ hk := h.oddity_typeII hk
  boundary _ hy := h.minusBelow_boundary hy
  compartment _ _ hC := h.compartmentInvariant_eq hC

/-- **Soundness of the invariants**: symbols related by sign walking and oddity fusion have the same invariants. -/
@[kb "conwaysloane1999" "Ch. 15, §7.5, pp. 381–382"]
theorem MoveEquiv.sameInvariants {σ τ : TwoSymbol} (h : MoveEquiv σ τ) : SameInvariants σ τ := by
  induction h with
  | rel _ _ h => exact h.sameInvariants
  | refl => exact SameInvariants.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem minusBelow_congr {σ τ : TwoSymbol} : ∀ {y : ℕ}, (∀ k < y, (σ k).sign = (τ k).sign) →
    minusBelow σ y = minusBelow τ y
  | 0, _ => rfl
  | y + 1, h => by
    show minusBelow σ y + _ = minusBelow τ y + _
    rw [minusBelow_congr (fun k hk => h k (by omega)), h y (by omega)]

theorem sign_eq_of_four_mul {σ τ : TwoSymbol} {m : ℕ} (hm : minusBelow σ m = minusBelow τ m)
    (h : (4 * (minusBelow σ (m + 1) : ZMod 8)) = 4 * (minusBelow τ (m + 1) : ZMod 8)) :
    (σ m).sign = (τ m).sign := by
  simp only [minusBelow, hm, Nat.cast_add, mul_add, add_right_inj] at h
  cases hs : (σ m).sign <;> cases ht : (τ m).sign <;> simp_all <;> revert h <;> decide

end Invariance

/-! ### Completeness of the invariants -/

section Completeness

/-- One more agreeing scale: if $\sigma$ and $	au$ have the same invariants and agree below $2^m$, a sequence of at most
two moves makes $\sigma$ agree with $	au$ below $2^{m+1}$. -/
theorem exists_moveEquiv_agree_succ {σ τ : TwoSymbol} (hS : SameInvariants σ τ) {m : ℕ}
    (hm : ∀ k < m, σ k = τ k) :
    ∃ σ', MoveEquiv σ σ' ∧ SameInvariants σ' τ ∧ ∀ k < m + 1, σ' k = τ k := by
  -- Step 1: the sign at 2^m.
  obtain ⟨σ₁, h₁, hS₁, hm₁, hsign⟩ : ∃ σ₁, MoveEquiv σ σ₁ ∧ SameInvariants σ₁ τ ∧ (∀ k < m, σ₁ k = τ k) ∧
      (σ₁ m).sign = (τ m).sign := by
    by_cases hs : (σ m).sign = (τ m).sign
    · exact ⟨σ, Relation.EqvGen.refl _, hS, hm, hs⟩
    · have hI : IsTypeI σ m ∨ IsTypeI σ (m + 1) := by
        by_contra hI
        push Not at hI
        have hb := hS.boundary m ⟨hI.1, hI.2⟩
        have hmb : minusBelow σ m = minusBelow τ m :=
          minusBelow_congr fun k hk => by rw [hm k hk]
        exact hs (sign_eq_of_four_mul hmb hb.symm)
      obtain ⟨i, hi, hIi⟩ : ∃ i, (i = m ∨ i = m + 1) ∧ IsTypeI σ i := by
        rcases hI with h | h
        · exact ⟨m, Or.inl rfl, h⟩
        · exact ⟨m + 1, Or.inr rfl, h⟩
      have hstep := Step.walk σ m i hi hIi
      refine ⟨walkStep σ m i, Relation.EqvGen.rel _ _ hstep, hstep.sameInvariants.symm.trans hS, ?_, ?_⟩
      · intro k hk
        rw [← hm k hk]
        simp only [walkStep]
        congr 1
        · simp [show ¬ (k = m ∨ k = m + 1) by omega]
        · rw [if_neg (by rcases hi with rfl | rfl <;> omega)]
      · simp only [walkStep, true_or, if_true]
        cases h1 : (σ m).sign <;> cases h2 : (τ m).sign <;> simp_all [Sign.flip]
  -- Step 2: the oddity at 2^m.
  have hdim : (σ₁ m).dim = (τ m).dim := (hS₁.dim_eq m).symm
  have htype : (σ₁ m).type = (τ m).type := (hS₁.type_eq m).symm
  by_cases ho : (σ₁ m).oddity = (τ m).oddity
  · refine ⟨σ₁, h₁, hS₁, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact hm₁ k hk
    · cases h : σ₁ k; cases h' : τ k; simp_all
  · have hI : IsTypeI σ₁ m := by
      by_contra hI
      exact ho (hS₁.oddity_typeII m hI).symm
    by_cases hI' : IsTypeI σ₁ (m + 1)
    · have hstep := Step.fuse σ₁ m ((τ m).oddity - (σ₁ m).oddity) hI hI'
      refine ⟨_, h₁.trans _ _ _ (Relation.EqvGen.rel _ _ hstep), hstep.sameInvariants.symm.trans hS₁,
        fun k hk => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · rw [← hm₁ k hk]
        simp only [fuseStep, if_neg (show k ≠ m by omega), if_neg (show k ≠ m + 1 by omega)]
      · have e : (fuseStep σ₁ k ((τ k).oddity - (σ₁ k).oddity) k) =
            { σ₁ k with oddity := (τ k).oddity } := by
          simp only [fuseStep, if_true]; congr 1; ring
        rw [e]
        cases h : σ₁ k; cases h' : τ k; simp_all
    · -- 2^m ends a compartment [2^c, 2^m]: the compartment invariant forces the oddity
      exfalso
      classical
      let P : ℕ → Prop := fun c => c ≤ m ∧ ∀ x, c ≤ x → x ≤ m → IsTypeI σ₁ x
      have hP : ∃ c, P c := ⟨m, le_refl m, fun x h1 h2 => by rwa [show x = m by omega]⟩
      let c := Nat.find hP
      have hc : P c := Nat.find_spec hP
      have hC : IsCompartment σ₁ c m := by
        refine ⟨hc.1, hc.2, ?_, hI'⟩
        by_cases hc0 : c = 0
        · exact Or.inl hc0
        · refine Or.inr fun hlt => ?_
          have := Nat.find_min hP (show c - 1 < c by omega)
          exact this ⟨by omega, fun x h1 h2 => by
            rcases Nat.eq_or_lt_of_le h1 with h | h
            · rwa [← h]
            · exact hc.2 x (by omega) h2⟩
      have hinv := hS₁.compartment c m hC
      unfold compartmentInvariant at hinv
      have hmb : ∀ y ∈ Icc c (m + 1), minusBelow τ y = minusBelow σ₁ y := by
        intro y hy
        refine minusBelow_congr fun k hk => ?_
        have := (Finset.mem_Icc.mp hy).2
        rcases Nat.lt_succ_iff_lt_or_eq.mp (show k < m + 1 by omega) with hk' | rfl
        · rw [hm₁ k hk']
        · exact hsign.symm
      have hsum : ∑ y ∈ Icc c (m + 1), (minusBelow τ y : ZMod 8) =
          ∑ y ∈ Icc c (m + 1), (minusBelow σ₁ y : ZMod 8) :=
        Finset.sum_congr rfl fun y hy => by rw [hmb y hy]
      rw [hsum] at hinv
      have hmem : m ∈ Icc c m := Finset.mem_Icc.mpr ⟨hc.1, le_refl m⟩
      rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem] at hinv
      have hrest : ∑ j ∈ (Icc c m).erase m, (τ j).oddity = ∑ j ∈ (Icc c m).erase m, (σ₁ j).oddity := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have := Finset.mem_erase.mp hj
        have := Finset.mem_Icc.mp this.2
        rw [hm₁ j (by omega)]
      rw [hrest] at hinv
      exact ho (add_right_cancel (add_right_cancel hinv)).symm

/-- Beyond the last type I form, agreement below $2^m$ propagates: symbols with the same invariants whose forms of
scale $\ge 2^B$ are all of type II, and which agree below $2^m$ with $m \ge B$, are equal. -/
theorem eq_of_agree_of_typeII {σ τ : TwoSymbol} (hS : SameInvariants σ τ) {B : ℕ}
    (hB : ∀ k, B ≤ k → ¬ IsTypeI σ k) {m : ℕ} (hmB : B ≤ m) (hm : ∀ k < m, σ k = τ k) : σ = τ := by
  have key : ∀ k, ∀ j < m + k, σ j = τ j := by
    intro k
    induction k with
    | zero => simpa using hm
    | succ k ih =>
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp (show j < m + k + 1 by omega) with hj | rfl
      · exact ih j hj
      · have hsign : (σ (m + k)).sign = (τ (m + k)).sign := by
          have hb := hS.boundary (m + k) ⟨hB _ (by omega), hB _ (by omega)⟩
          exact sign_eq_of_four_mul (minusBelow_congr fun i hi => by rw [ih i hi]) hb.symm
        have ho := hS.oddity_typeII (m + k) (hB _ (by omega))
        have hd := hS.dim_eq (m + k)
        have ht := hS.type_eq (m + k)
        cases h : σ (m + k); cases h' : τ (m + k); simp_all
  funext k
  exact key (k + 1) k (by omega)

/-- **Completeness of the invariants** (Conway–Sloane, §7.5–7.6): two 2-adic symbols with the same invariants, whose
forms are of type II beyond some scale, are related by sign walking and oddity fusion. -/
@[kb "conwaysloane1999" "Ch. 15, §7.5–7.6, pp. 381–382"]
theorem moveEquiv_of_sameInvariants {σ τ : TwoSymbol} (hS : SameInvariants σ τ) {B : ℕ}
    (hB : ∀ k, B ≤ k → ¬ IsTypeI σ k) : MoveEquiv σ τ := by
  have key : ∀ m, ∃ σ', MoveEquiv σ σ' ∧ SameInvariants σ' τ ∧ ∀ k < m, σ' k = τ k := by
    intro m
    induction m with
    | zero => exact ⟨σ, Relation.EqvGen.refl _, hS, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    | succ m ih =>
      obtain ⟨σ', h, hS', hm⟩ := ih
      obtain ⟨σ'', h', hS'', hm'⟩ := exists_moveEquiv_agree_succ hS' hm
      exact ⟨σ'', h.trans _ _ _ h', hS'', hm'⟩
  obtain ⟨σ', h, hS', hm⟩ := key B
  have hB' : ∀ k, B ≤ k → ¬ IsTypeI σ' k := fun k hk => by
    rw [(h.sameInvariants).isTypeI_iff]; exact hB k hk
  rw [eq_of_agree_of_typeII hS' hB' le_rfl hm] at h
  exact h

/-- **Sign walking and oddity fusion are exactly the invariants** (Conway–Sloane, §7.5): for 2-adic symbols with
finitely many type I forms, `MoveEquiv σ τ ↔ SameInvariants σ τ`. -/
@[kb "conwaysloane1999" "Ch. 15, §7.5–7.6, pp. 381–382"]
theorem moveEquiv_iff_sameInvariants {σ τ : TwoSymbol} {B : ℕ} (hB : ∀ k, B ≤ k → ¬ IsTypeI σ k) :
    MoveEquiv σ τ ↔ SameInvariants σ τ :=
  ⟨MoveEquiv.sameInvariants, fun h => moveEquiv_of_sameInvariants h hB⟩

end Completeness

end QuadFormsKB.ConwaySloane
