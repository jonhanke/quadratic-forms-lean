/-
# Moreno–Wagstaff 2005, §8.2: Gauss's and Jacobsthal's theorems (Theorems 8.2 and 8.3)

**Source.** C. J. Moreno and S. S. Wagstaff Jr., *Sums of Squares of Integers* (2005), §8.2, p. 322
(results of Gauss and of E. Jacobsthal, *Über die Darstellung der Primzahlen der Form 4n+1 als Summe zweier
Quadrate*, 1907, cited there without proof).

**Proves** (both unconditional)
* `theorem83` (Jacobsthal): for a prime $p = a^2 + b^2 \equiv 1 \pmod 4$ with $a \equiv 1 \pmod 4$,
  $a = -\sum_{j=1}^{(p-1)/2} (j/p)((j^2+1)/p)$.
* `theorem82` (Gauss): in the same situation $2a \equiv \binom{2k}{k} \pmod p$ ($p = 4k+1$) and $2|a| < p$.

**Method (Jacobsthal sums).** Let $\chi$ be the quadratic character of $\mathbb{F}_p$ and
$S(k) = \sum_x \chi(x)\chi(x^2+k)$.
1. $\chi(-1) = 1$, so $S(k) = 2\sum_{x \in P}\chi(x)\chi(x^2+k)$ with $P$ the "first half" of $\mathbb{F}_p^\times$;
   for $k = 1$ this half-sum is the sum in Theorem 8.3.
2. $S(kt^2) = \chi(t)S(k)$, so $S(k)^2 \in \{0, S(1)^2, S(r)^2\}$ ($r$ a nonsquare); with
   $\sum_k \chi((k+\alpha)(k+\beta)) = p\,[\alpha = \beta] - 1$ one gets $\sum_k S(k)^2 = 2p(p-1)$, hence
   $S(1)^2 + S(r)^2 = 4p$, i.e. $H^2 + H'^2 = p$ with $S(1) = 2H$, $S(r) = 2H'$.
3. The involution $x \mapsto \pm x^{-1}$ of $P$ preserves $\chi(x)\chi(x^2+1)$; its only exceptional points are
   $x = 1$ (value $\chi(2)$) and the root of $x^2 = -1$ in $P$ (value $0$). Hence $H \equiv \chi(2) + |P| - 2
   \equiv 3 \pmod 4$ (using $\chi(2) = \chi_8(p)$).
4. `corollary21` (uniqueness of the two-squares representation) gives $|a| = |H|$; the congruence mod $4$ gives
   $a = -H$ (Theorem 8.3).
5. Euler's criterion $\chi(y) \equiv y^{(p-1)/2}$ and the binomial theorem give
   $S(1) \equiv -\binom{2k}{k} \pmod p$ (power sums over $\mathbb{F}_p$), hence Theorem 8.2.
-/
import QuadFormsKB.Literature.MorenoWagstaff.Ch2ProofsB
import QuadFormsKB.Literature.MorenoWagstaff.Ch6to8Statements
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.ValMinAbs

namespace QuadFormsKB.MorenoWagstaff

namespace Jacobsthal

section Basic

variable {p : ℕ} [Fact p.Prime]

local notation "χ" => quadraticChar (ZMod p)

lemma ringChar_ne_two (hp : p % 4 = 1) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; omega

lemma neg_ne_self (hp : p % 4 = 1) {x : ZMod p} (hx : x ≠ 0) : -x ≠ x := by
  intro h
  have h2 : (2 : ZMod p) * x = 0 := by linear_combination -h
  rcases mul_eq_zero.mp h2 with h | h
  · have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    have := (Fact.out : p.Prime).two_le
    omega
  · exact hx h

lemma chi_neg (hp : p % 4 = 1) (x : ZMod p) : χ (-x) = χ x := by
  have h : χ (-1) = 1 := by
    rw [quadraticChar_neg_one (ringChar_ne_two hp)]
    simp [ZMod.card, ZMod.χ₄_nat_one_mod_four hp]
  rw [show -x = -1 * x by ring, map_mul, h, one_mul]

lemma chi_sq (x : ZMod p) : χ (x ^ 2) = if x = 0 then 0 else 1 := by
  split_ifs with h
  · simp [h]
  · exact quadraticChar_sq_one' h

lemma chi_mul_self (x : ZMod p) : χ x * χ x = if x = 0 then 0 else 1 := by
  rw [← map_mul, ← sq, chi_sq]

lemma chi_inv (x : ZMod p) : χ x⁻¹ = χ x := by
  by_cases hx : x = 0
  · simp [hx]
  · have : x⁻¹ = x * (x⁻¹) ^ 2 := by field_simp
    conv_lhs => rw [this]
    rw [map_mul, quadraticChar_sq_one' (inv_ne_zero hx), mul_one]

lemma sum_chi (hp : p % 4 = 1) : ∑ x : ZMod p, χ x = 0 :=
  quadraticChar_sum_zero (ringChar_ne_two hp)

/-- Sum of $\chi((k+\alpha)(k+\beta))$ over $k$. -/
lemma sum_chi_mul_shift (hp : p % 4 = 1) (α β : ZMod p) :
    ∑ k : ZMod p, χ ((k + α) * (k + β)) = if α = β then (p : ℤ) - 1 else -1 := by
  split_ifs with h
  · subst h
    have : ∀ k : ZMod p, χ ((k + α) * (k + α)) = 1 - if k = -α then 1 else 0 := by
      intro k
      rw [← sq, chi_sq]
      by_cases hk : k = -α
      · simp [hk]
      · have : k + α ≠ 0 := fun h => hk (by linear_combination h)
        simp [hk, this]
    simp only [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp
  · set c := β - α with hc
    have hc0 : c ≠ 0 := fun h0 => h (by linear_combination -h0)
    have h1 := Equiv.sum_comp (Equiv.addRight α) (fun k : ZMod p => χ (k * (k + c)))
    have h2 : ∑ k : ZMod p, χ ((k + α) * (k + β)) = ∑ k : ZMod p, χ (k * (k + c)) := by
      rw [← h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Equiv.coe_addRight, hc]
      congr 1; ring
    rw [h2]
    have h3 : ∀ k : ZMod p, χ (k * (k + c)) =
        χ (1 + c * k⁻¹) - if k = 0 then 1 else 0 := by
      intro k
      by_cases hk : k = 0
      · simp [hk]
      · have : k * (k + c) = k ^ 2 * (1 + c * k⁻¹) := by field_simp
        rw [this, map_mul, quadraticChar_sq_one' hk]
        simp [hk]
    simp only [h3, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have h4 : ∑ k : ZMod p, χ (1 + c * k⁻¹) = ∑ k : ZMod p, χ k := by
      have e1 : ∑ k : ZMod p, χ (1 + c * k⁻¹) = ∑ k : ZMod p, χ (1 + c * k) :=
        Equiv.sum_comp (Function.Involutive.toPerm (fun k : ZMod p => k⁻¹) inv_inv)
          (fun k => χ (1 + c * k))
      have e2 : ∑ k : ZMod p, χ (1 + c * k) = ∑ k : ZMod p, χ k :=
        Equiv.sum_comp ((Equiv.mulLeft₀ c hc0).trans (Equiv.addLeft 1)) (fun k => χ k)
      rw [e1, e2]
    rw [h4, sum_chi hp]
    simp

/-- The Jacobsthal sum $S(k) = \sum_{x \in \mathbb{F}_p} \chi(x)\chi(x^2 + k)$. -/
def S (k : ZMod p) : ℤ := ∑ x : ZMod p, χ x * χ (x ^ 2 + k)

lemma S_zero (hp : p % 4 = 1) : S (0 : ZMod p) = 0 := by
  unfold S
  have : ∀ x : ZMod p, χ x * χ (x ^ 2 + 0) = χ x := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · simp [quadraticChar_sq_one' hx]
  simp only [this]
  exact sum_chi hp

lemma S_scale {t : ZMod p} (ht : t ≠ 0) (k : ZMod p) : S (k * t ^ 2) = χ t * S k := by
  unfold S
  rw [← Equiv.sum_comp (Equiv.mulLeft₀ t ht), Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  show χ (t * y) * χ ((t * y) ^ 2 + k * t ^ 2) = χ t * (χ y * χ (y ^ 2 + k))
  have : (t * y) ^ 2 + k * t ^ 2 = t ^ 2 * (y ^ 2 + k) := by ring
  rw [this, map_mul, map_mul, quadraticChar_sq_one' ht]
  ring

lemma two_S_sq (hp : p % 4 = 1) {r : ZMod p} (hr : χ r = -1) (k : ZMod p) :
    2 * S k ^ 2 = (χ k ^ 2 + χ k) * S (1 : ZMod p) ^ 2 + (χ k ^ 2 - χ k) * S r ^ 2 := by
  by_cases hk : k = 0
  · subst hk
    simp [S_zero hp]
  rcases quadraticChar_dichotomy hk with h | h
  · obtain ⟨t, ht⟩ := (quadraticChar_one_iff_isSquare hk).mp h
    have ht0 : t ≠ 0 := by rintro rfl; exact hk (by simpa using ht)
    have : S k = χ t * S (1 : ZMod p) := by
      rw [← S_scale ht0, one_mul, ht]; ring_nf
    have h2 : χ t ^ 2 = 1 := quadraticChar_sq_one ht0
    rw [this, mul_pow, h2, h]
    ring
  · have hr0 : r ≠ 0 := by rintro rfl; simp at hr
    have h1 : χ (k * r⁻¹) = 1 := by rw [map_mul, chi_inv, h, hr]; norm_num
    have hkr : k * r⁻¹ ≠ 0 := mul_ne_zero hk (inv_ne_zero hr0)
    obtain ⟨t, ht⟩ := (quadraticChar_one_iff_isSquare hkr).mp h1
    have ht0 : t ≠ 0 := by rintro rfl; simp at ht; tauto
    have hk' : k = r * t ^ 2 := by
      have : k = k * r⁻¹ * r := by field_simp
      rw [this, ht]; ring
    have : S k = χ t * S r := by rw [hk', S_scale ht0]
    have h2 : χ t ^ 2 = 1 := quadraticChar_sq_one ht0
    rw [this, mul_pow, h2, h]
    ring

lemma sum_inner (hp : p % 4 = 1) (x : ZMod p) :
    ∑ y : ZMod p, (if x ^ 2 = y ^ 2 then χ x * χ y else 0) = if x = 0 then 0 else 2 := by
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [show (if x = 0 then (0 : ℤ) else 2) = 2 by simp [hx], Finset.sum_eq_add x (-x) (fun h => (neg_ne_self hp hx) h.symm)]
    · simp only [ite_true, neg_sq, chi_neg hp]
      rw [chi_mul_self]; simp [hx]
    · intro y _ hy
      rw [ite_eq_right_iff]
      intro h
      exfalso
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
      · exact hy.1 h.symm
      · exact hy.2 (by rw [h]; ring)
    · simp
    · simp

lemma sum_S_sq (hp : p % 4 = 1) : ∑ k : ZMod p, S k ^ 2 = 2 * p * (p - 1) := by
  have h1 : ∀ k : ZMod p, S k ^ 2 = ∑ x : ZMod p, ∑ y : ZMod p,
      χ x * χ y * χ ((k + x ^ 2) * (k + y ^ 2)) := by
    intro k
    rw [sq]
    unfold S
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [show (k + x ^ 2) * (k + y ^ 2) = (x ^ 2 + k) * (y ^ 2 + k) by ring, map_mul]
    ring
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ x : ZMod p, ∑ k : ZMod p, ∑ y : ZMod p, χ x * χ y * χ ((k + x ^ 2) * (k + y ^ 2)) =
      ∑ y : ZMod p, χ x * χ y * (if x ^ 2 = y ^ 2 then (p : ℤ) - 1 else -1) := by
    intro x
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.mul_sum, sum_chi_mul_shift hp]
  simp only [h2]
  have key : ∀ x y : ZMod p, χ x * χ y * (if x ^ 2 = y ^ 2 then (p : ℤ) - 1 else -1) =
      p * (if x ^ 2 = y ^ 2 then χ x * χ y else 0) - χ x * χ y := by
    intro x y
    split_ifs <;> ring
  simp only [key, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_inner hp]
  simp only [sum_chi hp, mul_zero, Finset.sum_const_zero, sub_zero]
  have h4 : ∑ x : ZMod p, (if x = 0 then (0 : ℤ) else 2) = 2 * (p - 1) := by
    have : ∀ x : ZMod p, (if x = 0 then (0 : ℤ) else 2) = 2 - if x = 0 then 2 else 0 := by
      intro x; split_ifs <;> simp
    simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Finset.sum_const, Finset.card_univ, ZMod.card]
    simp; ring
  rw [h4]; ring

lemma sum_chi_sq (_hp : p % 4 = 1) : ∑ k : ZMod p, χ k ^ 2 = p - 1 := by
  have : ∀ k : ZMod p, χ k ^ 2 = 1 - if k = 0 then 1 else 0 := by
    intro k; rw [sq, chi_mul_self]; split_ifs <;> simp
  simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, ZMod.card]
  simp

lemma exists_nonsquare (hp : p % 4 = 1) : ∃ r : ZMod p, χ r = -1 :=
  quadraticChar_exists_neg_one (ringChar_ne_two hp)

lemma S_one_sq_add (hp : p % 4 = 1) {r : ZMod p} (hr : χ r = -1) :
    S (1 : ZMod p) ^ 2 + S r ^ 2 = 4 * p := by
  have h := Finset.sum_congr (rfl : (Finset.univ : Finset (ZMod p)) = Finset.univ)
    (fun k _ => two_S_sq hp hr k)
  rw [← Finset.mul_sum, sum_S_sq hp, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_chi_sq hp, sum_chi hp] at h
  have hp1 : (p : ℤ) - 1 ≠ 0 := by
    have := (Fact.out : p.Prime).two_le
    omega
  apply mul_left_cancel₀ hp1
  linear_combination (-1 : ℤ) * h

/-- The set of residues with positive least-absolute-value representative ("the first half"). -/
def P : Finset (ZMod p) := Finset.univ.filter fun x => 0 < x.valMinAbs

lemma mem_P {x : ZMod p} : x ∈ P ↔ 0 < x.valMinAbs := by simp [P]

lemma neg_mem_P_iff (hp : p % 4 = 1) {x : ZMod p} (hx : x ≠ 0) : -x ∈ P ↔ x ∉ P := by
  have hne : 2 * x.val ≠ p := by omega
  rw [mem_P, mem_P, ZMod.valMinAbs_neg_of_ne_half hne]
  have : x.valMinAbs ≠ 0 := fun h => hx ((ZMod.valMinAbs_eq_zero x).mp h)
  omega

lemma sum_eq_two_mul_half (hp : p % 4 = 1) {g : ZMod p → ℤ} (hneg : ∀ x, g (-x) = g x)
    (h0 : g 0 = 0) : ∑ x, g x = 2 * ∑ x ∈ P, g x := by
  have hA : ∑ x ∈ P, g x = ∑ x : ZMod p, if x ∈ P then g x else 0 := by
    simp only [P, Finset.sum_filter, Finset.mem_filter, Finset.mem_univ, true_and]
  have hB : ∑ x : ZMod p, (if x ∈ P then 0 else g x) = ∑ x : ZMod p, if x ∈ P then g x else 0 := by
    rw [← Equiv.sum_comp (Equiv.neg (ZMod p))]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x = 0
    · subst hx; simp [h0]
    · simp only [Equiv.neg_apply, hneg]
      by_cases h : x ∈ P
      · simp [h, (neg_mem_P_iff hp hx).not.mpr (not_not.mpr h)]
      · have : -x ∈ P := (neg_mem_P_iff hp hx).mpr h
        simp [h, this]
  calc ∑ x, g x = ∑ x : ZMod p, ((if x ∈ P then g x else 0) + (if x ∈ P then 0 else g x)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        split_ifs <;> simp
    _ = 2 * ∑ x ∈ P, g x := by
        rw [Finset.sum_add_distrib, hB, ← hA]; ring

lemma S_eq_two_mul_half (hp : p % 4 = 1) (k : ZMod p) :
    S k = 2 * ∑ x ∈ P, χ x * χ (x ^ 2 + k) := by
  unfold S
  refine sum_eq_two_mul_half hp (fun x => ?_) (by simp)
  simp only [chi_neg hp, neg_sq]

lemma Icc_sum_eq (hp : p % 4 = 1) :
    ∑ j ∈ Finset.Icc (1 : ℤ) (((p : ℤ) - 1) / 2), legendreSym p j * legendreSym p (j ^ 2 + 1) =
      ∑ x ∈ (P : Finset (ZMod p)), χ x * χ (x ^ 2 + 1) := by
  have hv : ∀ j ∈ Finset.Icc (1 : ℤ) (((p : ℤ) - 1) / 2), ((j : ZMod p)).valMinAbs = j := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [ZMod.valMinAbs_spec]
    refine ⟨rfl, ?_, ?_⟩ <;> omega
  refine Finset.sum_nbij' (fun j : ℤ => (j : ZMod p)) (fun x : ZMod p => x.valMinAbs)
    ?_ ?_ ?_ ?_ ?_
  · intro j hj
    rw [mem_P, hv j hj]
    have := (Finset.mem_Icc.mp hj).1
    omega
  · intro x hx
    rw [mem_P] at hx
    have := ZMod.valMinAbs_mem_Ioc x
    have h2 : x.valMinAbs * 2 ≠ p := by
      intro h; omega
    rw [Finset.mem_Icc]
    simp only [Set.mem_Ioc] at this
    omega
  · intro j hj
    exact hv j hj
  · intro x _
    exact ZMod.coe_valMinAbs x
  · intro j _
    simp [legendreSym]

/-- A fixed-point-free involution preserving a $\pm1$-valued function: the sum is $\equiv |s| \pmod 4$. -/
lemma sum_sign_involution {α : Type*} [DecidableEq α] (s : Finset α) (σ : α → α) (g : α → ℤ)
    (hmem : ∀ x ∈ s, σ x ∈ s) (hinv : ∀ x ∈ s, σ (σ x) = x) (hfix : ∀ x ∈ s, σ x ≠ x)
    (hg : ∀ x ∈ s, g (σ x) = g x) (h1 : ∀ x ∈ s, g x = 1 ∨ g x = -1) :
    ∑ x ∈ s, g x ≡ (s.card : ℤ) [ZMOD 4] := by
  have h0 : ∑ x ∈ s, (if g x = -1 then (1 : ZMod 2) else 0) = 0 := by
    refine Finset.sum_involution (fun a _ => σ a) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [hg a ha]
      split_ifs <;> decide
    · intro a ha _
      exact hfix a ha
    · exact hmem
    · exact hinv
  rw [Finset.sum_boole, ZMod.natCast_eq_zero_iff] at h0
  obtain ⟨m, hm⟩ := h0
  have h3 : ∑ x ∈ s, g x = s.card - 2 * ((s.filter fun x => g x = -1).card : ℤ) := by
    have : ∀ x ∈ s, g x = 1 - 2 * (if g x = -1 then (1 : ℤ) else 0) := by
      intro x hx
      rcases h1 x hx with h | h <;> simp [h]
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
    simp
  rw [h3, hm]
  unfold Int.ModEq
  push_cast
  omega

lemma one_mem_P : (1 : ZMod p) ∈ P := by
  rw [mem_P]
  have h2 := (Fact.out : p.Prime).two_le
  have : (1 : ZMod p).valMinAbs = 1 := by
    rw [ZMod.valMinAbs_spec]
    refine ⟨by simp, ?_⟩
    simp only [Set.mem_Ioc]
    omega
  omega

lemma ne_zero_of_mem_P {x : ZMod p} (hx : x ∈ P) : x ≠ 0 := by
  rintro rfl
  rw [mem_P] at hx
  simp at hx

lemma card_P (hp : p % 4 = 1) : (P : Finset (ZMod p)).card = (p - 1) / 2 := by
  have hv : ∀ j ∈ Finset.Icc (1 : ℤ) (((p : ℤ) - 1) / 2), ((j : ZMod p)).valMinAbs = j := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [ZMod.valMinAbs_spec]
    refine ⟨rfl, ?_, ?_⟩ <;> omega
  have h : (Finset.Icc (1 : ℤ) (((p : ℤ) - 1) / 2)).card = (P : Finset (ZMod p)).card := by
    refine Finset.card_nbij' (fun j : ℤ => (j : ZMod p)) (fun x : ZMod p => x.valMinAbs)
      ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_coe, mem_P, hv j hj]
      have := (Finset.mem_Icc.mp (Finset.mem_coe.mp hj)).1
      omega
    · intro x hx
      rw [Finset.mem_coe, mem_P] at hx
      have := ZMod.valMinAbs_mem_Ioc x
      have h2 : x.valMinAbs * 2 ≠ p := by
        intro h; omega
      beta_reduce
      rw [Finset.mem_coe, Finset.mem_Icc]
      simp only [Set.mem_Ioc] at this
      omega
    · intro j hj
      exact hv j hj
    · intro x _
      exact ZMod.coe_valMinAbs x
  rw [← h, Int.card_Icc]
  omega

/-- Normalize a nonzero residue into $P$ by a sign. -/
def rho (y : ZMod p) : ZMod p := if y ∈ P then y else -y

lemma rho_mem (hp : p % 4 = 1) {y : ZMod p} (hy : y ≠ 0) : rho y ∈ P := by
  unfold rho
  split_ifs with h
  · exact h
  · exact (neg_mem_P_iff hp hy).mpr h

/-- The involution $x \mapsto \pm x^{-1}$ of $P$. -/
def tau (x : ZMod p) : ZMod p := rho x⁻¹

/-- The summand of $S(1)$. -/
def g1 (x : ZMod p) : ℤ := χ x * χ (x ^ 2 + 1)

lemma g1_neg (hp : p % 4 = 1) (x : ZMod p) : g1 (-x) = g1 x := by
  simp only [g1, chi_neg hp, neg_sq]

lemma g1_inv (x : ZMod p) : g1 x⁻¹ = g1 x := by
  by_cases hx : x = 0
  · simp [hx]
  · have : (x⁻¹) ^ 2 + 1 = (x⁻¹) ^ 2 * (x ^ 2 + 1) := by field_simp; ring
    simp only [g1, chi_inv, this, map_mul, quadraticChar_sq_one' (inv_ne_zero hx), one_mul]

lemma g1_tau (hp : p % 4 = 1) (x : ZMod p) : g1 (tau x) = g1 x := by
  unfold tau rho
  split_ifs
  · exact g1_inv x
  · rw [g1_neg hp, g1_inv]

lemma tau_mem (hp : p % 4 = 1) {x : ZMod p} (hx : x ∈ P) : tau x ∈ P :=
  rho_mem hp (inv_ne_zero (ne_zero_of_mem_P hx))

lemma tau_tau (hp : p % 4 = 1) {x : ZMod p} (hx : x ∈ P) : tau (tau x) = x := by
  have hx0 := ne_zero_of_mem_P hx
  unfold tau rho
  by_cases hy : x⁻¹ ∈ P
  · simp [hy, hx]
  · have : -x ∉ P := (neg_mem_P_iff hp hx0).not.mpr (not_not.mpr hx)
    simp [hy, this]

lemma tau_ne (hp : p % 4 = 1) {x : ZMod p} (hx : x ∈ P) (h1 : x ≠ 1) (h2 : x ^ 2 ≠ -1) :
    tau x ≠ x := by
  have hx0 := ne_zero_of_mem_P hx
  intro h
  unfold tau rho at h
  split_ifs at h with hy
  · apply h1
    have : x ^ 2 = 1 ^ 2 := by
      have : x * x = 1 := by
        have h3 : x⁻¹ * x = 1 := inv_mul_cancel₀ hx0
        rwa [h] at h3
      rw [sq, one_pow, this]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp this with h | h
    · exact h
    · exfalso
      have := (neg_mem_P_iff hp (one_ne_zero (α := ZMod p))).mp (h ▸ hx)
      exact this one_mem_P
  · apply h2
    have : x * x = -1 := by
      have : x * (-x⁻¹) = -1 := by field_simp
      rw [h] at this
      exact this
    rw [sq, this]

lemma exists_sq_neg_one_mem_P (hp : p % 4 = 1) : ∃ i ∈ (P : Finset (ZMod p)), i ^ 2 = -1 := by
  obtain ⟨y, hy⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (show p % 4 ≠ 3 by omega)
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  by_cases h : y ∈ P
  · exact ⟨y, h, by rw [sq]; exact hy.symm⟩
  · exact ⟨-y, (neg_mem_P_iff hp hy0).mpr h, by rw [neg_sq, sq]; exact hy.symm⟩

lemma legendre_two (hp : p % 4 = 1) :
    χ (2 : ZMod p) = if p % 8 = 1 then 1 else -1 := by
  have hp2 : p ≠ 2 := by omega
  have h := legendreSym.at_two (p := p) hp2
  have h2 : χ (2 : ZMod p) = legendreSym p 2 := by simp [legendreSym]
  rw [h2, h, ZMod.χ₈_nat_eq_if_mod_eight]
  have : p % 8 = 1 ∨ p % 8 = 5 := by omega
  rcases this with h | h <;> simp [h] <;> omega

lemma H_mod_four (hp : p % 4 = 1) : ∑ x ∈ (P : Finset (ZMod p)), g1 x ≡ 3 [ZMOD 4] := by
  classical
  obtain ⟨i0, hi0P, hi0⟩ := exists_sq_neg_one_mem_P hp
  have hne : (1 : ZMod p) ≠ i0 := by
    intro h
    rw [← h] at hi0
    exact neg_ne_self hp (one_ne_zero (α := ZMod p)) (by rw [← hi0]; ring)
  set Q : Finset (ZMod p) := P.filter (fun x => ¬ (x ≠ 1 ∧ x ^ 2 ≠ -1)) with hQdef
  set s : Finset (ZMod p) := P.filter (fun x => x ≠ 1 ∧ x ^ 2 ≠ -1) with hsdef
  have hQ : Q = {1, i0} := by
    ext x
    simp only [hQdef, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hx'⟩
      have hx'' : x ≠ 1 → x ^ 2 = -1 := fun h => by
        by_contra h'
        exact hx' ⟨h, h'⟩
      by_cases h1 : x = 1
      · exact Or.inl h1
      · right
        have h2 := hx'' h1
        have : x ^ 2 = i0 ^ 2 := by rw [h2, hi0]
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp this with h | h
        · exact h
        · exfalso
          have := (neg_mem_P_iff hp (ne_zero_of_mem_P hi0P)).mp (h ▸ hx)
          exact this hi0P
    · rintro (rfl | rfl)
      · exact ⟨one_mem_P, by simp⟩
      · exact ⟨hi0P, by rintro ⟨_, h⟩; exact h hi0⟩
  have hcardQ : Q.card = 2 := by rw [hQ, Finset.card_pair hne]
  have hsplit : ∑ x ∈ P, g1 x = ∑ x ∈ s, g1 x + ∑ x ∈ Q, g1 x :=
    (Finset.sum_filter_add_sum_filter_not P _ _).symm
  have hsumQ : ∑ x ∈ Q, g1 x = χ (2 : ZMod p) := by
    rw [hQ, Finset.sum_pair hne]
    have h1 : g1 (1 : ZMod p) = χ 2 := by
      simp only [g1, map_one, one_mul, one_pow]
      norm_num [one_add_one_eq_two]
    have h2 : g1 i0 = 0 := by simp [g1, hi0]
    rw [h1, h2, add_zero]
  have hcards : s.card + 2 = (P : Finset (ZMod p)).card := by
    have := Finset.card_filter_add_card_filter_not (s := (P : Finset (ZMod p)))
      (fun x => x ≠ 1 ∧ x ^ 2 ≠ -1)
    have h3 := hcardQ
    rw [hQdef] at h3
    rw [hsdef]
    omega
  have hsum : ∑ x ∈ s, g1 x ≡ (s.card : ℤ) [ZMOD 4] := by
    apply sum_sign_involution s tau g1
    · intro x hx
      rw [hsdef, Finset.mem_filter] at hx
      obtain ⟨hx1, hx2, hx3⟩ := hx
      rw [hsdef, Finset.mem_filter]
      refine ⟨tau_mem hp hx1, ?_, ?_⟩
      · intro h
        apply hx2
        have h' := tau_tau hp hx1
        rw [h] at h'
        rw [← h']
        unfold tau rho
        simp [one_mem_P]
      · intro h
        apply hx3
        have hx0 := ne_zero_of_mem_P hx1
        have : (tau x) ^ 2 = (x⁻¹) ^ 2 := by
          unfold tau rho
          split_ifs <;> simp
        rw [this] at h
        have h4 : x ^ 2 * (x⁻¹) ^ 2 = 1 := by field_simp
        rw [h] at h4
        linear_combination -h4
    · intro x hx
      rw [hsdef] at hx
      exact tau_tau hp (Finset.mem_filter.mp hx).1
    · intro x hx
      rw [hsdef, Finset.mem_filter] at hx
      exact tau_ne hp hx.1 hx.2.1 hx.2.2
    · intro x _
      exact g1_tau hp x
    · intro x hx
      rw [hsdef, Finset.mem_filter] at hx
      obtain ⟨hx1, hx2, hx3⟩ := hx
      have hx0 := ne_zero_of_mem_P hx1
      have hy : x ^ 2 + 1 ≠ 0 := fun h => hx3 (by linear_combination h)
      unfold g1
      rcases quadraticChar_dichotomy hx0 with h | h <;>
        rcases quadraticChar_dichotomy hy with h' | h' <;> simp [h, h']
  have hc := legendre_two hp
  have hcP := card_P (p := p) hp
  rw [hsplit, hsumQ]
  unfold Int.ModEq at hsum ⊢
  have := (Fact.out : p.Prime).two_le
  split_ifs at hc <;> omega

/-- Euler's criterion for the quadratic character, valid also at $0$. -/
lemma chi_cast_eq_pow (y : ZMod p) : ((χ y : ℤ) : ZMod p) = y ^ (p / 2) := by
  have h := legendreSym.eq_pow p (y.val : ℤ)
  simpa [legendreSym] using h

lemma sum_pow_eq (hp : p % 4 = 1) (n : ℕ) (hn : p = 4 * n + 1) (j : ℕ) (hj : j ≤ 2 * n) :
    ∑ x : ZMod p, x ^ (2 * n + 2 * j) = if j = n then -1 else 0 := by
  have hcard : p - 1 = 4 * n := by omega
  have hnpos : 0 < n := by have := (Fact.out : p.Prime).two_le; omega
  have hlt : ∀ e, e < 4 * n → ∑ x : ZMod p, x ^ e = 0 := by
    intro e he
    have := FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) e (by rw [ZMod.card]; omega)
    exact this
  split_ifs with h
  · subst h
    have : ∀ x : ZMod p, x ^ (2 * j + 2 * j) = 1 - if x = 0 then 1 else 0 := by
      intro x
      by_cases hx : x = 0
      · subst hx
        rw [zero_pow (by omega)]
        simp
      · have := ZMod.pow_card_sub_one_eq_one hx
        rw [hcard] at this
        rw [show 2 * j + 2 * j = 4 * j by ring, this]
        simp [hx]
    simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Finset.sum_const, Finset.card_univ, ZMod.card]
    simp
  · rcases lt_or_gt_of_ne h with h | h
    · exact hlt _ (by omega)
    · have : ∀ x : ZMod p, x ^ (2 * n + 2 * j) = x ^ (2 * (j - n)) := by
        intro x
        by_cases hx : x = 0
        · subst hx
          have h1 : 2 * n + 2 * j ≠ 0 := by omega
          have h2 : 2 * (j - n) ≠ 0 := by omega
          rw [zero_pow h1, zero_pow h2]
        · have := ZMod.pow_card_sub_one_eq_one hx
          rw [hcard] at this
          rw [show 2 * n + 2 * j = 4 * n + 2 * (j - n) by omega, pow_add, this, one_mul]
      simp only [this]
      exact hlt _ (by omega)

/-- $S(1) \equiv -\binom{2k}{k} \pmod p$, where $p = 4k+1$. -/
lemma S_one_cast (hp : p % 4 = 1) (n : ℕ) (hn : p = 4 * n + 1) :
    ((S (1 : ZMod p) : ℤ) : ZMod p) = -((2 * n).choose n : ZMod p) := by
  have hp2 : p / 2 = 2 * n := by omega
  have h1 : ((S (1 : ZMod p) : ℤ) : ZMod p) = ∑ x : ZMod p, x ^ (2 * n) * (x ^ 2 + 1) ^ (2 * n) := by
    unfold S
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [chi_cast_eq_pow, chi_cast_eq_pow, hp2]
  have h2 : ∀ x : ZMod p, x ^ (2 * n) * (x ^ 2 + 1) ^ (2 * n) =
      ∑ j ∈ Finset.range (2 * n + 1), ((2 * n).choose j : ZMod p) * x ^ (2 * n + 2 * j) := by
    intro x
    rw [add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [one_pow, mul_one, ← pow_mul, pow_add]
    ring
  rw [h1]
  simp only [h2]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  rw [Finset.sum_eq_single n]
  · rw [sum_pow_eq hp n hn n (by omega)]; simp
  · intro j hj hjn
    rw [sum_pow_eq hp n hn j (by have := Finset.mem_range.mp hj; omega)]
    simp [hjn]
  · intro h
    exfalso
    exact h (Finset.mem_range.mpr (by omega))

lemma ne_zero_of_prime_sq_add {p : ℕ} (hp : p.Prime) {a b : ℤ} (h : (p : ℤ) = a ^ 2 + b ^ 2) :
    b ≠ 0 := by
  rintro rfl
  have h1 : p = a.natAbs ^ 2 := by
    have : (p : ℤ) = (a.natAbs : ℤ) ^ 2 := by rw [Int.natAbs_sq]; simpa using h
    exact_mod_cast this
  rw [h1] at hp
  exact not_prime_pow (by norm_num) (Nat.prime_iff.mp hp)

lemma natAbs_eq_of_two_sq {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) {a b c d : ℤ}
    (hab : (p : ℤ) = a ^ 2 + b ^ 2) (hcd : (p : ℤ) = c ^ 2 + d ^ 2) (ha : Odd a) (hc : Odd c) :
    a.natAbs = c.natAbs := by
  have key : ∀ {a b : ℤ}, (p : ℤ) = a ^ 2 + b ^ 2 → Odd a →
      (0 < a.natAbs ∧ 0 < b.natAbs ∧ Odd a.natAbs ∧ Even b.natAbs ∧
        p = a.natAbs ^ 2 + b.natAbs ^ 2) := by
    intro a b hab ha
    have hb0 := ne_zero_of_prime_sq_add hp hab
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    have hbe : Even b := by
      rcases Int.even_or_odd b with h | h
      · exact h
      · exfalso
        have h1 := Int.sq_emod_four_eq_one_of_odd ha
        have h2 := Int.sq_emod_four_eq_one_of_odd h
        omega
    refine ⟨Int.natAbs_pos.mpr ha0, Int.natAbs_pos.mpr hb0, Int.natAbs_odd.mpr ha,
      Int.natAbs_even.mpr hbe, ?_⟩
    have : (p : ℤ) = (a.natAbs : ℤ) ^ 2 + (b.natAbs : ℤ) ^ 2 := by
      rw [Int.natAbs_sq, Int.natAbs_sq]; exact hab
    exact_mod_cast this
  obtain ⟨xy, -, huniq⟩ := corollary21 p hp hp4
  obtain ⟨h1, h2, h3, h4, h5⟩ := key hab ha
  obtain ⟨g1, g2, g3, g4, g5⟩ := key hcd hc
  have e1 := huniq (a.natAbs, b.natAbs) ⟨h1, h2, h3, h4, h5⟩
  have e2 := huniq (c.natAbs, d.natAbs) ⟨g1, g2, g3, g4, g5⟩
  have := congrArg Prod.fst (e1.trans e2.symm)
  exact this

/-- The integers $H, H'$ with $S(1) = 2H$, $S(r) = 2H'$, $H^2 + H'^2 = p$, $H \equiv 3 \pmod 4$. -/
lemma exists_H (hp : p % 4 = 1) :
    ∃ H H' : ℤ, 2 * H = S (1 : ZMod p) ∧ H = ∑ x ∈ (P : Finset (ZMod p)), g1 x ∧
      (p : ℤ) = H ^ 2 + H' ^ 2 ∧ H ≡ 3 [ZMOD 4] := by
  obtain ⟨r, hr⟩ := exists_nonsquare hp
  refine ⟨∑ x ∈ (P : Finset (ZMod p)), g1 x, (∑ x ∈ (P : Finset (ZMod p)), χ x * χ (x ^ 2 + r)),
    (S_eq_two_mul_half hp 1).symm, rfl, ?_, H_mod_four hp⟩
  have h1 := S_eq_two_mul_half hp (1 : ZMod p)
  have h2 := S_eq_two_mul_half hp r
  have h3 := S_one_sq_add hp hr
  rw [h1, h2] at h3
  have : (4 : ℤ) * ((∑ x ∈ (P : Finset (ZMod p)), g1 x) ^ 2 +
      (∑ x ∈ (P : Finset (ZMod p)), χ x * χ (x ^ 2 + r)) ^ 2) = 4 * p := by
    rw [← h3]; unfold g1; ring
  linarith

/-- The core of Theorems 8.2 and 8.3: $a = -H$ with $H$ half the Jacobsthal sum $S(1)$. -/
lemma a_eq_neg_H (hp : p % 4 = 1) {a b : ℤ} (hab : (p : ℤ) = a ^ 2 + b ^ 2) (ha : a ≡ 1 [ZMOD 4]) :
    ∃ H : ℤ, 2 * H = S (1 : ZMod p) ∧ H = ∑ x ∈ (P : Finset (ZMod p)), g1 x ∧ a = -H := by
  obtain ⟨H, H', h2H, hH, hpH, hH4⟩ := exists_H (p := p) hp
  have hpp := (Fact.out : p.Prime)
  have hHodd : Odd H := Int.odd_iff.mpr (by unfold Int.ModEq at hH4; omega)
  have haodd : Odd a := Int.odd_iff.mpr (by unfold Int.ModEq at ha; omega)
  have hn := natAbs_eq_of_two_sq hpp hp hab hpH haodd hHodd
  rcases Int.natAbs_eq_natAbs_iff.mp hn with h | h
  · exfalso
    unfold Int.ModEq at ha hH4
    omega
  · exact ⟨H, h2H, hH, h⟩

end Basic

end Jacobsthal

/-- **Moreno–Wagstaff, Theorem 8.3** (Jacobsthal 1907; §8.2, p. 322). **Proved, unconditional.**

For a prime $p = 4k+1$ written $p = a^2 + b^2$ with $a \equiv 1 \pmod 4$,
$a = -\sum_{j=1}^{(p-1)/2} \left(\frac{j}{p}\right)\left(\frac{j^2+1}{p}\right)$.

*Proof.* With $S(k) = \sum_{x \in \mathbb{F}_p} \chi(x)\chi(x^2+k)$ one shows $S(1) = 2H$ with $H$ the sum
above, $S(1)^2 + S(r)^2 = 4p$ for a nonsquare $r$ (second moment of $S$), $S(r)$ even, and $H \equiv 3 \pmod 4$
(pairing $j \leftrightarrow \pm j^{-1}$). Uniqueness of the two-squares representation
(`corollary21`) gives $|a| = |H|$ and the congruence mod $4$ fixes the sign. -/
theorem theorem83 : Theorem83 := by
  intro p _ a b hp hab ha
  obtain ⟨H, -, hH, haH⟩ := Jacobsthal.a_eq_neg_H (p := p) hp hab ha
  rw [Jacobsthal.Icc_sum_eq hp, haH, hH]
  rfl

/-- **Moreno–Wagstaff, Theorem 8.2** (Gauss; §8.2, p. 322). **Proved, unconditional.**

For a prime $p = 4k+1 = a^2 + b^2$ with $a \equiv 1 \pmod 4$: $2a \equiv \binom{2k}{k} \pmod p$ and
$2|a| < p$.

*Proof.* By `theorem83`'s core, $2a = -S(1)$. By Euler's criterion $\chi(y) \equiv y^{2k}$, so
$S(1) \equiv \sum_x x^{2k}(x^2+1)^{2k} = \sum_j \binom{2k}{j}\sum_x x^{2k+2j} \equiv -\binom{2k}{k}$ since
$\sum_x x^e$ vanishes for $0 < e < p-1$ or $p - 1 < e < 2(p-1)$ and equals $-1$ for $e = p-1$.
The bound holds as $a^2 < a^2 + b^2 = p$ ($b \neq 0$) and $p \ge 5$. -/
theorem theorem82 : Theorem82 := by
  intro p a b hp hp4 hab ha
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨H, h2H, -, haH⟩ := Jacobsthal.a_eq_neg_H (p := p) hp4 hab ha
  have h2 := hp.two_le
  set n := (p - 1) / 4 with hn
  have hpn : p = 4 * n + 1 := by omega
  constructor
  · rw [← ZMod.intCast_eq_intCast_iff]
    have h1 := Jacobsthal.S_one_cast hp4 n hpn
    have h3 : (2 * a : ℤ) = -(Jacobsthal.S (1 : ZMod p)) := by rw [← h2H, haH]; ring
    rw [h3]
    push_cast
    rw [h1]
    simp
  · have hb : 0 < b ^ 2 := by
      have := Jacobsthal.ne_zero_of_prime_sq_add hp hab
      positivity
    by_contra hcon
    have hle : (p : ℤ) ≤ 2 * |a| := not_lt.mp hcon
    have h4 : (p : ℤ) ^ 2 ≤ (2 * |a|) ^ 2 := pow_le_pow_left₀ (by positivity) hle 2
    have h5 : |a| ^ 2 = a ^ 2 := sq_abs a
    have h6 : (5 : ℤ) ≤ p := by omega
    nlinarith

end QuadFormsKB.MorenoWagstaff
