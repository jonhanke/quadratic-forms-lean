/-
# Kitaoka 1993, Theorem 3.4.2: the Hasse invariant of orthogonal sums, tensor products and scalings

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §3.4, definition of $S(U)$, p. 57, and Theorem 3.4.2,
p. 59 (printed pages).

**Setting.** $F$ is a local field ($\mathbb Q_p$ or $\mathbb R$) and $(\ ,\ )_F$ the Hilbert symbol
(`hilbertSymbol F`). A regular quadratic space $U$ over $F$ has an orthogonal basis, $U \cong \langle a_1\rangle \perp
\dots \perp \langle a_u\rangle$ with $a_i \in F^\times$, and Kitaoka defines $S(U) = \prod_{i \le j}(a_i, a_j)_F$ (with
$\le$, not $<$; Theorem 3.4.1 shows it does not depend on the basis) and $dU = \prod_i a_i$ (modulo squares, which the
Hilbert symbol does not see). Here a diagonal space is given by its coefficient family $a : \iota \to F$ over a finite
linearly ordered index set $\iota$ (`Fin u` for $\langle a_0\rangle \perp \dots \perp \langle a_{u-1}\rangle$), and
`hasseK a` $= \prod_{i \le j}(a_i, a_j)_F$, `discK a` $= \prod_i a_i$.
* $U \perp V$ for $U = \langle a_i\rangle$, $V = \langle b_j\rangle$ is the family on the ordered disjoint union
  $\iota \oplus_{\mathrm{lex}} \kappa$ (all of $\iota$ before $\kappa$): `Sum.elim a b`.
* $U \otimes V$ has the orthogonal basis $u_i \otimes v_j$ with $Q(u_i \otimes v_j) = a_ib_j$, indexed by
  $\iota \times_{\mathrm{lex}} \kappa$ (`tensorK a b`).
* $\langle a\rangle \otimes V$ is $\langle ab_j\rangle_j$.

**Proves** (unconditional, for $F = \mathbb Q_p$ and $F = \mathbb R$; the algebra is done for every field of
characteristic $0$ whose Hilbert symbol is bimultiplicative)
* `theorem342_sum_padic`, `theorem342_sum_real`: $S(U \perp V) = S(U)S(V)(dU, dV)_F$;
* `theorem342_tensor_padic`, `theorem342_tensor_real`:
  $S(U \otimes V) = S(U)^vS(V)^u(dU, dV)_F^{uv+1}(dU, -1)_F^{v(v-1)/2}(dV, -1)_F^{u(u-1)/2}$;
* `theorem342_scalar_padic`, `theorem342_scalar_real`:
  $S(\langle a\rangle \otimes V) = (a, -1)_F^{v(v+1)/2}(a, dV)_F^{v+1}S(V)$.

**Proof.** The sum formula splits $\prod_{i \le j}$ into the pairs inside $U$, inside $V$, and across (Kitaoka).
The scalar formula expands $(ab_i, ab_j) = (a, a)(a, b_j)(b_i, a)(b_i, b_j)$ and counts: there are $v(v+1)/2$ pairs
$i \le j$, and each index occurs in $v + 1$ of them. The tensor formula is computed directly (Kitaoka argues by
induction on $u$): pairs $(i, j) \le (k, l)$ in the lexicographic order have $i < k$, or $i = k$ and $j \le l$; the
first kind contribute $(a_i^v dV, a_k^v dV)$, the second kind $S(\langle a_i\rangle \otimes V)$.
-/
import QuadFormsKB.Equiv.Hilbert
import QuadFormsKB.Literature.Cassels.Ch3.ExerciseTen
import Mathlib.Order.Sum.Order
import Mathlib.Order.Prod.Lex.Basic

open Finset

noncomputable section

namespace QuadFormsKB.Kitaoka.Hasse

/-! ### Definitions -/

section Defs

variable {K : Type*} [Field K]

/-- Kitaoka's Hasse invariant $S(U) = \prod_{i \le j}(a_i, a_j)_F$ of the diagonal space
$U = \perp_i \langle a_i\rangle$, $i$ running over a finite linearly ordered set (Kitaoka 1993, §3.4, p. 57). -/
@[kb "kitaoka1993" "§3.4, p. 57 (S(U))"]
def hasseK {ι : Type*} [Fintype ι] [LinearOrder ι] (a : ι → K) : ℤ :=
  ∏ i, ∏ j, if i ≤ j then hilbertSymbol K (a i) (a j) else 1

/-- The discriminant $dU = \prod_i a_i$ of the diagonal space $\perp_i \langle a_i\rangle$. -/
def discK {ι : Type*} [Fintype ι] (a : ι → K) : K := ∏ i, a i

/-- The diagonal coefficients $a_ib_j$ of $U \otimes V$ for $U = \perp_i\langle a_i\rangle$,
$V = \perp_j \langle b_j\rangle$, indexed lexicographically by $(i, j)$. -/
def tensorK {ι κ : Type*} (a : ι → K) (b : κ → K) : ι ×ₗ κ → K := fun p => a (ofLex p).1 * b (ofLex p).2

/-- The Hilbert symbol of $K$ is bimultiplicative on $K^\times$. Holds for $\mathbb Q_p$ and $\mathbb R$. -/
def HilbertBimult (K : Type*) [Field K] : Prop :=
  ∀ a b c : K, a ≠ 0 → b ≠ 0 → c ≠ 0 →
    hilbertSymbol K a (b * c) = hilbertSymbol K a b * hilbertSymbol K a c

end Defs

/-! ### Signs and counting -/

section Signs

theorem pm_pow_eq {x : ℤ} (h : x = 1 ∨ x = -1) {m n : ℕ} (hmn : m % 2 = n % 2) : x ^ m = x ^ n := by
  rcases h with rfl | rfl
  · simp
  · rw [neg_one_pow_eq_pow_mod_two, hmn, ← neg_one_pow_eq_pow_mod_two]

theorem pm_mul {x y : ℤ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) : x * y = 1 ∨ x * y = -1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp

theorem pm_prod {ι : Type*} (s : Finset ι) (f : ι → ℤ) (hf : ∀ i, f i = 1 ∨ f i = -1) :
    (∏ i ∈ s, f i) = 1 ∨ (∏ i ∈ s, f i) = -1 :=
  Finset.prod_induction _ (fun x : ℤ => x = 1 ∨ x = -1) (fun _ _ => pm_mul) (Or.inl rfl) fun i _ => hf i

theorem pm_mul_self {x : ℤ} (h : x = 1 ∨ x = -1) : x * x = 1 := by rcases h with rfl | rfl <;> norm_num

/-- $\frac{v(v+1)}{2} \cdot 2 = v^2 + v$. -/
theorem tri (v : ℕ) : v * (v + 1) / 2 * 2 = v * v + v := by
  rw [Nat.div_mul_cancel (Nat.even_mul_succ_self v).two_dvd]
  ring

/-- $\frac{v(v-1)}{2} + v = \frac{v(v+1)}{2}$. -/
theorem tri' (v : ℕ) : v * (v - 1) / 2 + v = v * (v + 1) / 2 := by
  rcases v with _ | w
  · simp
  · simp only [Nat.add_sub_cancel]
    rw [show (w + 1) * (w + 1 + 1) = (w + 1) * w + 2 * (w + 1) by ring, Nat.add_mul_div_left _ _ two_pos]

theorem ite_eq_pow {M : Type*} [Monoid M] (P : Prop) [Decidable P] (c : M) :
    (if P then c else 1) = c ^ (if P then 1 else 0) := by
  split_ifs <;> simp

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

omit [LinearOrder ι] in
/-- $\prod_{i, j}[P(i, j)]\,c = c^{\#\{(i, j) : P(i, j)\}}$. -/
theorem prod_prod_ite_const {M : Type*} [CommMonoid M] (P : ι → ι → Prop) [∀ i j, Decidable (P i j)] (c : M) :
    (∏ i, ∏ j, if P i j then c else 1) = c ^ (∑ i, ∑ j, if P i j then 1 else 0) := by
  simp_rw [ite_eq_pow, Finset.prod_pow_eq_pow_sum]

/-- $2\,\#\{(i, j) : i \le j\} = n^2 + n$. -/
theorem cnt_le_two (n : ℕ) (hn : Fintype.card ι = n) :
    (∑ i : ι, ∑ j : ι, if i ≤ j then 1 else 0) * 2 = n * n + n := by
  have hswap : (∑ i : ι, ∑ j : ι, if i ≤ j then 1 else 0) = ∑ i : ι, ∑ j : ι, if j ≤ i then 1 else 0 :=
    Finset.sum_comm
  have hsum : (∑ i : ι, ∑ j : ι, if i ≤ j then 1 else 0) + (∑ i : ι, ∑ j : ι, if j ≤ i then 1 else 0) =
      ∑ i : ι, ∑ j : ι, ((1 : ℕ) + if i = j then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h.le, h.not_ge, h.ne]
    · simp
    · simp [h.le, h.not_ge, h.ne']
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib] at hsum
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true] at hsum
  rw [hn] at hsum
  omega

/-- $\#\{(i, j) : i \le j\} = \#\{(i, j) : i < j\} + n$. -/
theorem cnt_le_eq (n : ℕ) (hn : Fintype.card ι = n) :
    (∑ i : ι, ∑ j : ι, if i ≤ j then 1 else 0) = (∑ i : ι, ∑ j : ι, if i < j then 1 else 0) + n := by
  have : ∀ i : ι, (∑ j : ι, if i ≤ j then 1 else 0) = (∑ j : ι, if i < j then 1 else 0) + 1 := by
    intro i
    have : ∀ j : ι, (if i ≤ j then 1 else 0) = (if i < j then 1 else 0) + (if i = j then 1 else 0) := by
      intro j
      rcases lt_trichotomy i j with h | rfl | h
      · simp [h.le, h, h.ne]
      · simp
      · simp [h.not_ge, h.not_gt, h.ne']
    rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_add_distrib]
    simp
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib]
  simp [hn]

/-- Each index $k$ lies in $n + 1$ of the pairs $i \le j$ (as $i$ or as $j$, counted twice when $i = j = k$). -/
theorem cnt_point (n : ℕ) (hn : Fintype.card ι = n) (k : ι) :
    (∑ i : ι, if i ≤ k then 1 else 0) + (∑ j : ι, if k ≤ j then 1 else 0) = n + 1 := by
  rw [← Finset.sum_add_distrib]
  have : ∀ i : ι, ((if i ≤ k then 1 else 0) + if k ≤ i then 1 else 0) = 1 + (if i = k then 1 else 0) := by
    intro i
    rcases lt_trichotomy i k with h | rfl | h
    · simp [h.le, h.not_ge, h.ne]
    · simp
    · simp [h.le, h.not_ge, h.ne']
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib]
  simp [hn]

/-- Each index $k$ lies in $n - 1$ of the pairs $i < j$. -/
theorem cnt_point_lt (n : ℕ) (hn : Fintype.card ι = n) (k : ι) :
    (∑ i : ι, if i < k then 1 else 0) + (∑ j : ι, if k < j then 1 else 0) + 1 = n := by
  rw [← Finset.sum_add_distrib]
  have : ∀ i : ι, ((if i < k then 1 else 0) + if k < i then 1 else 0) = 1 - (if i = k then 1 else 0) := by
    intro i
    rcases lt_trichotomy i k with h | rfl | h
    · simp [h, h.not_gt, h.ne]
    · simp
    · simp [h, h.not_gt, h.ne']
  have hsplit : (∑ i : ι, (1 - if i = k then 1 else 0)) + 1 = ∑ i : ι, (1 : ℕ) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k), ← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
    simp only [ite_true, tsub_self, add_zero]
    rw [Finset.sum_congr rfl fun i hi => by rw [if_neg (Finset.ne_of_mem_erase hi)]]
  rw [Finset.sum_congr rfl fun i _ => this i, hsplit]
  simp [hn]

end Signs

/-! ### Hilbert-symbol algebra under bimultiplicativity -/

section Algebra

variable {K : Type*} [Field K] (hB : HilbertBimult K)
include hB

local notation "hs" => hilbertSymbol K

omit hB in
theorem hs_pm (a b : K) : hs a b = 1 ∨ hs a b = -1 := by
  unfold hilbertSymbol
  split_ifs <;> simp

theorem hs_mul_left {a b c : K} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    hs (a * b) c = hs a c * hs b c := by
  rw [hilbertSymbol_comm, hB _ _ _ hc ha hb, hilbertSymbol_comm K c, hilbertSymbol_comm K c]

theorem hs_prod_right {α : Type*} (s : Finset α) {a : K} (ha : a ≠ 0) (b : α → K) (hb : ∀ i, b i ≠ 0) :
    hs a (∏ i ∈ s, b i) = ∏ i ∈ s, hs a (b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hilbertSymbol_one_right]
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, hB _ _ _ ha (hb j)
      (Finset.prod_ne_zero_iff.mpr fun i _ => hb i), ih]

theorem hs_prod_left {α : Type*} (s : Finset α) (a : α → K) (ha : ∀ i, a i ≠ 0) {b : K} (hb : b ≠ 0) :
    hs (∏ i ∈ s, a i) b = ∏ i ∈ s, hs (a i) b := by
  rw [hilbertSymbol_comm, hs_prod_right hB s hb a ha]
  exact Finset.prod_congr rfl fun i _ => hilbertSymbol_comm K b (a i)

theorem hs_pow_left {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) (n : ℕ) : hs (a ^ n) b = hs a b ^ n := by
  have := hs_prod_left hB (Finset.range n) (fun _ => a) (fun _ => ha) hb
  simpa using this

theorem hs_self {a : K} (ha : a ≠ 0) : hs a a = hs a (-1) := by
  have h := hilbertSymbol_self_neg K a
  rw [show -a = -1 * a by ring, hB _ _ _ ha (by norm_num) ha] at h
  rcases hs_pm a (-1 : K) with h1 | h1 <;> rw [h1] at h ⊢ <;> linarith

/-- $\prod_{i, j}(x_i, y_j) = (\prod_i x_i, \prod_j y_j)$. -/
theorem prod_prod_hs {α β : Type*} [Fintype α] [Fintype β] (x : α → K) (y : β → K) (hx : ∀ i, x i ≠ 0)
    (hy : ∀ j, y j ≠ 0) : ∏ i, ∏ j, hs (x i) (y j) = hs (∏ i, x i) (∏ j, y j) := by
  rw [hs_prod_left hB _ x hx (Finset.prod_ne_zero_iff.mpr fun j _ => hy j)]
  exact Finset.prod_congr rfl fun i _ => (hs_prod_right hB _ (hx i) y hy).symm

omit hB in
theorem hasseK_pm {ι : Type*} [Fintype ι] [LinearOrder ι] (a : ι → K) : hasseK a = 1 ∨ hasseK a = -1 :=
  pm_prod _ _ fun i => pm_prod _ _ fun j => by split_ifs; exacts [hs_pm _ _, Or.inl rfl]

/-- $S(U) = \prod_{i < j}(a_i, a_j) \cdot (dU, -1)$. -/
theorem hasseK_eq_lt {ι : Type*} [Fintype ι] [LinearOrder ι] (a : ι → K) (ha : ∀ i, a i ≠ 0) :
    hasseK a = (∏ i, ∏ j, if i < j then hs (a i) (a j) else 1) * hs (discK a) (-1) := by
  unfold hasseK discK
  rw [hs_prod_left hB _ a ha (by norm_num), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have : ∀ j, (if i ≤ j then hs (a i) (a j) else 1) =
      (if i < j then hs (a i) (a j) else 1) * (if i = j then hs (a i) (-1) else 1) := by
    intro j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h.le, h, h.ne]
    · simp [hs_self hB (ha i)]
    · simp [h.not_ge, h.not_gt, h.ne']
  rw [Finset.prod_congr rfl fun j _ => this j, Finset.prod_mul_distrib]
  simp

/-! #### The sum formula -/

/-- **Sum formula** (general form): $S(U \perp V) = S(U)S(V)(dU, dV)$. -/
theorem hasseK_sum {ι κ : Type*} [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ] (a : ι → K) (b : κ → K)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0) :
    hasseK (fun s : ι ⊕ₗ κ => Sum.elim a b (ofLex s)) = hasseK a * hasseK b * hs (discK a) (discK b) := by
  unfold hasseK
  have hL : ∀ (f : ι ⊕ₗ κ → ℤ), ∏ s : ι ⊕ₗ κ, f s = (∏ i, f (toLex (Sum.inl i))) * ∏ j, f (toLex (Sum.inr j)) :=
    fun f => (Fintype.prod_equiv toLex _ f fun _ => rfl).symm.trans (Fintype.prod_sum_type _)
  rw [hL]
  simp_rw [hL]
  simp only [ofLex_toLex, Sum.elim_inl, Sum.elim_inr, Sum.Lex.inl_le_inl_iff, Sum.Lex.inr_le_inr_iff,
    Sum.Lex.inl_le_inr, Sum.Lex.not_inr_le_inl, ite_true, ite_false, Finset.prod_const_one, mul_one,
    Finset.prod_mul_distrib]
  rw [prod_prod_hs hB a b ha hb]
  unfold discK
  ring

/-! #### The scalar formula -/

/-- **Scalar formula** (general form): $S(\langle c\rangle \otimes V) = (c, -1)^{v(v+1)/2}(c, dV)^{v+1}S(V)$. -/
theorem hasseK_scalar {κ : Type*} [Fintype κ] [LinearOrder κ] {c : K} (hc : c ≠ 0) (b : κ → K)
    (hb : ∀ j, b j ≠ 0) :
    hasseK (fun j => c * b j) = hs c (-1) ^ (Fintype.card κ * (Fintype.card κ + 1) / 2) *
      hs c (discK b) ^ (Fintype.card κ + 1) * hasseK b := by
  set v := Fintype.card κ with hv
  have hterm : ∀ i j, hs (c * b i) (c * b j) = hs c (-1) * hs c (b j) * hs c (b i) * hs (b i) (b j) := by
    intro i j
    rw [hs_mul_left hB hc (hb i) (mul_ne_zero hc (hb j)), hB _ _ _ hc hc (hb j),
      hB _ _ _ (hb i) hc (hb j), hs_self hB hc, hilbertSymbol_comm K (b i) c]
    ring
  have hsplit : ∀ i j, (if i ≤ j then hs (c * b i) (c * b j) else 1) =
      (if i ≤ j then hs c (-1) else 1) * (if i ≤ j then hs c (b j) else 1) *
        (if i ≤ j then hs c (b i) else 1) * (if i ≤ j then hs (b i) (b j) else 1) := by
    intro i j
    split_ifs
    · exact hterm i j
    · simp
  unfold hasseK
  simp_rw [hsplit, Finset.prod_mul_distrib]
  rw [prod_prod_ite_const]
  -- the middle factors
  have hmid : (∏ i : κ, ∏ j : κ, if i ≤ j then hs c (b j) else 1) *
      (∏ i : κ, ∏ j : κ, if i ≤ j then hs c (b i) else 1) = hs c (discK b) ^ (v + 1) := by
    rw [Finset.prod_comm (f := fun i j => if i ≤ j then hs c (b j) else 1)]
    simp_rw [ite_eq_pow, Finset.prod_pow_eq_pow_sum]
    rw [← Finset.prod_mul_distrib]
    simp_rw [← pow_add]
    rw [Finset.prod_congr rfl fun k _ => by rw [cnt_point v hv.symm k]]
    unfold discK
    rw [hs_prod_right hB _ hc b hb, Finset.prod_pow]
  have hN : (∑ i : κ, ∑ j : κ, if i ≤ j then 1 else 0) = v * (v + 1) / 2 := by
    have := cnt_le_two v hv.symm
    rw [show v * (v + 1) = v * v + v by ring]
    omega
  rw [hN, mul_assoc (hs c (-1) ^ _), hmid]

/-! #### The tensor formula -/

/-- **Tensor formula** (general form): $S(U \otimes V) = S(U)^vS(V)^u(dU, dV)^{uv+1}(dU, -1)^{v(v-1)/2}
(dV, -1)^{u(u-1)/2}$. -/
theorem hasseK_tensor {ι κ : Type*} [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ] (a : ι → K) (b : κ → K)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0) :
    hasseK (tensorK a b) = hasseK a ^ Fintype.card κ * hasseK b ^ Fintype.card ι *
      hs (discK a) (discK b) ^ (Fintype.card ι * Fintype.card κ + 1) *
      hs (discK a) (-1) ^ (Fintype.card κ * (Fintype.card κ - 1) / 2) *
      hs (discK b) (-1) ^ (Fintype.card ι * (Fintype.card ι - 1) / 2) := by
  set u := Fintype.card ι with hu
  set v := Fintype.card κ with hv
  set dU := discK a
  set dV := discK b
  have hdV : dV ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hb j
  have hdU : dU ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => ha i
  -- rewrite the product over the lexicographic product
  have hL : ∀ (f : ι ×ₗ κ → ℤ), ∏ p : ι ×ₗ κ, f p = ∏ i, ∏ j, f (toLex (i, j)) :=
    fun f => (Fintype.prod_equiv toLex _ f fun _ => rfl).symm.trans (Fintype.prod_prod_type _)
  have hexp : hasseK (tensorK a b) = ∏ i, ∏ k, ∏ j, ∏ l,
      (if i < k ∨ i = k ∧ j ≤ l then hs (a i * b j) (a k * b l) else 1) := by
    unfold hasseK tensorK
    rw [hL]
    simp_rw [hL]
    simp only [ofLex_toLex, Prod.Lex.toLex_le_toLex]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_comm]
  -- the blocks with i < k and with i = k
  have hblock : ∀ i k, (∏ j, ∏ l, (if i < k ∨ i = k ∧ j ≤ l then hs (a i * b j) (a k * b l) else 1)) =
      (if i < k then hs (a i ^ v * dV) (a k ^ v * dV) else 1) *
        (if i = k then hasseK (fun j => a i * b j) else 1) := by
    intro i k
    rcases lt_trichotomy i k with h | rfl | h
    · simp only [h, true_or, ite_true, h.ne, ite_false, mul_one]
      rw [prod_prod_hs hB _ _ (fun j => mul_ne_zero (ha i) (hb j)) (fun l => mul_ne_zero (ha k) (hb l)),
        Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      simp [dV, discK, hv]
    · simp [hasseK]
    · simp [h.not_gt, h.ne', (lt_asymm h)]
  rw [hexp]
  simp_rw [hblock, Finset.prod_mul_distrib]
  -- diagonal blocks: the scalar formula
  have hdiag : (∏ i, ∏ k, if i = k then hasseK (fun j => a i * b j) else 1) =
      hs dU (-1) ^ (v * (v + 1) / 2) * hs dU dV ^ (v + 1) * hasseK b ^ u := by
    simp only [Finset.prod_ite_eq, Finset.mem_univ, ite_true]
    rw [Finset.prod_congr rfl fun i _ => hasseK_scalar hB (ha i) b hb]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow, Finset.prod_const,
      ← hs_prod_left hB _ a ha (by norm_num), ← hs_prod_left hB _ a ha hdV]
    rfl
  -- off-diagonal blocks
  have hoff : ∀ i k, (if i < k then hs (a i ^ v * dV) (a k ^ v * dV) else 1) =
      (if i < k then hs (a i) (a k) ^ (v * v) else 1) * (if i < k then hs (a i) dV ^ v else 1) *
        (if i < k then hs (a k) dV ^ v else 1) * (if i < k then hs dV (-1) else 1) := by
    intro i k
    split_ifs
    · have hai := pow_ne_zero v (ha i)
      have hak := pow_ne_zero v (ha k)
      rw [hs_mul_left hB hai hdV (mul_ne_zero hak hdV), hB _ _ _ hai hak hdV, hB _ _ _ hdV hak hdV,
        hs_pow_left hB (ha i) hak, hilbertSymbol_comm K (a i) (a k ^ v), hs_pow_left hB (ha k) (ha i),
        hs_pow_left hB (ha i) hdV, hilbertSymbol_comm K dV (a k ^ v), hs_pow_left hB (ha k) hdV,
        hs_self hB hdV, hilbertSymbol_comm K (a k) (a i)]
      ring
    · simp
  simp_rw [hoff, Finset.prod_mul_distrib]
  rw [hdiag]
  have hite_pow : ∀ (i k : ι) (x : ℤ) (n : ℕ), (if i < k then x ^ n else 1) = (if i < k then x else 1) ^ n := by
    intro i k x n
    split_ifs <;> simp
  simp_rw [hite_pow, Finset.prod_pow]
  -- the four off-diagonal products
  set SL := ∏ i, ∏ k, if i < k then hs (a i) (a k) else 1 with hSL_def
  have hSL : SL = hasseK a * hs dU (-1) := by
    rw [hasseK_eq_lt hB a ha, mul_assoc, pm_mul_self (hs_pm _ _), mul_one]
  have hAB : (∏ i, ∏ k, if i < k then hs (a i) dV else 1) * (∏ i, ∏ k, if i < k then hs (a k) dV else 1) =
      ∏ m, hs (a m) dV ^ (u - 1) := by
    rw [Finset.prod_comm (f := fun i k => if i < k then hs (a k) dV else 1)]
    simp_rw [ite_eq_pow, Finset.prod_pow_eq_pow_sum]
    rw [← Finset.prod_mul_distrib]
    simp_rw [← pow_add]
    refine Finset.prod_congr rfl fun m _ => ?_
    have := cnt_point_lt u hu.symm m
    congr 1
    omega
  have hNlt : (∑ i : ι, ∑ k : ι, if i < k then 1 else 0) = u * (u - 1) / 2 := by
    have h1 := cnt_le_two u hu.symm
    have h2 := cnt_le_eq u hu.symm
    have h3 := tri u
    have h4 := tri' u
    omega
  have hz : (∏ m, hs (a m) dV ^ (u - 1)) ^ v * hs dU dV ^ (v + 1) = hs dU dV ^ (u * v + 1) := by
    rw [show hs dU dV = ∏ m, hs (a m) dV from hs_prod_left hB _ a ha hdV, ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_pow,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun m _ => ?_
    have hu0 : 0 < u := Fintype.card_pos_iff.mpr ⟨m⟩
    rw [← pow_mul, ← pow_add]
    congr 1
    clear_value u
    obtain ⟨w, rfl⟩ : ∃ w, u = w + 1 := ⟨u - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hx : hasseK a ^ (v * v) = hasseK a ^ v :=
    pm_pow_eq (hasseK_pm a) (by rw [Nat.mul_mod]; rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h])
  have hy : hs dU (-1) ^ (v * v) * hs dU (-1) ^ (v * (v + 1) / 2) = hs dU (-1) ^ (v * (v - 1) / 2) := by
    rw [← pow_add]
    refine pm_pow_eq (hs_pm _ _) ?_
    have h3 := tri v
    have h4 := tri' v
    omega
  rw [prod_prod_ite_const, hNlt, hSL, mul_pow, hx]
  calc _ = hasseK a ^ v * hasseK b ^ u *
          ((∏ m, hs (a m) dV ^ (u - 1)) ^ v * hs dU dV ^ (v + 1)) *
          (hs dU (-1) ^ (v * v) * hs dU (-1) ^ (v * (v + 1) / 2)) * hs dV (-1) ^ (u * (u - 1) / 2) := by
        rw [← hAB, mul_pow]
        ring
    _ = _ := by rw [hz, hy]

end Algebra

/-! ### The local fields $\mathbb Q_p$ and $\mathbb R$ -/

/-- The Hilbert symbol of $\mathbb Q_p$ is bimultiplicative. -/
theorem hilbertBimult_padic (p : ℕ) [Fact p.Prime] : HilbertBimult ℚ_[p] :=
  fun a b c ha hb hc => Cassels.Ch3Ex.hilbertSymbol_padic_mul_right a b c ha hb hc

/-- The Hilbert symbol of $\mathbb R$ is bimultiplicative: $(a, b)_{\mathbb R} = -1$ exactly when $a, b < 0$. -/
theorem hilbertBimult_real : HilbertBimult ℝ := by
  have key : ∀ x y : ℝ, x ≠ 0 → y ≠ 0 → hilbertSymbol ℝ x y = if x < 0 ∧ y < 0 then -1 else 1 := by
    intro x y hx hy
    split_ifs with h
    · exact (hilbertSymbol_real x y hx hy).mpr h
    · rcases hs_pm x y with h1 | h1
      · exact h1
      · exact absurd ((hilbertSymbol_real x y hx hy).mp h1) h
  intro a b c ha hb hc
  rw [key a (b * c) ha (mul_ne_zero hb hc), key a b ha hb, key a c ha hc]
  rcases lt_or_gt_of_ne hb with hb' | hb' <;> rcases lt_or_gt_of_ne hc with hc' | hc'
  · have h : ¬ b * c < 0 := (mul_pos_of_neg_of_neg hb' hc').not_gt
    by_cases h' : a < 0 <;> simp [h, h', hb', hc']
  · have h : b * c < 0 := mul_neg_of_neg_of_pos hb' hc'
    by_cases h' : a < 0 <;> simp [h, h', hb', hc', hc'.not_gt]
  · have h : b * c < 0 := mul_neg_of_pos_of_neg hb' hc'
    by_cases h' : a < 0 <;> simp [h, h', hb', hc', hb'.not_gt]
  · have h : ¬ b * c < 0 := (mul_pos hb' hc').not_gt
    by_cases h' : a < 0 <;> simp [h, h', hb'.not_gt, hc'.not_gt]

section Local

variable {ι κ : Type} [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]

/-- **Kitaoka 1993, Theorem 3.4.2, first formula** (p. 59), $F = \mathbb Q_p$: for regular diagonal spaces
$U = \perp_i\langle a_i\rangle$, $V = \perp_j\langle b_j\rangle$ over $\mathbb Q_p$,
$S(U \perp V) = S(U)S(V)(dU, dV)_p$. Unconditional. -/
@[kb "kitaoka1993" "§3.4, Thm. 3.4.2, p. 59 (S(U ⊥ V), over ℚ_p)"]
theorem theorem342_sum_padic (p : ℕ) [Fact p.Prime] (a : ι → ℚ_[p]) (b : κ → ℚ_[p]) (ha : ∀ i, a i ≠ 0)
    (hb : ∀ j, b j ≠ 0) :
    hasseK (fun s : ι ⊕ₗ κ => Sum.elim a b (ofLex s)) =
      hasseK a * hasseK b * hilbertSymbol ℚ_[p] (discK a) (discK b) :=
  hasseK_sum (hilbertBimult_padic p) a b ha hb

/-- **Kitaoka 1993, Theorem 3.4.2, first formula** (p. 59), $F = \mathbb R$: $S(U \perp V) = S(U)S(V)(dU, dV)_\infty$.
Unconditional. -/
@[kb "kitaoka1993" "§3.4, Thm. 3.4.2, p. 59 (S(U ⊥ V), over ℝ)"]
theorem theorem342_sum_real (a : ι → ℝ) (b : κ → ℝ) (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0) :
    hasseK (fun s : ι ⊕ₗ κ => Sum.elim a b (ofLex s)) =
      hasseK a * hasseK b * hilbertSymbol ℝ (discK a) (discK b) :=
  hasseK_sum hilbertBimult_real a b ha hb

/-- **Kitaoka 1993, Theorem 3.4.2, second formula** (p. 59), $F = \mathbb Q_p$: with $u = \dim U$, $v = \dim V$,
$S(U \otimes V) = S(U)^vS(V)^u(dU, dV)_p^{uv+1}(dU, -1)_p^{v(v-1)/2}(dV, -1)_p^{u(u-1)/2}$. Unconditional. -/
@[kb "kitaoka1993" "§3.4, Thm. 3.4.2, p. 59 (S(U ⊗ V), over ℚ_p)"]
theorem theorem342_tensor_padic (p : ℕ) [Fact p.Prime] (a : ι → ℚ_[p]) (b : κ → ℚ_[p]) (ha : ∀ i, a i ≠ 0)
    (hb : ∀ j, b j ≠ 0) :
    hasseK (tensorK a b) = hasseK a ^ Fintype.card κ * hasseK b ^ Fintype.card ι *
      hilbertSymbol ℚ_[p] (discK a) (discK b) ^ (Fintype.card ι * Fintype.card κ + 1) *
      hilbertSymbol ℚ_[p] (discK a) (-1) ^ (Fintype.card κ * (Fintype.card κ - 1) / 2) *
      hilbertSymbol ℚ_[p] (discK b) (-1) ^ (Fintype.card ι * (Fintype.card ι - 1) / 2) :=
  hasseK_tensor (hilbertBimult_padic p) a b ha hb

/-- **Kitaoka 1993, Theorem 3.4.2, second formula** (p. 59), $F = \mathbb R$. Unconditional. -/
@[kb "kitaoka1993" "§3.4, Thm. 3.4.2, p. 59 (S(U ⊗ V), over ℝ)"]
theorem theorem342_tensor_real (a : ι → ℝ) (b : κ → ℝ) (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0) :
    hasseK (tensorK a b) = hasseK a ^ Fintype.card κ * hasseK b ^ Fintype.card ι *
      hilbertSymbol ℝ (discK a) (discK b) ^ (Fintype.card ι * Fintype.card κ + 1) *
      hilbertSymbol ℝ (discK a) (-1) ^ (Fintype.card κ * (Fintype.card κ - 1) / 2) *
      hilbertSymbol ℝ (discK b) (-1) ^ (Fintype.card ι * (Fintype.card ι - 1) / 2) :=
  hasseK_tensor hilbertBimult_real a b ha hb

/-- **Kitaoka 1993, Theorem 3.4.2, third formula** (p. 59), $F = \mathbb Q_p$: for $c \in \mathbb Q_p^\times$ and
$V = \perp_j\langle b_j\rangle$ of dimension $v$, $S(\langle c\rangle \otimes V) = (c, -1)_p^{v(v+1)/2}(c, dV)_p^{v+1}
S(V)$. Unconditional. -/
@[kb "kitaoka1993" "§3.4, Thm. 3.4.2, p. 59 (S(⟨a⟩ ⊗ V), over ℚ_p)"]
theorem theorem342_scalar_padic (p : ℕ) [Fact p.Prime] {c : ℚ_[p]} (hc : c ≠ 0) (b : κ → ℚ_[p])
    (hb : ∀ j, b j ≠ 0) :
    hasseK (fun j => c * b j) = hilbertSymbol ℚ_[p] c (-1) ^ (Fintype.card κ * (Fintype.card κ + 1) / 2) *
      hilbertSymbol ℚ_[p] c (discK b) ^ (Fintype.card κ + 1) * hasseK b :=
  hasseK_scalar (hilbertBimult_padic p) hc b hb

/-- **Kitaoka 1993, Theorem 3.4.2, third formula** (p. 59), $F = \mathbb R$. Unconditional. -/
@[kb "kitaoka1993" "§3.4, Thm. 3.4.2, p. 59 (S(⟨a⟩ ⊗ V), over ℝ)"]
theorem theorem342_scalar_real {c : ℝ} (hc : c ≠ 0) (b : κ → ℝ) (hb : ∀ j, b j ≠ 0) :
    hasseK (fun j => c * b j) = hilbertSymbol ℝ c (-1) ^ (Fintype.card κ * (Fintype.card κ + 1) / 2) *
      hilbertSymbol ℝ c (discK b) ^ (Fintype.card κ + 1) * hasseK b :=
  hasseK_scalar hilbertBimult_real hc b hb

end Local

end QuadFormsKB.Kitaoka.Hasse
