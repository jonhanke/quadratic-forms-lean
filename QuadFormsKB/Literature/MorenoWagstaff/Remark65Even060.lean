/-
# Moreno–Wagstaff 2005, Remark 6.5 for every even $k \ge 4$: the singular series of $2k$ squares

**Source.** C. J. Moreno and S. S. Wagstaff Jr., *Sums of Squares of Integers* (2005), Remark 6.5, (6.23), p. 196.

**Result** (`remark65Even`, unconditional, statement `Remark65Even` of `Wave2/RemarkSixFive.lean`): for even $k \ge 4$
and $n \ge 1$,
$$\rho_{2k}(n) = \frac{2k}{(2^k - 1)\,|B_k|}\sum_{d \mid n} d^{k-1}(-1)^{(d + k/2)(n/d - 1)}.$$
Numerical check before proving: for $k = 6$ the constant is $8$ and the right side gives $8, 264, 1952, 7944$ at
$n = 1, 2, 3, 4$, agreeing with the Eisenstein part of $r_{12}(n)$; no erratum was found.

**Route** (Siegel's local product, as for six squares in the historical library; arguments copied and adapted):
write $k = 2(j+1)$, $n = 2^a u$ with $u$ odd.
1. $\rho_{2k}(n) = \beta_\infty(n)\prod_p\beta_p(n)$ (`singularSeriesSq_eq_aE`, `betaInf_sumSq`).
2. Odd $p$ (`localDensity_sumSq_even_odd`): $\beta_p(p^a u') = (1 - p^{-k})\sum_{i \le a}(p^{1-k})^i$, from Table 2 and the
   recursion (5.7), the character $((-1)^k/p)$ being trivial.
3. $p = 2$: counting solutions modulo $8$ (`sqCnt8_four_mul`, a closed form for $\#\{x \in (\mathbb Z/8)^{4h} : \sum x_i^2 = c\}$
   proved by convolution with the table for four squares) gives $\beta_2$ for $4 \nmid n$; the Zero-type reduction
   (`beta2_four_mul`) gives $\beta_2(4T) = 4\beta_2(T)/2^{2k} + (N(4T) - 2^{4k}/2)\cdot 8/2^{6k}$, and by strong induction
   (`beta2_pow_mul`) $2^{a(k-1)}\beta_2(2^a u) = T_a$ with $T_0 = 1$ and
   $T_a = 2^{a(k-1)} + (-1)^{k/2}\bigl(\sum_{b<a}2^{b(k-1)} - 2\bigr)$ for $a \ge 1$.
4. Euler products (`eulerProduct_even`): $\prod_p(1 - p^{-k}) = \zeta(k)^{-1}$ (`hasProd_one_sub_inv_pow`, with
   $\zeta(2h)$ from Mathlib's `hasSum_zeta_nat`, the sign of $B_{2h}$ coming from positivity of $\zeta$) and the
   divisor-sum Euler product (`hasProd_gG`).
5. The divisor sum of the statement equals $\sigma_{k-1}(u)\,T_a$ (`divisorSum_eq`), by splitting divisors of $2^a u$
   as products; the final identity is `aE_even` and `remark65Even`.
-/
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.LSeries.RiemannZeta
import QuadFormsKB.Siegel.FourSquaresDensities
import QuadFormsKB.Siegel.Theta
import QuadFormsKB.LocalDensity.Table2
import QuadFormsKB.LocalDensity.LowerBounds
import QuadFormsKB.LocalDensity.Explicit
import QuadFormsKB.Literature.MorenoWagstaff.Wave2.RemarkSixFive
import Mathlib.Data.Finset.NatDivisors

namespace QuadFormsKB.MorenoWagstaff.Remark65Even060

open QuadFormsKB.Siegel QuadFormsKB.LocalDensity

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-! ### Counting solutions modulo $q$ of a sum of squares -/

/-- The number of $\vec x \in (\mathbb Z/q)^n$ with $x_0^2 + \dots + x_{n-1}^2 = c$. -/
def sqCnt (q n : ℕ) [NeZero q] (c : ZMod q) : ℕ :=
  Fintype.card {x : Fin n → ZMod q // ∑ i, x i ^ 2 = c}

theorem sqCnt_zero (q : ℕ) [NeZero q] (c : ZMod q) : sqCnt q 0 c = if c = 0 then 1 else 0 := by
  unfold sqCnt
  simp only [Finset.univ_eq_empty, Finset.sum_empty]
  split_ifs with h
  · subst h
    exact Fintype.card_eq_one_iff.mpr ⟨⟨finZeroElim, rfl⟩, fun x => Subtype.ext (funext finZeroElim)⟩
  · exact Fintype.card_eq_zero_iff.mpr ⟨fun x => h x.2.symm⟩

/-- Adding one variable: $N_{n+1}(c) = \sum_y N_n(c - y^2)$. -/
theorem sqCnt_succ (q n : ℕ) [NeZero q] (c : ZMod q) :
    sqCnt q (n + 1) c = ∑ y : ZMod q, sqCnt q n (c - y ^ 2) := by
  classical
  unfold sqCnt
  rw [Fintype.card_congr ((Fin.consEquiv fun _ : Fin (n + 1) => ZMod q).symm.subtypeEquiv
      (q := fun p : ZMod q × (Fin n → ZMod q) => p.1 ^ 2 + ∑ i, p.2 i ^ 2 = c)
      (fun x => by simp [Fin.sum_univ_succ, Fin.consEquiv, Fin.tail]))]
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Fintype.card_subtype, Finset.card_filter]
  refine Finset.sum_congr rfl fun z _ => ?_
  congr 1
  exact propext ⟨fun h => by rw [← h]; ring, fun h => by rw [h]; ring⟩

/-- Convolution: $N_{m+n}(c) = \sum_r N_m(r)N_n(c - r)$. -/
theorem sqCnt_add (q : ℕ) [NeZero q] (m n : ℕ) (c : ZMod q) :
    sqCnt q (m + n) c = ∑ r : ZMod q, sqCnt q m r * sqCnt q n (c - r) := by
  induction m generalizing c with
  | zero =>
    simp only [zero_add, sqCnt_zero]
    simp
  | succ m ih =>
    rw [Nat.add_right_comm, sqCnt_succ]
    simp only [ih, sqCnt_succ, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    refine Fintype.sum_equiv (Equiv.addRight (y ^ 2)) _ _ fun r => ?_
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    congr 2
    ring

/-- Counts of $\sum_{i<n} x_i^2 \equiv c \pmod 8$, for $n = 1, \dots, 4$. -/
def tab8 : ℕ → ZMod 8 → ℕ
  | 1 => ![2, 4, 0, 0, 2, 0, 0, 0]
  | 2 => ![8, 16, 16, 0, 8, 16, 0, 0]
  | 3 => ![32, 96, 96, 64, 32, 96, 96, 0]
  | _ => ![128, 512, 768, 512, 384, 512, 768, 512]

theorem sqCnt8_one (c : ZMod 8) : sqCnt 8 1 c = tab8 1 c := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, sqCnt_succ]
  simp only [sqCnt_zero]
  revert c; decide

theorem sqCnt8_succ_tab (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 3) (c : ZMod 8) :
    tab8 (n + 1) c = ∑ y : ZMod 8, tab8 n (c - y ^ 2) := by
  interval_cases n <;> revert c <;> decide

theorem sqCnt8_eq_tab (n : ℕ) (h1 : 1 ≤ n) (h4 : n ≤ 4) (c : ZMod 8) : sqCnt 8 n c = tab8 n c := by
  induction n generalizing c with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact sqCnt8_one c
    · rw [sqCnt_succ, sqCnt8_succ_tab n hpos (by omega)]
      exact Finset.sum_congr rfl fun y _ => ih hpos (by omega) _

/-- $R_0$: $4, -4$ at $c = 0, 4$, else $0$. -/
def R0 (c : ZMod 8) : ℤ := if c = 0 then 4 else if c = 4 then -4 else 0

/-- $C_i$: $1$ at $c = 0, 4$; $-1$ at $c = 2, 6$; else $0$. -/
def Ci (c : ZMod 8) : ℤ := if c = 0 ∨ c = 4 then 1 else if c = 2 ∨ c = 6 then -1 else 0

theorem R0_eigen : ∀ c : ZMod 8, ∑ r : ZMod 8, (tab8 4 r : ℤ) * R0 (c - r) = -256 * R0 c := by
  decide

theorem Ci_eigen : ∀ c : ZMod 8, ∑ r : ZMod 8, (tab8 4 r : ℤ) * Ci (c - r) = -1024 * Ci c := by
  decide

theorem one_eigen : ∑ r : ZMod 8, (tab8 4 r : ℤ) = 4096 := by decide

/-- **Closed form of $N_{4h}(c)$ modulo $8$** ($h \ge 1$). -/
theorem sqCnt8_four_mul (h : ℕ) (hh : 1 ≤ h) (c : ZMod 8) :
    8 * (sqCnt 8 (4 * h) c : ℤ) =
      8 ^ (4 * h) + (-1) ^ h * (2 ^ (8 * h) * R0 c + 2 * 2 ^ (10 * h) * Ci c) := by
  induction h, hh using Nat.le_induction generalizing c with
  | base =>
    rw [sqCnt8_eq_tab 4 (by norm_num) le_rfl]
    revert c; decide
  | succ h hh ih =>
    rw [show 4 * (h + 1) = 4 + 4 * h by ring, sqCnt_add]
    push_cast
    rw [Finset.mul_sum]
    have : ∀ r : ZMod 8, 8 * ((sqCnt 8 4 r : ℤ) * (sqCnt 8 (4 * h) (c - r) : ℤ)) =
        (tab8 4 r : ℤ) * (8 ^ (4 * h) + (-1) ^ h * (2 ^ (8 * h) * R0 (c - r) +
          2 * 2 ^ (10 * h) * Ci (c - r))) := by
      intro r
      rw [sqCnt8_eq_tab 4 (by norm_num) le_rfl, ← ih (c - r)]
      ring
    rw [Finset.sum_congr rfl fun r _ => this r]
    have key : ∑ r : ZMod 8, (tab8 4 r : ℤ) * (8 ^ (4 * h) + (-1) ^ h * (2 ^ (8 * h) * R0 (c - r) +
          2 * 2 ^ (10 * h) * Ci (c - r))) =
        (∑ r : ZMod 8, (tab8 4 r : ℤ)) * 8 ^ (4 * h) +
        ((-1) ^ h * 2 ^ (8 * h)) * ∑ r : ZMod 8, (tab8 4 r : ℤ) * R0 (c - r) +
        (2 * (-1) ^ h * 2 ^ (10 * h)) * ∑ r : ZMod 8, (tab8 4 r : ℤ) * Ci (c - r) := by
      simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [key, one_eigen, R0_eigen, Ci_eigen]
    ring

/-! ### Local densities at odd primes -/

theorem sumSq_eq_diag' (n : ℕ) : sumSq n = QuadForm.diag fun _ : Fin n => (1 : ℤ) := rfl

lemma not_dvd_one' {n : ℕ} (p : ℕ) [Fact p.Prime] : ∀ _ : Fin n, ¬ (p : ℤ) ∣ (1 : ℤ) := fun _ h =>
  (Fact.out : p.Prime).one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h)

lemma legendre_even (k : ℕ) (hk : Even k) (p : ℕ) [Fact p.Prime] :
    (legendreSym p ((-1) ^ (2 * k / 2) * ∏ i : Fin (2 * k), (1 : ℤ)) : ℝ) = 1 := by
  rw [Nat.mul_div_cancel_left _ (by norm_num), hk.neg_one_pow]
  simp [legendreSym.at_one]

/-- The non-Zero-type density of $I_{2k}$ at $p^2T$ ($p$ odd): $(1 - p^{-k})(1 + p^{1-k})$. -/
theorem nz_odd_sq (k : ℕ) (hk : Even k) (hk1 : 1 ≤ k) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (T : ℤ) :
    localDensityOf (sumSq (2 * k)) p ((p : ℤ) ^ 2 * T) (fun j x => ¬ IsZeroType p j x) =
      (1 - 1 / (p : ℝ) ^ k) * (1 + 1 / (p : ℝ) ^ (k - 1)) := by
  have hpp : p.Prime := Fact.out
  have h1 : padicValInt p (p : ℤ) = 1 := by simp [padicValInt, padicValNat_self]
  have ha := not_dvd_one' (n := 2 * k) p
  rw [sumSq_eq_diag', localDensityOf_nonZero_diag_sq _ p hp ha T,
    ← localDensity_diag_ord_one (fun _ : Fin (2 * k) => (1 : ℤ)) p hp ha (p : ℤ) h1,
    localDensity_diag_even_ord_one (fun _ : Fin (2 * k) => (1 : ℤ)) p hp ha (by omega)
      (by exact ⟨k, by ring⟩) (p : ℤ) dvd_rfl (by
        intro h
        have h' : p ^ 2 ∣ p := by exact_mod_cast h
        have := Nat.le_of_dvd hpp.pos h'
        nlinarith [hpp.two_le]),
    legendre_even k hk]
  rw [show 2 * k / 2 = k by omega, show (2 * k - 2) / 2 = k - 1 by omega]

/-- **$\beta_p$ of $I_{2k}$, $k$ even, odd $p$, all valuations:** for $p \nmid u$,
$\beta_p(p^a u) = (1 - p^{-k})\sum_{i=0}^{a}(p^{1-k})^i$. -/
theorem localDensity_sumSq_even_odd (k : ℕ) (hk : Even k) (hk1 : 1 ≤ k) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a : ℕ) (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) :
    localDensity (sumSq (2 * k)) p ((p : ℤ) ^ a * u) =
      (1 - 1 / (p : ℝ) ^ k) * ∑ i ∈ Finset.range (a + 1), (1 / (p : ℝ) ^ (k - 1)) ^ i := by
  have hpp : p.Prime := Fact.out
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have ha := not_dvd_one' (n := 2 * k) p
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (dvd_zero _)
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    match a with
    | 0 =>
      rw [pow_zero, one_mul, sumSq_eq_diag',
        localDensity_diag_even_unit (fun _ : Fin (2 * k) => (1 : ℤ)) p hp ha (by omega)
          (by exact ⟨k, by ring⟩) u hu, legendre_even k hk, show 2 * k / 2 = k by omega]
      simp
    | 1 =>
      rw [pow_one, sumSq_eq_diag',
        localDensity_diag_even_ord_one (fun _ : Fin (2 * k) => (1 : ℤ)) p hp ha (by omega)
          (by exact ⟨k, by ring⟩) _
          (dvd_mul_right _ _) (by
            rintro ⟨c, hc⟩
            apply hu
            refine ⟨c, mul_left_cancel₀ (by exact_mod_cast hpp.ne_zero : (p : ℤ) ≠ 0) ?_⟩
            rw [hc]; ring),
        legendre_even k hk, show 2 * k / 2 = k by omega, show (2 * k - 2) / 2 = k - 1 by omega]
      simp [Finset.sum_range_succ]
    | a + 2 =>
      have hT : (p : ℤ) ^ a * u ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hpp.ne_zero)) hu0
      have hK := localDensityOf_nonZero_eq (sumSq (2 * k)) posDef_sumSq.nondegenerate p
        (by omega) _ hT
      rw [nz_odd_sq k hk hk1 p hp] at hK
      have e : (p : ℤ) ^ (a + 2) * u = (p : ℤ) ^ 2 * ((p : ℤ) ^ a * u) := by ring
      rw [e]
      have hloc : localDensity (sumSq (2 * k)) p ((p : ℤ) ^ 2 * ((p : ℤ) ^ a * u)) =
          localDensity (sumSq (2 * k)) p ((p : ℤ) ^ a * u) / ((p : ℝ) ^ (2 * k - 2)) +
            (1 - 1 / (p : ℝ) ^ k) * (1 + 1 / (p : ℝ) ^ (k - 1)) := by
        rw [div_eq_mul_inv, mul_comm (localDensity _ _ _)]
        push_cast at hK
        linarith
      rw [hloc, ih a (by omega), sum_range_add_two]
      have hx : ((p : ℝ) ^ (2 * k - 2)) = ((p : ℝ) ^ (k - 1)) ^ 2 := by
        rw [← pow_mul]; congr 1; omega
      rw [hx]
      have : (p : ℝ) ^ (k - 1) ≠ 0 := pow_ne_zero _ hp0
      field_simp
      ring

/-! ### Local densities at $2$ -/

theorem evalIn_sumSq' {n : ℕ} {S : Type*} [CommRing S] (x : Fin n → S) :
    (sumSq n).evalIn S x = ∑ i, x i ^ 2 := by
  simp only [sumSq, QuadForm.evalIn, QuadForm.diag, Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp [sq]
  · intro j _ hj; simp [Ne.symm hj]
  · simp

/-- The non-Zero-type density at $p = 2$ is attained at level $3$. -/
theorem localDensityOf_nonZero_sumSq_two (n : ℕ) (m : ℤ) :
    localDensityOf (sumSq n) 2 m (fun k x => ¬ IsZeroType 2 k x) =
      (repCountOf (sumSq n) 2 3 m (fun x => ¬ IsZeroType 2 3 x) : ℝ) / 2 ^ (3 * (n - 1)) := by
  apply limUnder_eq_of_eventually
  filter_upwards [Filter.eventually_ge_atTop 3] with k hk
  obtain ⟨l, rfl⟩ : ∃ l, k = 3 + l := ⟨k - 3, by omega⟩
  have h := repCountGood_add_diag (fun _ : Fin n => (1 : ℤ)) 2 m 3 l (by norm_num)
  rw [isGoodType_diag_unimodular _ 2 (not_dvd_one' 2),
    isGoodType_diag_unimodular _ 2 (not_dvd_one' 2)] at h
  rw [sumSq_eq_diag', h]
  push_cast
  rw [show (3 + l) * (n - 1) = 3 * (n - 1) + (n - 1) * l by ring, pow_add]
  field_simp

theorem repCount_sumSq_eq (q : ℕ) [Fact q.Prime] (k n : ℕ) (m : ℤ) :
    repCount (sumSq n) q k m = sqCnt (q ^ k) n (m : ZMod (q ^ k)) := by
  haveI : NeZero (q ^ k) := ⟨pow_ne_zero _ (Fact.out : q.Prime).ne_zero⟩
  unfold repCount sqCnt
  rw [Nat.card_eq_fintype_card]
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [evalIn_sumSq']

/-- If $4 \nmid m$, $\beta_2(m) = N_n(m \bmod 8)/2^{3(n-1)}$. -/
theorem localDensity_sumSq_two (n : ℕ) (m : ℤ) (hm : ¬ (4 : ℤ) ∣ m) :
    localDensity (sumSq n) 2 m = (sqCnt 8 n (m : ZMod 8) : ℝ) / 2 ^ (3 * (n - 1)) := by
  have h1 : localDensity (sumSq n) 2 m = localDensityOf (sumSq n) 2 m (fun k x => ¬ IsZeroType 2 k x) := by
    unfold localDensity localDensityOf Filter.limUnder
    refine congrArg Filter.lim (Filter.map_congr ?_)
    filter_upwards [Filter.eventually_ge_atTop 2] with k hk
    have hm' : ¬ ((2 : ℕ) : ℤ) ^ 2 ∣ m := by norm_num; exact hm
    rw [repCount_eq_zero_add_nonZero, repCountZero_eq _ 2 m k hk]
    simp only [hm', ↓reduceIte, zero_add]
  rw [h1, localDensityOf_nonZero_sumSq_two]
  congr 2
  have hz : repCountOf (sumSq n) 2 3 m (IsZeroType 2 3) = 0 := by
    rw [repCountZero_eq _ 2 m 3 (by norm_num)]
    have hm' : ¬ ((2 : ℕ) : ℤ) ^ 2 ∣ m := by norm_num; exact hm
    split_ifs
    rfl
  have hsplit := repCount_eq_zero_add_nonZero (sumSq n) 2 3 m
  rw [hz, zero_add] at hsplit
  rw [← hsplit, repCount_sumSq_eq]
  rfl

theorem sqCnt_two (n : ℕ) (hn : 1 ≤ n) (c : ZMod 2) : sqCnt 2 n c = 2 ^ (n - 1) := by
  induction n, hn using Nat.le_induction generalizing c with
  | base =>
    rw [sqCnt_succ 2 0]
    simp only [sqCnt_zero]
    revert c; decide
  | succ n hn ih =>
    rw [sqCnt_succ]
    simp only [ih]
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
    rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]
    ring

/-- Level $3$ solutions that are not of Zero type, when $4 \mid m$. -/
theorem nonZero_level3 (n : ℕ) (hn : 1 ≤ n) (m : ℤ) (hm : (4 : ℤ) ∣ m) :
    repCountOf (sumSq n) 2 3 m (fun x => ¬ IsZeroType 2 3 x) + 2 ^ n * 2 ^ (n - 1) =
      sqCnt 8 n (m : ZMod 8) := by
  have hsplit := repCount_eq_zero_add_nonZero (sumSq n) 2 3 m
  rw [repCountZero_eq _ 2 m 3 (by norm_num)] at hsplit
  have hm' : ((2 : ℕ) : ℤ) ^ 2 ∣ m := by norm_num; exact hm
  rw [if_pos hm'] at hsplit
  have h1 : repCount (sumSq n) 2 (3 - 2) (m / ((2 : ℕ) : ℤ) ^ 2) = 2 ^ (n - 1) := by
    rw [repCount_sumSq_eq 2 (3 - 2) n]
    exact sqCnt_two n hn _
  rw [h1] at hsplit
  rw [repCount_sumSq_eq] at hsplit
  have : sqCnt (2 ^ 3) n (m : ZMod (2 ^ 3)) = sqCnt 8 n (m : ZMod 8) := rfl
  rw [this] at hsplit
  omega

/-! ### $\beta_2$ of $I_{4(j+1)}$ -/

/-- $P = 2^k$ with $k = 2(j+1)$. -/
noncomputable def PP (j : ℕ) : ℝ := 2 ^ (2 * (j + 1))

/-- $g = 2^{k-1}$ with $k = 2(j+1)$. -/
noncomputable def gg (j : ℕ) : ℝ := 2 ^ (2 * j + 1)

/-- $s = (-1)^{k/2}$. -/
noncomputable def ss (j : ℕ) : ℝ := (-1) ^ (j + 1)

theorem PP_eq (j : ℕ) : PP j = 2 * gg j := by unfold PP gg; ring

theorem gg_pos (j : ℕ) : 0 < gg j := by unfold gg; positivity

theorem ss_sq (j : ℕ) : ss j ^ 2 = 1 := by
  unfold ss; rw [← pow_mul, mul_comm, pow_mul]; simp

theorem count_real (j : ℕ) (c : ZMod 8) :
    (sqCnt 8 (2 * (2 * (j + 1))) c : ℝ) =
      (PP j ^ 6 + ss j * (PP j ^ 4 * (R0 c : ℝ) + 2 * PP j ^ 5 * (Ci c : ℝ))) / 8 := by
  have h := sqCnt8_four_mul (j + 1) (by omega) c
  rw [show 4 * (j + 1) = 2 * (2 * (j + 1)) by ring] at h
  have h' := congrArg (Int.cast : ℤ → ℝ) h
  push_cast at h'
  have e1 : (8 : ℝ) ^ (2 * (2 * (j + 1))) = PP j ^ 6 := by
    unfold PP; rw [← pow_mul, show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul]; congr 1; ring
  have e2 : (2 : ℝ) ^ (8 * (j + 1)) = PP j ^ 4 := by
    unfold PP; rw [← pow_mul]; congr 1; ring
  have e3 : (2 : ℝ) ^ (10 * (j + 1)) = PP j ^ 5 := by
    unfold PP; rw [← pow_mul]; congr 1; ring
  rw [e1, e2, e3] at h'
  unfold ss
  linarith

theorem pow_den (j : ℕ) : (2 : ℝ) ^ (3 * (2 * (2 * (j + 1)) - 1)) = PP j ^ 6 / 8 := by
  rw [show 3 * (2 * (2 * (j + 1)) - 1) = 12 * j + 9 by omega]
  unfold PP
  rw [← pow_mul]
  rw [eq_div_iff (by norm_num)]
  ring

theorem pow_four (j : ℕ) : (2 : ℝ) ^ (2 * (2 * (j + 1))) * 2 ^ (2 * (2 * (j + 1)) - 1) = PP j ^ 4 / 2 := by
  rw [← pow_add, show 2 * (2 * (j + 1)) + (2 * (2 * (j + 1)) - 1) = 8 * j + 7 by omega]
  unfold PP
  rw [← pow_mul, eq_div_iff (by norm_num), ← pow_succ]
  congr 1; ring

theorem pow_nm2 (j : ℕ) : (2 : ℝ) ^ (2 * (2 * (j + 1)) - 2) = PP j ^ 2 / 4 := by
  rw [show 2 * (2 * (j + 1)) - 2 = 4 * j + 2 by omega]
  unfold PP
  rw [← pow_mul, eq_div_iff (by norm_num)]
  ring

theorem PP_pos (j : ℕ) : 0 < PP j := by rw [PP_eq]; have := gg_pos j; linarith

/-- $\beta_2(m) = 1$ for odd $m$. -/
theorem beta2_odd (j : ℕ) (m : ℤ) (hm : Odd m) :
    localDensity (sumSq (2 * (2 * (j + 1)))) 2 m = 1 := by
  have hnd : ¬ (4 : ℤ) ∣ m := by obtain ⟨k, rfl⟩ := hm; omega
  rw [localDensity_sumSq_two _ m hnd, count_real, pow_den]
  have hodd : ((m : ZMod 8)) ≠ 0 ∧ (m : ZMod 8) ≠ 2 ∧ (m : ZMod 8) ≠ 4 ∧ (m : ZMod 8) ≠ 6 := by
    have hv : ((((m : ℤ) : ZMod 8)).val : ℤ) = m % 8 := ZMod.val_intCast m
    obtain ⟨k, rfl⟩ := hm
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> rw [h] at hv <;> revert hv <;> simp [ZMod.val] <;> omega
  have hP := PP_pos j
  rw [show R0 (m : ZMod 8) = 0 by unfold R0; simp [hodd.1, hodd.2.2.1],
    show Ci (m : ZMod 8) = 0 by unfold Ci; simp [hodd.1, hodd.2.1, hodd.2.2.1, hodd.2.2.2]]
  field_simp
  simp

theorem R0Ci (r : ZMod 8) :
    (r.val % 2 = 1 → R0 r = 0 ∧ Ci r = 0) ∧ (r.val % 4 = 2 → R0 r = 0 ∧ Ci r = -1) ∧
    (r.val = 4 → R0 r = -4 ∧ Ci r = 1) ∧ (r.val = 0 → R0 r = 4 ∧ Ci r = 1) := by
  revert r; decide

/-- $\beta_2(2u) = 1 - 2s/P$ for odd $u$. -/
theorem beta2_two (j : ℕ) (m : ℤ) (hm : m % 4 = 2) :
    localDensity (sumSq (2 * (2 * (j + 1)))) 2 m = 1 - 2 * ss j / PP j := by
  have hnd : ¬ (4 : ℤ) ∣ m := by omega
  rw [localDensity_sumSq_two _ m hnd, count_real, pow_den]
  have hv : ((((m : ℤ) : ZMod 8)).val : ℤ) = m % 8 := ZMod.val_intCast m
  have h := (R0Ci (m : ZMod 8)).2.1 (by omega)
  have hP := PP_pos j
  rw [h.1, h.2]
  field_simp
  push_cast
  ring

/-- The recursion at $2$: $\beta_2(4T) = 4\beta_2(T)/P^2 + (N(4T) - P^4/2)\cdot 8/P^6$. -/
theorem beta2_four_mul (j : ℕ) (T : ℤ) (hT : T ≠ 0) :
    localDensity (sumSq (2 * (2 * (j + 1)))) 2 (4 * T) =
      4 * localDensity (sumSq (2 * (2 * (j + 1)))) 2 T / PP j ^ 2 +
        ((sqCnt 8 (2 * (2 * (j + 1))) ((4 * T : ℤ) : ZMod 8) : ℝ) - PP j ^ 4 / 2) * 8 / PP j ^ 6 := by
  have h := localDensityOf_nonZero_eq (sumSq (2 * (2 * (j + 1)))) posDef_sumSq.nondegenerate 2
    (by omega) T hT
  have e : ((2 : ℕ) : ℤ) ^ 2 * T = 4 * T := by norm_num
  rw [e, localDensityOf_nonZero_sumSq_two] at h
  have hc := nonZero_level3 (2 * (2 * (j + 1))) (by omega) (4 * T) ⟨T, rfl⟩
  have hc' : (repCountOf (sumSq (2 * (2 * (j + 1)))) 2 3 (4 * T) (fun x => ¬ IsZeroType 2 3 x) : ℝ) =
      (sqCnt 8 (2 * (2 * (j + 1))) ((4 * T : ℤ) : ZMod 8) : ℝ) - PP j ^ 4 / 2 := by
    rw [← pow_four]
    have : ((repCountOf (sumSq (2 * (2 * (j + 1)))) 2 3 (4 * T) (fun x => ¬ IsZeroType 2 3 x) : ℕ) : ℝ) +
        2 ^ (2 * (2 * (j + 1))) * 2 ^ (2 * (2 * (j + 1)) - 1) =
        (sqCnt 8 (2 * (2 * (j + 1))) ((4 * T : ℤ) : ZMod 8) : ℝ) := by exact_mod_cast hc
    linarith
  have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [h2] at h
  rw [hc', pow_den, pow_nm2] at h
  have hP := PP_pos j
  have hd : ((PP j ^ 2 / 4)⁻¹) = 4 / PP j ^ 2 := by rw [inv_div]
  rw [hd] at h
  have : ((sqCnt 8 (2 * (2 * (j + 1))) ((4 * T : ℤ) : ZMod 8) : ℝ) - PP j ^ 4 / 2) / (PP j ^ 6 / 8) =
      ((sqCnt 8 (2 * (2 * (j + 1))) ((4 * T : ℤ) : ZMod 8) : ℝ) - PP j ^ 4 / 2) * 8 / PP j ^ 6 := by
    field_simp
  rw [this] at h
  have e2 : 4 / PP j ^ 2 * localDensity (sumSq (2 * (2 * (j + 1)))) 2 T =
      4 * localDensity (sumSq (2 * (2 * (j + 1)))) 2 T / PP j ^ 2 := by ring
  linarith

theorem val_eq_of_mod (x : ℤ) (r : ℕ) (h : x % 8 = r) : (x : ZMod 8).val = r := by
  have := ZMod.val_intCast (n := 8) x
  omega

/-- **$\beta_2$ of $I_{2k}$ on $2^a u$**($k = 2(j+1)$, $u$ odd): $1$ if $a = 0$, and otherwise
$T_a/g^a$ with $g = 2^{k-1}$, $T_a = g^a + (-1)^{k/2}\bigl(\sum_{b<a} g^b - 2\bigr)$. -/
theorem beta2_pow_mul (j a : ℕ) (u : ℤ) (hu : Odd u) :
    localDensity (sumSq (2 * (2 * (j + 1)))) 2 (2 ^ a * u) =
      if a = 0 then 1 else
        (gg j ^ a + ss j * (∑ b ∈ Finset.range a, gg j ^ b - 2)) / gg j ^ a := by
  obtain ⟨w, rfl⟩ := hu
  have hg := gg_pos j
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    match a with
    | 0 => simpa using beta2_odd j _ ⟨w, rfl⟩
    | 1 =>
      rw [beta2_two j _ (by norm_num; omega)]
      simp only [Nat.one_ne_zero, ↓reduceIte, Finset.sum_range_one, pow_one, pow_zero]
      rw [PP_eq]
      field_simp
      ring
    | a + 2 =>
      have hT : (2 : ℤ) ^ a * (2 * w + 1) ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (by norm_num)) (by omega)
      rw [show (2 : ℤ) ^ (a + 2) * (2 * w + 1) = 4 * (2 ^ a * (2 * w + 1)) by ring,
        beta2_four_mul j _ hT, ih a (by omega), count_real]
      have hP := PP_pos j
      rcases a with _ | a
      · have h := (R0Ci (((4 * (2 ^ 0 * (2 * w + 1)) : ℤ) : ZMod 8))).2.2.1
          (val_eq_of_mod _ 4 (by rw [pow_zero]; omega))
        rw [h.1, h.2]
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, if_true, Nat.add_eq_zero_iff,
          OfNat.ofNat_ne_zero, and_false, ↓reduceIte, zero_add, pow_zero, pow_one]
        rw [PP_eq]
        have : PP j = 2 * gg j := PP_eq j
        have h2 : (2 * gg j) ≠ 0 := by positivity
        push_cast
        field_simp
        ring
      · have h := (R0Ci (((4 * (2 ^ (a + 1) * (2 * w + 1)) : ℤ) : ZMod 8))).2.2.2
          (val_eq_of_mod _ 0 (by
            rw [show (4 * (2 ^ (a + 1) * (2 * w + 1)) : ℤ) = 8 * (2 ^ a * (2 * w + 1)) by ring]
            omega))
        rw [h.1, h.2]
        simp only [Finset.sum_range_succ (n := a + 1 + 1), Finset.sum_range_succ (n := a + 1)]
        simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte,
          Nat.succ_ne_zero]
        rw [PP_eq]
        have h2 : (2 * gg j) ≠ 0 := by positivity
        push_cast
        field_simp
        ring

/-! ### Euler products -/

/-- $d \mapsto d^{-(e+1)}$ as an arithmetic function. -/
noncomputable def invPow (e : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => 1 / (d : ℝ) ^ (e + 1), by simp⟩

theorem isMultiplicative_invPow (e : ℕ) : ArithmeticFunction.IsMultiplicative (invPow e) := by
  refine ⟨by simp [invPow], fun {m n} _ => ?_⟩
  simp only [invPow, ArithmeticFunction.coe_mk, Nat.cast_mul, mul_pow, one_div, mul_inv]

/-- $\sum_{d \mid m} d^{-(e+1)} = \prod_{p \mid m}\sum_{i \le v_p(m)} (p^{-(e+1)})^i$. -/
theorem sum_divisors_invPow (e m : ℕ) (hm : m ≠ 0) :
    ∑ d ∈ m.divisors, 1 / (d : ℝ) ^ (e + 1) =
      ∏ p ∈ m.primeFactors, ∑ i ∈ Finset.range (m.factorization p + 1), (1 / (p : ℝ) ^ (e + 1)) ^ i := by
  have hmul := ((isMultiplicative_invPow e).mul ArithmeticFunction.isMultiplicative_zeta.natCast)
  have h := hmul.multiplicative_factorization _ hm
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  have hz : ∑ d ∈ m.divisors, 1 / (d : ℝ) ^ (e + 1) = ∑ d ∈ m.divisors, invPow e d := rfl
  rw [hz, h, Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.divisors_prime_pow hpp, Finset.sum_map]
  refine Finset.sum_congr rfl fun i _ => ?_
  show 1 / (((p ^ i : ℕ)) : ℝ) ^ (e + 1) = _
  rw [Nat.cast_pow, ← pow_mul, mul_comm, pow_mul, one_div_pow]

/-- The factor $\sum_{i \le v_p(m)}(p^{-(e+1)})^i$ at the prime $p$. -/
noncomputable def gG (e m : ℕ) (p : AWS.PrimeIdx) : ℝ :=
  ∑ i ∈ Finset.range (m.factorization p + 1), (1 / ((p : ℕ) : ℝ) ^ (e + 1)) ^ i

theorem hasProd_gG (e m : ℕ) (hm : m ≠ 0) :
    HasProd (gG e m) (∑ d ∈ m.divisors, 1 / (d : ℝ) ^ (e + 1)) := by
  let s : Finset AWS.PrimeIdx :=
    m.primeFactors.preimage (fun p : AWS.PrimeIdx => (p : ℕ)) Subtype.val_injective.injOn
  have h : HasProd (gG e m) (∏ p ∈ s, gG e m p) :=
    hasProd_prod_of_ne_finset_one fun p hp => by
      have hnd : ¬ (p : ℕ) ∣ m := fun hd => hp (Finset.mem_preimage.mpr
        (Nat.mem_primeFactors.mpr ⟨p.2, hd, hm⟩))
      rw [gG, Nat.factorization_eq_zero_of_not_dvd hnd]
      simp
  convert h using 1
  rw [sum_divisors_invPow e m hm]
  have e' : ∀ p ∈ s, gG e m p = (fun x : ℕ =>
      ∑ i ∈ Finset.range (m.factorization x + 1), (1 / (x : ℝ) ^ (e + 1)) ^ i) (p : ℕ) :=
    fun p _ => rfl
  rw [Finset.prod_congr rfl e', Finset.prod_preimage (fun p : AWS.PrimeIdx => (p : ℕ)) m.primeFactors
    Subtype.val_injective.injOn (fun x : ℕ =>
      ∑ i ∈ Finset.range (m.factorization x + 1), (1 / (x : ℝ) ^ (e + 1)) ^ i)
    (fun x hx hxr => absurd ⟨⟨x, Nat.prime_of_mem_primeFactors hx⟩, rfl⟩ hxr)]

/-- $n \mapsto n^{-K}$, completely multiplicative. -/
noncomputable def invPowK (K : ℕ) (hK : K ≠ 0) : ℕ →*₀ ℝ where
  toFun n := 1 / (n : ℝ) ^ K
  map_zero' := by simp [hK]
  map_one' := by simp
  map_mul' m n := by simp [mul_pow, mul_comm]

/-- $\zeta(2h) = 2^{2h-1}\pi^{2h}|B_{2h}|/(2h)!$ and the Bernoulli number has the sign making this positive. -/
theorem zeta_even_value (h : ℕ) (hh : h ≠ 0) :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ (2 * h))
      ((2 : ℝ) ^ (2 * h - 1) * Real.pi ^ (2 * h) * |(bernoulli (2 * h) : ℝ)| / (2 * h).factorial) := by
  have H := hasSum_zeta_nat hh
  have hpos : 0 < (-1 : ℝ) ^ (h + 1) * (2 : ℝ) ^ (2 * h - 1) * Real.pi ^ (2 * h) *
        bernoulli (2 * h) / (2 * h).factorial := by
    rw [← H.tsum_eq]
    have hs := H.summable
    refine hs.tsum_pos (fun n => by positivity) 1 ?_
    simp
  have hB : (-1 : ℝ) ^ (h + 1) * (bernoulli (2 * h) : ℝ) = |(bernoulli (2 * h) : ℝ)| := by
    have hp2 : 0 < (2 : ℝ) ^ (2 * h - 1) * Real.pi ^ (2 * h) / (2 * h).factorial := by positivity
    have hp3 : 0 < (-1 : ℝ) ^ (h + 1) * (bernoulli (2 * h) : ℝ) := by
      have e : (-1 : ℝ) ^ (h + 1) * (2 : ℝ) ^ (2 * h - 1) * Real.pi ^ (2 * h) * bernoulli (2 * h) / (2 * h).factorial =
          ((2 : ℝ) ^ (2 * h - 1) * Real.pi ^ (2 * h) / (2 * h).factorial) * ((-1 : ℝ) ^ (h + 1) * bernoulli (2 * h)) := by
        ring
      rw [e] at hpos
      exact (pos_iff_pos_of_mul_pos hpos).mp hp2
    have : |(-1 : ℝ) ^ (h + 1) * (bernoulli (2 * h) : ℝ)| = |(bernoulli (2 * h) : ℝ)| := by
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [← this, abs_of_pos hp3]
  convert H using 2
  rw [← hB]
  ring

/-- The value $\zeta(2h)$. -/
noncomputable def zetaVal (h : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * h - 1) * Real.pi ^ (2 * h) * |(bernoulli (2 * h) : ℝ)| / (2 * h).factorial

theorem zetaVal_pos (h : ℕ) (hh : h ≠ 0) : 0 < zetaVal h := by
  have H := zeta_even_value h hh
  have := H.summable.tsum_pos (fun n => by positivity) 1 (by simp)
  rwa [H.tsum_eq] at this

/-- **Euler product** $\prod_p (1 - p^{-2h}) = \zeta(2h)^{-1}$. -/
theorem hasProd_one_sub_inv_pow (h : ℕ) (hh : h ≠ 0) :
    HasProd (fun p : AWS.PrimeIdx => 1 - 1 / ((p : ℕ) : ℝ) ^ (2 * h)) (zetaVal h)⁻¹ := by
  have hK : 2 * h ≠ 0 := by omega
  have H := zeta_even_value h hh
  have hsn : Summable fun n : ℕ => ‖invPowK (2 * h) hK n‖ := by
    refine H.summable.congr (fun n => ?_)
    show 1 / (n : ℝ) ^ (2 * h) = ‖1 / (n : ℝ) ^ (2 * h)‖
    rw [Real.norm_of_nonneg (by positivity)]
  have hh' := EulerProduct.eulerProduct_completely_multiplicative_hasProd hsn
  have hval : (∑' n : ℕ, invPowK (2 * h) hK n) = zetaVal h := H.tsum_eq
  rw [hval] at hh'
  have h2 := hh'.inv₀ (zetaVal_pos h hh).ne'
  have h3 : HasProd (fun p : Nat.Primes => 1 - 1 / ((p : ℕ) : ℝ) ^ (2 * h)) (zetaVal h)⁻¹ := by
    simpa [invPowK] using h2
  exact h3

/-- The prime $2$ contributes a single constant factor. -/
theorem hasProd_two_factor (c : ℝ) :
    HasProd (fun p : AWS.PrimeIdx => if (p : ℕ) = 2 then c else 1) c := by
  have h : HasProd (fun p : AWS.PrimeIdx => if (p : ℕ) = 2 then c else 1)
      (∏ p ∈ ({⟨2, Nat.prime_two⟩} : Finset AWS.PrimeIdx), if (p : ℕ) = 2 then c else 1) :=
    hasProd_prod_of_ne_finset_one fun p hp => by
      rw [if_neg]
      intro h2; exact hp (Finset.mem_singleton.mpr (Subtype.ext h2))
  rw [Finset.prod_singleton] at h
  simpa using h

/-- The $2$-adic density of $I_{4(j+1)}$ at a positive integer. -/
noncomputable def beta2 (j m : ℕ) : ℝ := localDensity (sumSq (2 * (2 * (j + 1)))) 2 (m : ℤ)

/-- The "naive" factor at $2$: $(1 - 2^{-k})\sum_{i \le v_2(m)}(2^{1-k})^i$. -/
noncomputable def F2 (j m : ℕ) : ℝ :=
  (1 - 1 / (2 : ℝ) ^ (2 * (j + 1))) * ∑ i ∈ Finset.range (m.factorization 2 + 1),
    (1 / (2 : ℝ) ^ (2 * j + 1)) ^ i

theorem F2_pos (j m : ℕ) : 0 < F2 j m := by
  unfold F2
  refine mul_pos ?_ (Finset.sum_pos (fun i _ => by positivity) ⟨0, by simp⟩)
  have : (1 : ℝ) < 2 ^ (2 * (j + 1)) := one_lt_pow₀ (by norm_num) (by omega)
  rw [sub_pos, div_lt_one (by positivity)]
  exact this

theorem eulerFactor_even (j m : ℕ) (hm : m ≠ 0) (p : AWS.PrimeIdx) :
    eulerFactor (sumSq (2 * (2 * (j + 1)))) (m : ℤ) p =
      (if (p : ℕ) = 2 then beta2 j m / F2 j m else 1) *
        ((1 - 1 / ((p : ℕ) : ℝ) ^ (2 * (j + 1))) * gG (2 * j) m p) := by
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  by_cases h2 : (p : ℕ) = 2
  · rw [if_pos h2]
    obtain ⟨p, hp⟩ := p
    simp only at h2
    subst h2
    have : (1 - 1 / ((2 : ℕ) : ℝ) ^ (2 * (j + 1))) * gG (2 * j) m ⟨2, hp⟩ = F2 j m := by
      unfold gG F2; push_cast; rfl
    rw [this, div_mul_cancel₀ _ (F2_pos j m).ne']
    rfl
  · rw [if_neg h2, one_mul]
    show localDensity (sumSq (2 * (2 * (j + 1)))) (p : ℕ) (m : ℤ) = _
    have hm0 : m ≠ 0 := hm
    have hu : ¬ ((p : ℕ) : ℤ) ∣ ((m / (p : ℕ) ^ m.factorization p : ℕ) : ℤ) := by
      exact_mod_cast Nat.not_dvd_ordCompl p.2 hm0
    have e : (m : ℤ) = ((p : ℕ) : ℤ) ^ m.factorization p * ((m / (p : ℕ) ^ m.factorization p : ℕ) : ℤ) := by
      exact_mod_cast (Nat.ordProj_mul_ordCompl_eq_self m p).symm
    rw [e, localDensity_sumSq_even_odd (2 * (j + 1)) ⟨j + 1, by ring⟩ (by omega) (p : ℕ) h2 _ _ hu]
    rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega]
    rfl

/-- **The Euler product of $I_{4(j+1)}$ at $m \ge 1$:**
$\prod_p\beta_p(m) = \dfrac{\beta_2(m)}{F_2}\cdot\zeta(k)^{-1}\sum_{d \mid m}d^{-(k-1)}$, $k = 2(j+1)$. -/
theorem eulerProduct_even (j m : ℕ) (hm : m ≠ 0) :
    eulerProduct (sumSq (2 * (2 * (j + 1)))) (m : ℤ) =
      beta2 j m / F2 j m * ((zetaVal (j + 1))⁻¹ * ∑ d ∈ m.divisors, 1 / (d : ℝ) ^ (2 * j + 1)) := by
  have hall := (hasProd_two_factor (beta2 j m / F2 j m)).mul
    ((hasProd_one_sub_inv_pow (j + 1) (by omega)).mul (hasProd_gG (2 * j) m hm))
  have hfun : eulerFactor (sumSq (2 * (2 * (j + 1)))) (m : ℤ) = fun p : AWS.PrimeIdx =>
      (if (p : ℕ) = 2 then beta2 j m / F2 j m else 1) *
        ((1 - 1 / ((p : ℕ) : ℝ) ^ (2 * (j + 1))) * gG (2 * j) m p) :=
    funext (eulerFactor_even j m hm)
  unfold eulerProduct
  rw [hfun]
  exact hall.tprod_eq

/-! ### The divisor sum -/

theorem negpow_eq (n : ℕ) : (-1 : ℂ) ^ n = if Even n then 1 else -1 := by
  rcases Nat.even_or_odd n with h | h
  · simp [h, h.neg_one_pow]
  · simp [Nat.not_even_iff_odd.mpr h, h.neg_one_pow]

/-- $(-1)^{(d+h)(q-1)} = 1$ for odd $q$ and $(-1)^{d+h}$ for even $q \ne 0$. -/
theorem sign_lemma (d h q : ℕ) (hq : q ≠ 0) :
    (-1 : ℂ) ^ ((d + h) * (q - 1)) = if Odd q then 1 else (-1) ^ (d + h) := by
  rcases Nat.even_or_odd q with he | ho
  · rw [if_neg (Nat.not_odd_iff_even.mpr he)]
    obtain ⟨t, rfl⟩ := he
    have ht : t ≠ 0 := by omega
    have hodd : Odd (t + t - 1) := ⟨t - 1, by omega⟩
    rcases Nat.even_or_odd (d + h) with h1 | h1
    · rw [(h1.mul_right _).neg_one_pow, h1.neg_one_pow]
    · rw [(h1.mul hodd).neg_one_pow, h1.neg_one_pow]
  · rw [if_pos ho]
    obtain ⟨t, rfl⟩ := ho
    rw [show 2 * t + 1 - 1 = 2 * t by omega]
    exact ((even_two_mul t).mul_left _).neg_one_pow

theorem sign_two_pow (a b y u h : ℕ) (hb : b ≤ a) (hy : y ∣ u) (hu : Odd u) :
    (-1 : ℂ) ^ ((2 ^ b * y + h) * (2 ^ a * u / (2 ^ b * y) - 1)) =
      if b = a then 1 else if b = 0 then -(-1) ^ h else (-1) ^ h := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy; subst hy; exact absurd hu (by decide)
  have hyodd : Odd y := Odd.of_dvd_nat hu hy
  obtain ⟨z, rfl⟩ := hy
  have hz : Odd z := by
    rcases Nat.even_or_odd z with he | ho
    · exfalso; exact (Nat.not_even_iff_odd.mpr hu) (Even.mul_left he _)
    · exact ho
  have hz0 : z ≠ 0 := hz.pos.ne'
  have hd0 : 2 ^ b * y ≠ 0 := mul_ne_zero (by positivity) hy0
  have hq : 2 ^ a * (y * z) / (2 ^ b * y) = 2 ^ (a - b) * z := by
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hb
    rw [Nat.add_sub_cancel_left, pow_add]
    have : 2 ^ b * 2 ^ c * (y * z) = (2 ^ b * y) * (2 ^ c * z) := by ring
    rw [this, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
  rw [hq, sign_lemma _ _ _ (mul_ne_zero (by positivity) hz0)]
  by_cases hba : b = a
  · subst hba
    simp only [Nat.sub_self, pow_zero, one_mul, if_true]
    rw [if_pos hz]
  · have hev : ¬ Odd (2 ^ (a - b) * z) := by
      rw [Nat.not_odd_iff_even]
      exact Even.mul_right (by
        have : a - b ≠ 0 := by omega
        exact (Nat.even_pow.mpr ⟨even_two, this⟩)) _
    rw [if_neg hev, if_neg hba, pow_add]
    by_cases hb0 : b = 0
    · subst hb0
      simp only [pow_zero, one_mul, if_true]
      rw [negpow_eq y, if_neg (Nat.not_even_iff_odd.mpr hyodd)]
      ring
    · rw [if_neg hb0, negpow_eq (2 ^ b * y),
        if_pos (Even.mul_right (Nat.even_pow.mpr ⟨even_two, hb0⟩) _)]
      ring

/-- **The divisor sum of Remark 6.5**: for $m = 2^a u$ with $u$ odd and $k = 2(j+1)$,
$\sum_{d \mid m} d^{k-1}(-1)^{(d + k/2)(m/d - 1)} = \sigma_{k-1}(u)\,T_a$. -/
theorem divisorSum_eq (j a u : ℕ) (hu : Odd u) :
    ∑ d ∈ (2 ^ a * u).divisors, (d : ℂ) ^ (2 * (j + 1) - 1) *
        (-1 : ℂ) ^ ((d + 2 * (j + 1) / 2) * ((2 ^ a * u) / d - 1)) =
      (∑ y ∈ u.divisors, (y : ℂ) ^ (2 * j + 1)) *
        (if a = 0 then 1 else ((2 : ℂ) ^ (2 * j + 1)) ^ a +
          (-1) ^ (j + 1) * (∑ b ∈ Finset.range a, ((2 : ℂ) ^ (2 * j + 1)) ^ b - 2)) := by
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, show 2 * (j + 1) / 2 = j + 1 by omega]
  have hcop : (2 ^ a).Coprime u := by
    apply Nat.Coprime.pow_left
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_
    intro h
    exact (Nat.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr h)
  have himg : (2 ^ a * u).divisors =
      Finset.image (fun p : ℕ × ℕ => p.1 * p.2) (Nat.divisors (2 ^ a) ×ˢ Nat.divisors u) := by
    rw [Nat.divisors_mul, Finset.mul_def]
  rw [himg, Finset.sum_image hcop.mul_injOn_divisors, Finset.sum_product,
    Nat.divisors_prime_pow Nat.prime_two, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hterm : ∀ b ∈ Finset.range (a + 1), ∑ y ∈ u.divisors, ((2 ^ b * y : ℕ) : ℂ) ^ (2 * j + 1) *
      (-1 : ℂ) ^ ((2 ^ b * y + (j + 1)) * (2 ^ a * u / (2 ^ b * y) - 1)) =
      (∑ y ∈ u.divisors, (y : ℂ) ^ (2 * j + 1)) * (((2 : ℂ) ^ (2 * j + 1)) ^ b *
        (if b = a then 1 else if b = 0 then -(-1) ^ (j + 1) else (-1) ^ (j + 1))) := by
    intro b hb
    have hb' : b ≤ a := by simpa [Nat.lt_succ_iff] using hb
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [sign_two_pow a b y u (j + 1) hb' (Nat.dvd_of_mem_divisors hy) hu]
    push_cast
    rw [mul_pow, ← pow_mul, mul_comm b (2 * j + 1)]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · rw [if_neg (by omega), Finset.sum_range_succ, if_pos rfl, mul_one]
    have : ∀ b ∈ Finset.range a, ((2 : ℂ) ^ (2 * j + 1)) ^ b *
        (if b = a then 1 else if b = 0 then -(-1) ^ (j + 1) else (-1) ^ (j + 1)) =
        (-1) ^ (j + 1) * (((2 : ℂ) ^ (2 * j + 1)) ^ b) -
          (if b = 0 then 2 * (-1) ^ (j + 1) else 0) := by
      intro b hb
      have hba : b ≠ a := (Finset.mem_range.mp hb).ne
      rw [if_neg hba]
      by_cases hb0 : b = 0
      · subst hb0; simp; ring
      · simp [hb0]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [Finset.sum_ite_eq', Finset.mem_range, ha]
    ring

/-! ### Assembly -/

theorem sigma_split (e a u : ℕ) (hu : Odd u) :
    ∑ d ∈ (2 ^ a * u).divisors, (d : ℝ) ^ e =
      (∑ b ∈ Finset.range (a + 1), ((2 : ℝ) ^ e) ^ b) * ∑ y ∈ u.divisors, (y : ℝ) ^ e := by
  have hcop : (2 ^ a).Coprime u := by
    apply Nat.Coprime.pow_left
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_
    intro h
    exact (Nat.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr h)
  have h := ((ArithmeticFunction.isMultiplicative_sigma (k := e)).map_mul_of_coprime hcop)
  rw [ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply_prime_pow Nat.prime_two,
    ArithmeticFunction.sigma_apply] at h
  have h' := congrArg (Nat.cast : ℕ → ℝ) h
  push_cast at h'
  rw [h']
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← pow_mul, mul_comm]

theorem geom_rev (g : ℝ) (hg : g ≠ 0) (a : ℕ) :
    ∑ b ∈ Finset.range (a + 1), g ^ b = g ^ a * ∑ i ∈ Finset.range (a + 1), (1 / g) ^ i := by
  rw [Finset.mul_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ a := by simpa [Nat.lt_succ_iff] using hi
  have : a + 1 - 1 - i + i = a := by omega
  rw [show a + 1 - 1 - i = a - i by omega, one_div_pow]
  have : g ^ a = g ^ (a - i) * g ^ i := by rw [← pow_add]; congr 1; omega
  rw [this]
  field_simp

theorem factorization_two (a u : ℕ) (hu : Odd u) : (2 ^ a * u).factorization 2 = a := by
  have hu0 : u ≠ 0 := hu.pos.ne'
  rw [Nat.factorization_mul (by positivity) hu0]
  simp only [Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
  have : ¬ 2 ∣ u := fun h => (Nat.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr h)
  rw [Nat.factorization_eq_zero_of_not_dvd this]
  simp

theorem bern_pos (j : ℕ) : 0 < |(bernoulli (2 * (j + 1)) : ℝ)| := by
  rcases (abs_nonneg (bernoulli (2 * (j + 1)) : ℝ)).lt_or_eq with h | h
  · exact h
  · exfalso
    have := zetaVal_pos (j + 1) (by omega)
    unfold zetaVal at this
    rw [← h] at this
    simp at this

/-- **The local product of $I_{4(j+1)}$ in closed form** ($m = 2^a u$, $u$ odd). -/
theorem aE_even (j m a u : ℕ) (hu : Odd u) (hmu : m = 2 ^ a * u) :
    aE (sumSq (2 * (2 * (j + 1)))) (m : ℤ) =
      (2 * (2 * (j + 1)) : ℝ) / (((2 : ℝ) ^ (2 * (j + 1)) - 1) * |(bernoulli (2 * (j + 1)) : ℝ)|) *
        (∑ y ∈ u.divisors, (y : ℝ) ^ (2 * j + 1)) *
        (if a = 0 then 1 else ((2 : ℝ) ^ (2 * j + 1)) ^ a +
          (-1) ^ (j + 1) * (∑ b ∈ Finset.range a, ((2 : ℝ) ^ (2 * j + 1)) ^ b - 2)) := by
  have hu0 : u ≠ 0 := hu.pos.ne'
  have hm : m ≠ 0 := by rw [hmu]; positivity
  have hfac : m.factorization 2 = a := by rw [hmu]; exact factorization_two a u hu
  have hB := bern_pos j
  set g : ℝ := (2 : ℝ) ^ (2 * j + 1) with hg
  have hg0 : 0 < g := by positivity
  have hbeta : beta2 j m * g ^ a =
      (if a = 0 then 1 else g ^ a + (-1) ^ (j + 1) * (∑ b ∈ Finset.range a, g ^ b - 2)) := by
    have h := beta2_pow_mul j a (u : ℤ) (by exact_mod_cast hu)
    have e : (m : ℤ) = 2 ^ a * (u : ℤ) := by rw [hmu]; push_cast; ring
    unfold beta2
    rw [e, h]
    unfold gg ss
    split_ifs with ha
    · subst ha; simp
    · simp only [← hg]
      field_simp
  have hD : (m : ℝ) ^ (2 * j + 1) * ∑ d ∈ m.divisors, 1 / (d : ℝ) ^ (2 * j + 1) =
      (∑ b ∈ Finset.range (a + 1), g ^ b) * ∑ y ∈ u.divisors, (y : ℝ) ^ (2 * j + 1) := by
    have hs := sigma_split (2 * j + 1) a u hu
    rw [← hg] at hs
    rw [← hs, ← hmu, Finset.mul_sum,
      ← Nat.sum_div_divisors m (fun d => (d : ℝ) ^ (2 * j + 1))]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdm := Nat.dvd_of_mem_divisors hd
    have hd0 : d ≠ 0 := by rintro rfl; simp at hdm; exact hm hdm
    rw [Nat.cast_div hdm (by exact_mod_cast hd0), div_pow]
    have : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
    field_simp
  have hS2 : ∑ b ∈ Finset.range (a + 1), g ^ b =
      g ^ a * ∑ i ∈ Finset.range (a + 1), (1 / g) ^ i := geom_rev g hg0.ne' a
  have hF2 : F2 j m = (1 - 1 / (2 : ℝ) ^ (2 * (j + 1))) *
      ∑ i ∈ Finset.range (a + 1), (1 / g) ^ i := by
    unfold F2; rw [hfac]
  rw [aE, aEWith, eulerProduct_even j m hm, betaInf_sumSq (by omega)]
  have hK : ((2 * (2 * (j + 1)) : ℕ) : ℝ) / 2 = ((2 * j + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [hK, add_sub_cancel_right, show ((2 * j + 1 : ℕ) : ℝ) + 1 = ((2 * j + 1 + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, Real.rpow_natCast]
  have hΓ : Real.Gamma ((2 * j + 1 + 1 : ℕ) : ℝ) = ((2 * j + 1 : ℕ).factorial : ℝ) := by
    rw [Nat.cast_succ]; exact Real.Gamma_nat_eq_factorial _
  rw [hΓ]
  have hcast : (((m : ℤ)) : ℝ) = (m : ℝ) := by simp
  rw [hcast, ← hbeta]
  set G2 := ∑ i ∈ Finset.range (a + 1), (1 / g) ^ i with hG2
  set σu := ∑ y ∈ u.divisors, (y : ℝ) ^ (2 * j + 1) with hσu
  set D := ∑ d ∈ m.divisors, 1 / (d : ℝ) ^ (2 * j + 1) with hDdef
  have hG2pos : 0 < G2 := Finset.sum_pos (fun i _ => by positivity) ⟨0, by simp⟩
  have hc0 : (0 : ℝ) < 1 - 1 / (2 : ℝ) ^ (2 * (j + 1)) := by
    have : (1 : ℝ) < 2 ^ (2 * (j + 1)) := one_lt_pow₀ (by norm_num) (by omega)
    rw [sub_pos, div_lt_one (by positivity)]; exact this
  have hz : zetaVal (j + 1) = (2 : ℝ) ^ (2 * j + 1) * Real.pi ^ (2 * j + 1 + 1) *
      |(bernoulli (2 * (j + 1)) : ℝ)| / ((2 * j + 1 + 1 : ℕ).factorial) := by
    unfold zetaVal
    rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
  have hbd : beta2 j m ≠ 0 ∨ True := Or.inr trivial
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hfact : ((2 * j + 1 + 1 : ℕ).factorial : ℝ) = ((2 * j + 1 : ℕ) + 1 : ℝ) * (2 * j + 1 : ℕ).factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hfpos : (0 : ℝ) < ((2 * j + 1 : ℕ).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  calc (m : ℝ) ^ (2 * j + 1) * Real.pi ^ (2 * j + 1 + 1) / ((2 * j + 1 : ℕ).factorial : ℝ) *
        (beta2 j m / F2 j m * ((zetaVal (j + 1))⁻¹ * D))
      = Real.pi ^ (2 * j + 1 + 1) / ((2 * j + 1 : ℕ).factorial : ℝ) * beta2 j m /
          ((1 - 1 / (2 : ℝ) ^ (2 * (j + 1))) * G2) * (zetaVal (j + 1))⁻¹ *
          ((m : ℝ) ^ (2 * j + 1) * D) := by rw [hF2]; ring
    _ = Real.pi ^ (2 * j + 1 + 1) / ((2 * j + 1 : ℕ).factorial : ℝ) * beta2 j m /
          ((1 - 1 / (2 : ℝ) ^ (2 * (j + 1))) * G2) * (zetaVal (j + 1))⁻¹ *
          (g ^ a * G2 * σu) := by rw [hD, hS2]
    _ = _ := by
      rw [hz, hfact]
      push_cast
      have h2 : ((2 : ℝ) ^ (2 * (j + 1))) = 2 * g := by rw [hg]; ring
      rw [h2]
      have hb2 : (2 : ℝ) ^ (2 * j + 1) = g := hg.symm
      rw [hb2]
      have hgne := hg0.ne'
      have hBne := hB.ne'
      have : (2 * g - 1) ≠ 0 := by
        have : (1 : ℝ) ≤ g := one_le_pow₀ (by norm_num)
        intro h; linarith
      have h3 : (1 - 1 / (2 * g)) ≠ 0 := by
        intro h; field_simp at h; linarith [one_le_pow₀ (n := 2 * j + 1) (show (1 : ℝ) ≤ 2 by norm_num)]
      field_simp
      ring

end QuadFormsKB.MorenoWagstaff.Remark65Even060

namespace QuadFormsKB.MorenoWagstaff

open QuadFormsKB.Siegel

/-- **Moreno–Wagstaff, Remark 6.5 (p. 196), every even $k \ge 4$:** for all $n \ge 1$,
$\rho_{2k}(n) = \dfrac{2k}{(2^k - 1)|B_k|}\sum_{d \mid n} d^{k-1}(-1)^{(d + k/2)(n/d - 1)}$. Unconditional. -/
@[kb "morenowagstaff2005" "Remark 6.5, p. 196 (every even k ≥ 4)"]
theorem remark65Even : Remark65Even := by
  intro k n hk h4 hn
  obtain ⟨r, rfl⟩ := hk
  obtain ⟨j, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
  rw [show j + 1 + (j + 1) = 2 * (j + 1) by ring]
  rw [singularSeriesSq_eq_aE (by omega) hn]
  obtain ⟨a, u, hu, hmu⟩ : ∃ a u : ℕ, Odd u ∧ n = 2 ^ a * u :=
    ⟨n.factorization 2, n / 2 ^ n.factorization 2,
      Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Nat.not_dvd_ordCompl Nat.prime_two hn.ne')),
      (Nat.ordProj_mul_ordCompl_eq_self n 2).symm⟩
  subst hmu
  rw [Remark65Even060.aE_even j _ a u hu rfl, Remark65Even060.divisorSum_eq j a u hu]
  split_ifs <;> push_cast <;> ring

end QuadFormsKB.MorenoWagstaff
