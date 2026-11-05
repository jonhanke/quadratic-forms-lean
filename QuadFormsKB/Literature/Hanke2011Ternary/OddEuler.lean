/-
# Hanke 2011 (ternary masses), §3: explicit ternary Euler factors for primes $p \nmid 2$

J. Hanke, *Explicit formulas for masses of ternary quadratic lattices of varying determinant over number fields*,
arXiv:1109.1054 (bib key `hanke2011ternary`), §3, pp. 7–9.

The local Dirichlet series are formal power series in $X := q^{-s}$: the term of $S_{\mathfrak p} = \pi^\nu u$ is
$A^*_{\mathfrak p}(S_{\mathfrak p}) N_{F/\mathbb{Q}}(I(S_{\mathfrak p}))^{-s} = A^*_{\mathfrak p}(S_{\mathfrak p})X^\nu$.
A rational identity $\sum_\nu c_\nu X^\nu = N(X)/D(X)$ is stated in the equivalent multiplied-out form
$\big(\sum_\nu c_\nu X^\nu\big)\cdot D(X) = N(X)$ in `PowerSeries ℚ` ($D$ has constant term $1$, so it is invertible).
Here $q > 1$ is the size of the residue field and `ε'` $= \left(\frac{-1}{\mathfrak p}\right)$.

* `identity_7`: the paper's identity (7), $\sum_{\nu}\sum_{a+b=\nu,\ 0\le a\le b} q^{-(2a+b)}X^\nu =
  \frac{1}{(1-q^{-1}X)(1-q^{-3}X^2)}$.
* `lemma_3_1`: $\sum_\nu A^*_{\mathfrak p}(\pi^\nu u)X^\nu = \dfrac{1-q^{-6}X^3}{(1-q^{-1}X)(1-q^{-3}X^2)}$.
* `lemma_3_2`: $\sum_\nu B^*_{\mathfrak p}(\pi^\nu u)X^\nu = \dfrac{1+\varepsilon'q^{-2}X+q^{-4}X^2}{1-q^{-2}X^2}$.
* `lemma_3_3_A`, `lemma_3_3_B`: the same for the Euler factors, with an arbitrary unit part in each degree.
-/
import QuadFormsKB.Literature.Hanke2011Ternary.OddPrimes

namespace QuadFormsKB.Hanke2011Ternary

open PowerSeries Finset

/-- The geometric series $\sum_m c^m X^{km}$ (as `spread`). -/
noncomputable abbrev geom (k : ℕ) (c : ℚ) : PowerSeries ℚ := spread k fun m => c ^ m

theorem geom_mul (k : ℕ) (hk : 0 < k) (c : ℚ) : geom k c * (1 - C c * X ^ k) = 1 :=
  spread_geom_mul k hk c

theorem mk_pow_eq_geom (c : ℚ) : PowerSeries.mk (fun d => c ^ d) = geom 1 c := by
  rw [geom, spread_one]

theorem geom_sub_one (k : ℕ) (c : ℚ) : spread k (fun m => if m = 0 then 0 else c ^ m) = geom k c - 1 := by
  rw [spread_sub_const, pow_zero, map_one]

theorem mk_sub_one (c : ℚ) : PowerSeries.mk (fun d => if d = 0 then 0 else c ^ d) = geom 1 c - 1 := by
  rw [← geom_sub_one, spread_one]

/-- **Identity (7)** (Hanke 2011, p. 7): the Ferrers diagram identity
$$\sum_{\nu' \ge 0}\ \sum_{\substack{0 \le a' \le b'\\ a'+b' = \nu'}} q^{-(2a'+b')} X^{\nu'}
  = \frac{1}{1 - q^{-1}X}\cdot\frac{1}{1 - q^{-3}X^2},$$
in multiplied-out form. -/
@[kb "hanke2011ternary" "§3, proof of Lemma 3.1, (7), p. 7"]
theorem identity_7 (q : ℚ) :
    PowerSeries.mk (fun ν => ∑ ab ∈ (antidiagonal ν).filter (fun ab => ab.1 ≤ ab.2), q⁻¹ ^ (2 * ab.1 + ab.2)) *
      ((1 - C q⁻¹ * X) * (1 - C (q⁻¹ ^ 3) * X ^ 2)) = 1 := by
  rw [mk_sum_le_eq (fun a b => q⁻¹ ^ (2 * a + b)) (fun a => (q⁻¹ ^ 3) ^ a) (fun d => q⁻¹ ^ d)
    (fun a d => by rw [← pow_mul, ← pow_add]; ring_nf)]
  rw [mk_pow_eq_geom]
  have h1 := geom_mul 1 one_pos q⁻¹
  have h2 := geom_mul 2 two_pos (q⁻¹ ^ 3)
  rw [pow_one] at h1
  linear_combination (geom 1 q⁻¹ * (1 - C q⁻¹ * X)) * h2 + h1

/-- The $A^*$ row of Table 2 in the variables $(a, d)$, $b = a + d$:
$q^{-3a}q^{-d} - q^{-2}\,[a \ge 1]q^{-3a}\,[d \ge 1]q^{-d}$. -/
theorem rowA_eq (q : ℚ) (a d : ℕ) :
    rowA q a (a + d) = (q⁻¹ ^ 3) ^ a * q⁻¹ ^ d -
      q⁻¹ ^ 2 * ((if a = 0 then 0 else (q⁻¹ ^ 3) ^ a) * (if d = 0 then 0 else q⁻¹ ^ d)) := by
  unfold rowA
  rcases Nat.eq_zero_or_pos a with rfl | ha <;> rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · simp [show d ≠ 0 by omega]
  · simp [show a ≠ 0 by omega, ← pow_mul]
  · simp only [show a ≠ 0 by omega, show d ≠ 0 by omega, show a + d ≠ 0 by omega, show a ≠ a + d by omega,
      false_and, and_false, if_false]
    rw [← pow_mul, show 2 * a + (a + d) = 3 * a + d by ring, pow_add, mul_comm 3 a]
    ring

/-- **Lemma 3.1** (Hanke 2011, p. 7): for $\mathfrak p \nmid 2$ and a fixed unit square class $u$,
$$\sum_{\substack{S_{\mathfrak p} \in \mathrm{SqCl}(F_{\mathfrak p}^\times, \mathcal O_{\mathfrak p}^\times)\\
\widetilde S_{\mathfrak p} = u}} \frac{A^*_{\mathfrak p;3}(S_{\mathfrak p})}{N_{F/\mathbb{Q}}(I(S_{\mathfrak p}))^s}
= \frac{1 - q^{-(3s+6)}}{(1 - q^{-(s+1)})(1 - q^{-(2s+3)})},$$
i.e. with $X = q^{-s}$ and $S_{\mathfrak p} = \pi^\nu u$:
$\big(\sum_\nu A^*_{\mathfrak p}(\pi^\nu u) X^\nu\big)(1 - q^{-1}X)(1 - q^{-3}X^2) = 1 - q^{-6}X^3$. -/
@[kb "hanke2011ternary" "§3, Lemma 3.1, p. 7"]
theorem lemma_3_1 {q : ℚ} (hq : 1 < q) (ε' u : ℤˣ) :
    PowerSeries.mk (fun ν => Astar q ε' ν u) * ((1 - C q⁻¹ * X) * (1 - C (q⁻¹ ^ 3) * X ^ 2)) =
      1 - C (q⁻¹ ^ 6) * X ^ 3 := by
  have e1 := mk_sum_le_eq (fun a b => (q⁻¹ ^ 3) ^ a * q⁻¹ ^ (b - a)) (fun a => (q⁻¹ ^ 3) ^ a)
    (fun d => q⁻¹ ^ d) (fun a d => by rw [Nat.add_sub_cancel_left])
  have e2 := mk_sum_le_eq (fun a b => (if a = 0 then 0 else (q⁻¹ ^ 3) ^ a) *
      (if b - a = 0 then 0 else q⁻¹ ^ (b - a)))
    (fun a => if a = 0 then 0 else (q⁻¹ ^ 3) ^ a) (fun d => if d = 0 then 0 else q⁻¹ ^ d)
    (fun a d => by rw [Nat.add_sub_cancel_left])
  have hA : PowerSeries.mk (fun ν => Astar q ε' ν u) =
      (spread 2 fun a => (q⁻¹ ^ 3) ^ a) * PowerSeries.mk (fun d => q⁻¹ ^ d) -
        C (q⁻¹ ^ 2) * ((spread 2 fun a => if a = 0 then 0 else (q⁻¹ ^ 3) ^ a) *
          PowerSeries.mk (fun d => if d = 0 then 0 else q⁻¹ ^ d)) := by
    rw [← e1, ← e2]
    ext ν
    rw [map_sub, coeff_C_mul]
    simp only [coeff_mk]
    rw [Astar_eq_sum hq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ab hab => ?_
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (mem_filter.mp hab).2
    rw [hd, rowA_eq, Nat.add_sub_cancel_left]
  rw [hA, geom_sub_one, mk_sub_one, mk_pow_eq_geom]
  have h1 := geom_mul 1 one_pos q⁻¹
  have h2 := geom_mul 2 two_pos (q⁻¹ ^ 3)
  rw [pow_one] at h1
  simp only [map_pow] at h1 h2 ⊢
  set T := C q⁻¹
  set G1 := geom 1 q⁻¹
  set G2 := geom 2 (q⁻¹ ^ 3)
  linear_combination (G1 * (1 - T * X) - T ^ 2 * (G1 * (1 - T * X) - (1 - T * X))) * h2 +
    (1 - T ^ 2 * (1 - (1 - T ^ 3 * X ^ 2))) * h1

/-- The $B^*$ row of Table 2 in the variables $(a, d)$, $b = a + d$, as a sum of four products
$\delta_0(a)\psi_B(d) + \varphi_B(a)\delta_0(d) - \delta_0(a)\delta_0(d) + (1-q^{-2})P(a)Q(d)$. -/
theorem rowB_eq (q : ℚ) (ε' : ℤˣ) (a d : ℕ) :
    rowB q ε' a (a + d) =
      (if a = 0 then 1 else 0) * (if Even d then q⁻¹ ^ d else (ε' : ℤ) * q⁻¹ ^ (d + 1)) +
      (if Even a then q⁻¹ ^ (3 * a) else q⁻¹ ^ (3 * a + 1)) * (if d = 0 then 1 else 0) -
      (if a = 0 then 1 else 0) * (if d = 0 then 1 else 0) +
      (1 - q⁻¹ ^ 2) * ((if a = 0 then 0 else if Even a then q⁻¹ ^ (3 * a) else 0) *
        (if d = 0 then 0 else if Even d then q⁻¹ ^ d else 0)) := by
  unfold rowB
  rcases Nat.eq_zero_or_pos a with rfl | ha <;> rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · simp [show d ≠ 0 by omega]
  · simp [show a ≠ 0 by omega]
  · simp only [show a ≠ 0 by omega, show d ≠ 0 by omega, show a + d ≠ 0 by omega, show a ≠ a + d by omega,
      false_and, and_false, if_false, zero_mul, mul_zero, add_zero, zero_add, sub_zero]
    rw [show 2 * a + (a + d) = 3 * a + d by ring]
    by_cases h1 : Even a <;> by_cases h2 : Even d
    · rw [if_pos ⟨h1, (Nat.even_add.mpr (iff_of_true h1 h2))⟩, if_pos h1, if_pos h2, pow_add] <;> ring
    · rw [if_neg (fun h => h2 ((Nat.even_add.mp h.2).mp h1)), if_pos h1, if_neg h2] <;> ring
    · rw [if_neg (fun h => h1 h.1), if_neg h1] <;> ring
    · rw [if_neg (fun h => h1 h.1), if_neg h1] <;> ring

/-- $\sum_d \psi_B(d)X^d = (1 + \varepsilon' q^{-2}X)\sum_m q^{-2m}X^{2m}$. -/
theorem mk_psiB (q : ℚ) (ε' : ℤˣ) :
    PowerSeries.mk (fun d => if Even d then q⁻¹ ^ d else (ε' : ℤ) * q⁻¹ ^ (d + 1)) =
      (1 + C ((ε' : ℤ) * q⁻¹ ^ 2) * X) * geom 2 (q⁻¹ ^ 2) := by
  ext d
  rw [add_mul, one_mul, map_add, mul_assoc, coeff_C_mul, coeff_mk]
  rcases d with _ | d
  · simp [geom, coeff_spread]
  · rw [coeff_succ_X_mul, geom, coeff_spread, coeff_spread]
    rcases Nat.even_or_odd (d + 1) with h | h
    · have hd : ¬ Even d := by rw [Nat.even_add_one] at h; exact h
      rw [if_pos h, if_pos (even_iff_two_dvd.mp h), if_neg (fun h' => hd (even_iff_two_dvd.mpr h')), mul_zero,
        add_zero, ← pow_mul, Nat.mul_div_cancel' (even_iff_two_dvd.mp h)]
    · have hd : Even d := by rw [Nat.odd_add_one] at h; exact Nat.not_odd_iff_even.mp h
      rw [if_neg (Nat.not_even_iff_odd.mpr h), if_neg (fun h' => (Nat.not_even_iff_odd.mpr h)
        (even_iff_two_dvd.mpr h')), if_pos (even_iff_two_dvd.mp hd), zero_add, ← pow_mul,
        Nat.mul_div_cancel' (even_iff_two_dvd.mp hd), mul_assoc, ← pow_add, add_comm 2 d]

/-- $\sum_a \varphi_B(a)X^{2a} = (1 + q^{-4}X^2)\sum_m q^{-6m}X^{4m}$. -/
theorem spread_phiB (q : ℚ) :
    spread 2 (fun a => if Even a then q⁻¹ ^ (3 * a) else q⁻¹ ^ (3 * a + 1)) =
      (1 + C (q⁻¹ ^ 4) * X ^ 2) * geom 4 (q⁻¹ ^ 6) := by
  have hsplit : (fun a => if Even a then q⁻¹ ^ (3 * a) else q⁻¹ ^ (3 * a + 1)) =
      (fun a => if 2 ∣ a then (q⁻¹ ^ 6) ^ (a / 2) else 0) +
      (fun a => if a = 0 then 0 else (fun m => if 2 ∣ m then q⁻¹ ^ 4 * (q⁻¹ ^ 6) ^ (m / 2) else 0) (a - 1)) := by
    funext a
    simp only [Pi.add_apply]
    rcases Nat.even_or_odd a with h | h
    · obtain ⟨k, rfl⟩ := h
      have hk : 2 ∣ k + k := ⟨k, by ring⟩
      rw [if_pos ⟨k, rfl⟩, if_pos hk]
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp
      · rw [if_neg (by omega), if_neg (fun h => by omega), add_zero, ← pow_mul,
          show (k + k) / 2 = k by omega]; ring_nf
    · obtain ⟨k, rfl⟩ := h
      rw [if_neg (Nat.not_even_iff_odd.mpr ⟨k, rfl⟩), if_neg (fun h => by omega), zero_add, if_neg (by omega),
        Nat.add_sub_cancel, if_pos ⟨k, rfl⟩, Nat.mul_div_cancel_left _ two_pos, ← pow_mul, ← pow_add]
      ring_nf
  rw [hsplit, spread_add,
    spread_shift 2 two_pos (fun m => if 2 ∣ m then q⁻¹ ^ 4 * (q⁻¹ ^ 6) ^ (m / 2) else 0),
    spread_spread 2 2 two_pos two_pos (fun m => (q⁻¹ ^ 6) ^ m),
    spread_spread 2 2 two_pos two_pos (fun m => q⁻¹ ^ 4 * (q⁻¹ ^ 6) ^ m), spread_smul]
  simp only [geom]
  ring

/-- $\sum_a P(a)X^{2a}$ with $P(a) = [a\ \text{even}]q^{-3a}$ is $\sum_m q^{-6m}X^{4m}$. -/
theorem spread_P (q : ℚ) :
    spread 2 (fun a => if a = 0 then 0 else if Even a then q⁻¹ ^ (3 * a) else 0) = geom 4 (q⁻¹ ^ 6) - 1 := by
  have : (fun a => if a = 0 then 0 else if Even a then q⁻¹ ^ (3 * a) else 0) =
      fun a => if a = 0 then 0 else (fun a => if 2 ∣ a then (q⁻¹ ^ 6) ^ (a / 2) else 0) a := by
    funext a
    by_cases h0 : a = 0
    · simp [h0]
    · simp only [h0, if_false]
      by_cases h1 : Even a
      · obtain ⟨k, rfl⟩ := h1
        rw [if_pos ⟨k, rfl⟩, if_pos ⟨k, by ring⟩, show (k + k) / 2 = k by omega, ← pow_mul]
        congr 1; ring
      · rw [if_neg h1, if_neg (fun h => h1 (even_iff_two_dvd.mpr h))]
  rw [this, spread_sub_const, spread_spread 2 2 two_pos two_pos]
  simp

/-- $\sum_d Q(d)X^{d}$ with $Q(d) = [d \ge 1,\ d\ \text{even}]q^{-d}$ is $\sum_m q^{-2m}X^{2m} - 1$. -/
theorem mk_Q (q : ℚ) :
    PowerSeries.mk (fun d => if d = 0 then 0 else if Even d then q⁻¹ ^ d else 0) = geom 2 (q⁻¹ ^ 2) - 1 := by
  have : (fun d => if d = 0 then 0 else if Even d then q⁻¹ ^ d else 0) =
      fun d => if d = 0 then 0 else (fun d => if 2 ∣ d then (q⁻¹ ^ 2) ^ (d / 2) else 0) d := by
    funext d
    by_cases h0 : d = 0
    · simp [h0]
    · simp only [h0, if_false]
      by_cases h1 : Even d
      · obtain ⟨k, rfl⟩ := h1
        rw [if_pos ⟨k, rfl⟩, if_pos ⟨k, by ring⟩, show (k + k) / 2 = k by omega, ← pow_mul]
        congr 1; ring
      · rw [if_neg h1, if_neg (fun h => h1 (even_iff_two_dvd.mpr h))]
  rw [this, ← spread_one, spread_sub_const, spread_spread 1 2 one_pos two_pos]
  simp

/-- **Lemma 3.2** (Hanke 2011, p. 8): for $\mathfrak p \nmid 2$ and a fixed unit square class $u$,
$$\sum_{\substack{S_{\mathfrak p}\\ \widetilde S_{\mathfrak p} = u}}
\frac{B^*_{\mathfrak p;3}(S_{\mathfrak p})}{N_{F/\mathbb{Q}}(I(S_{\mathfrak p}))^s}
= \frac{1 + \varepsilon' q^{-(s+2)} + q^{-(2s+4)}}{1 - q^{-(2s+2)}},
\qquad \varepsilon' = \left(\tfrac{-1}{\mathfrak p}\right),$$
i.e. with $X = q^{-s}$: $\big(\sum_\nu B^*_{\mathfrak p}(\pi^\nu u)X^\nu\big)(1 - q^{-2}X^2)
= 1 + \varepsilon'q^{-2}X + q^{-4}X^2$. -/
@[kb "hanke2011ternary" "§3, Lemma 3.2, p. 8"]
theorem lemma_3_2 {q : ℚ} (hq : 1 < q) (ε' u : ℤˣ) :
    PowerSeries.mk (fun ν => Bstar q ε' ν u) * (1 - C (q⁻¹ ^ 2) * X ^ 2) =
      1 + C ((ε' : ℤ) * q⁻¹ ^ 2) * X + C (q⁻¹ ^ 4) * X ^ 2 := by
  set ψB : ℕ → ℚ := fun d => if Even d then q⁻¹ ^ d else (ε' : ℤ) * q⁻¹ ^ (d + 1)
  set φB : ℕ → ℚ := fun a => if Even a then q⁻¹ ^ (3 * a) else q⁻¹ ^ (3 * a + 1)
  set δ : ℕ → ℚ := fun a => if a = 0 then 1 else 0
  set P : ℕ → ℚ := fun a => if a = 0 then 0 else if Even a then q⁻¹ ^ (3 * a) else 0
  set Q : ℕ → ℚ := fun d => if d = 0 then 0 else if Even d then q⁻¹ ^ d else 0
  have hB : PowerSeries.mk (fun ν => Bstar q ε' ν u) =
      spread 2 δ * PowerSeries.mk ψB + spread 2 φB * PowerSeries.mk δ - spread 2 δ * PowerSeries.mk δ +
        C (1 - q⁻¹ ^ 2) * (spread 2 P * PowerSeries.mk Q) := by
    rw [← mk_sum_le_eq (fun a b => δ a * ψB (b - a)) δ ψB (fun a d => by rw [Nat.add_sub_cancel_left]),
      ← mk_sum_le_eq (fun a b => φB a * δ (b - a)) φB δ (fun a d => by rw [Nat.add_sub_cancel_left]),
      ← mk_sum_le_eq (fun a b => δ a * δ (b - a)) δ δ (fun a d => by rw [Nat.add_sub_cancel_left]),
      ← mk_sum_le_eq (fun a b => P a * Q (b - a)) P Q (fun a d => by rw [Nat.add_sub_cancel_left])]
    ext ν
    rw [map_add, map_sub, map_add, coeff_C_mul]
    simp only [coeff_mk]
    rw [Bstar_eq_sum hq, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ab hab => ?_
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (mem_filter.mp hab).2
    rw [hd, rowB_eq, Nat.add_sub_cancel_left]
  have hδ : spread 2 δ = 1 := spread_single_zero 2 two_pos
  have hδ1 : PowerSeries.mk δ = 1 := by rw [← spread_one]; exact spread_single_zero 1 one_pos
  rw [hB, hδ, hδ1, mk_psiB, spread_phiB, spread_P, mk_Q]
  have h2 := geom_mul 2 two_pos (q⁻¹ ^ 2)
  have h4 := geom_mul 4 (by norm_num) (q⁻¹ ^ 6)
  set G2 := geom 2 (q⁻¹ ^ 2)
  set G4 := geom 4 (q⁻¹ ^ 6)
  have hD4 : (1 - C (q⁻¹ ^ 6) * X ^ 4 : PowerSeries ℚ) ≠ 0 := by
    intro h; have := congrArg (constantCoeff) h; simp at this
  apply mul_right_cancel₀ hD4
  simp only [map_pow, map_mul, map_sub, map_one] at h2 h4 ⊢
  set T := C q⁻¹
  set E := C ((ε' : ℤ) : ℚ)
  linear_combination ((1 - T ^ 6 * X ^ 4) * (1 + E * T ^ 2 * X) + (1 - T ^ 2) * (T ^ 6 * X ^ 4)) * h2 +
    ((1 - T ^ 2 * X ^ 2) * (1 + T ^ 4 * X ^ 2) + (1 - T ^ 2) * (G2 * (1 - T ^ 2 * X ^ 2) - (1 - T ^ 2 * X ^ 2))) * h4

/-- **Lemma 3.3, $A^*$** (Hanke 2011, p. 9): the Euler factor at $\mathfrak p \nmid 2$ of $D_{A^*,\lambda;3}(s)$,
$\sum_{\nu\ge0} A^*_{\mathfrak p}(S_{\mathfrak p}^\nu)N(I(S_{\mathfrak p}^\nu))^{-s}$ with
$S_{\mathfrak p}^\nu = S(\mathfrak p)^\nu$, equals $\dfrac{1 - q^{-(3s+6)}}{(1-q^{-(s+1)})(1-q^{-(2s+3)})}$; the
unit part `uν ν` of $S(\mathfrak p)^\nu$ is arbitrary, since $A^*_{\mathfrak p}$ depends only on $\nu$. -/
@[kb "hanke2011ternary" "§3, Lemma 3.3, p. 9"]
theorem lemma_3_3_A {q : ℚ} (hq : 1 < q) (ε' : ℤˣ) (uν : ℕ → ℤˣ) :
    PowerSeries.mk (fun ν => Astar q ε' ν (uν ν)) * ((1 - C q⁻¹ * X) * (1 - C (q⁻¹ ^ 3) * X ^ 2)) =
      1 - C (q⁻¹ ^ 6) * X ^ 3 := by
  have : (fun ν => Astar q ε' ν (uν ν)) = fun ν => Astar q ε' ν 1 := by
    funext ν; rw [Astar_eq_sum hq, Astar_eq_sum hq]
  rw [this]; exact lemma_3_1 hq ε' 1

/-- **Lemma 3.3, $B^*$** (Hanke 2011, p. 9): the Euler factor at $\mathfrak p \nmid 2$ of $D_{B^*,\lambda;3}(s)$
equals $\dfrac{1 + \varepsilon'q^{-(s+2)} + q^{-(2s+4)}}{1 - q^{-(2s+2)}}$, for any unit parts `uν ν`. -/
@[kb "hanke2011ternary" "§3, Lemma 3.3, p. 9"]
theorem lemma_3_3_B {q : ℚ} (hq : 1 < q) (ε' : ℤˣ) (uν : ℕ → ℤˣ) :
    PowerSeries.mk (fun ν => Bstar q ε' ν (uν ν)) * (1 - C (q⁻¹ ^ 2) * X ^ 2) =
      1 + C ((ε' : ℤ) * q⁻¹ ^ 2) * X + C (q⁻¹ ^ 4) * X ^ 2 := by
  have : (fun ν => Bstar q ε' ν (uν ν)) = fun ν => Bstar q ε' ν 1 := by
    funext ν; rw [Bstar_eq_sum hq, Bstar_eq_sum hq]
  rw [this]; exact lemma_3_2 hq ε' 1

end QuadFormsKB.Hanke2011Ternary
