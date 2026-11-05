/-
# Hanke 2011 (ternary masses), §6: the ternary Euler factors at $\mathfrak p \mid 2$, $F_{\mathfrak p} = \mathbb{Q}_2$

J. Hanke, *Explicit formulas for masses of ternary quadratic lattices of varying determinant over number fields*,
arXiv:1109.1054 (bib key `hanke2011ternary`), §6, pp. 22–25.

The local Dirichlet series are formal power series in $X := 2^{-s}$, with the term of $S_{\mathfrak p}$ of Hessian
valuation $h$ equal to (value)$\cdot X^h$ (`DyadicTables.lean`). Rational identities are stated multiplied out, as in
`OddEuler.lean`.

* `lemma_6_1`: $\sum_h A^*_{\mathfrak p}(2^h u)X^h = \dfrac{(1 - 2^{-6}X^3)\,X}{(1 - 2^{-1}X)(1 - 2^{-3}X^2)}$.
* `lemma_6_2`: $\sum_h B^*_{\mathfrak p}(2^h u)X^h = \dfrac{-\varepsilon_u(1 + 2^{-2}X + 2^{-4}X^2)\,X}{1 - 2^{-2}X^2}$,
  $\varepsilon_u = (-1,u)_2$.
* `lemma_6_4_A`, `lemma_6_4_B`: the Euler factors for a distinguished family, $S_{\mathfrak p^\nu} = \lambda(\mathfrak p)^\nu$,
  with $\varepsilon_{\mathfrak p} := (-1, \lambda(\mathfrak p))_{\mathfrak p}$; the unit part of
  $\lambda(\mathfrak p)^h$ then has $\varepsilon_{u_h} = \varepsilon_{\mathfrak p}^h$ (since $(-1, 2)_2 = 1$).
  *Clarification (proposed by the formalization, not yet confirmed by the author):* the paper writes
  $\varepsilon_{\mathfrak p} := (-1, S_{\mathfrak p})_{\mathfrak p}$ with $S_{\mathfrak p} = \lambda(\mathfrak p^\nu)$, which
  depends on $\nu$; the formula holds with $S_{\mathfrak p} = \lambda(\mathfrak p)$ (the case $\nu = 1$).
-/
import QuadFormsKB.Literature.Hanke2011Ternary.DyadicTables
import QuadFormsKB.Literature.Hanke2011Ternary.OddEuler

namespace QuadFormsKB.Hanke2011Ternary

open PowerSeries Finset

/-! ### Helper lemmas (not part of the paper's statements) -/

theorem mk_add' (f g : ℕ → ℚ) :
    PowerSeries.mk (fun h => f h + g h) = PowerSeries.mk f + PowerSeries.mk g := by
  ext n; simp

theorem mk_single (h₀ : ℕ) (v : ℚ) : PowerSeries.mk (single h₀ v) = C v * X ^ h₀ := by
  ext n
  rw [coeff_mk, coeff_C_mul, coeff_X_pow]
  simp only [single]
  by_cases h : n = h₀ <;> simp [h]


theorem spread_split (k : ℕ) (hk : 0 < k) (g : ℕ → ℚ) :
    spread k g = spread (2 * k) (fun i => g (2 * i)) + X ^ k * spread (2 * k) (fun i => g (2 * i + 1)) := by
  ext n
  rw [map_add, coeff_X_pow_mul', coeff_spread, coeff_spread, coeff_spread]
  have hk2 : 0 < 2 * k := by omega
  by_cases h1 : k ∣ n
  · obtain ⟨a, rfl⟩ := h1
    rw [if_pos (dvd_mul_right k a), Nat.mul_div_cancel_left _ hk]
    rcases Nat.even_or_odd' a with ⟨i, rfl | rfl⟩
    · have e1 : k * (2 * i) = 2 * k * i := by ring
      rw [e1, if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hk2]
      have : ¬ (k ≤ 2 * k * i ∧ 2 * k ∣ 2 * k * i - k) := by
        rintro ⟨hle, m, hm⟩
        have h3 : k * (2 * i) = k * (2 * m + 1) := by
          have : 2 * k * i = 2 * k * m + k := by omega
          nlinarith
        have := Nat.eq_of_mul_eq_mul_left hk h3
        omega
      by_cases hle : k ≤ 2 * k * i
      · rw [if_pos hle, if_neg (fun hd => this ⟨hle, hd⟩)]; simp
      · rw [if_neg hle]; simp
    · have e1 : k * (2 * i + 1) = 2 * k * i + k := by ring
      have hn : ¬ 2 * k ∣ k * (2 * i + 1) := by
        rintro ⟨m, hm⟩
        have h3 : k * (2 * i + 1) = k * (2 * m) := by rw [hm]; ring
        have := Nat.eq_of_mul_eq_mul_left hk h3
        omega
      have hle : k ≤ k * (2 * i + 1) := by rw [e1]; omega
      have e2 : k * (2 * i + 1) - k = 2 * k * i := by rw [e1]; omega
      rw [if_neg hn, if_pos hle, e2, if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hk2]
      simp
  · have h2 : ¬ 2 * k ∣ n := fun h => h1 (Dvd.dvd.trans (dvd_mul_left k 2) h)
    rw [if_neg h1, if_neg h2]
    by_cases hle : k ≤ n
    · rw [if_pos hle]
      have : ¬ 2 * k ∣ n - k := fun h =>
        h1 ((Nat.dvd_sub_iff_left hle (dvd_refl k)).mp (Dvd.dvd.trans (dvd_mul_left k 2) h))
      rw [if_neg this]; simp
    · rw [if_neg hle]; simp


theorem family_coeff (k m b₀ : ℕ) (hk : 0 < k) (hOf : ℕ → ℕ) (hO : ∀ b, hOf b = k * b + m)
    (val : ℕ → ℚ) (h : ℕ) :
    family b₀ hOf val h =
      if k * b₀ + m ≤ h ∧ k ∣ (h - (k * b₀ + m)) then val (b₀ + (h - (k * b₀ + m)) / k) else 0 := by
  unfold family
  by_cases hc : k * b₀ + m ≤ h ∧ k ∣ (h - (k * b₀ + m))
  · rw [if_pos hc]
    obtain ⟨hle, j, hj⟩ := hc
    have hj' : (h - (k * b₀ + m)) / k = j := by rw [hj]; exact Nat.mul_div_cancel_left _ hk
    rw [hj']
    have hh : h = k * (b₀ + j) + m := by rw [mul_add]; omega
    rw [Finset.sum_eq_single (b₀ + j)]
    · rw [if_pos ⟨by omega, by rw [hO]; omega⟩]
    · intro b _ hb
      rw [if_neg]
      rintro ⟨_, h2⟩
      rw [hO] at h2
      apply hb
      have : k * b = k * (b₀ + j) := by omega
      exact Nat.eq_of_mul_eq_mul_left hk this
    · intro hn
      exfalso; apply hn
      rw [Finset.mem_range]
      have : b₀ + j ≤ k * (b₀ + j) := Nat.le_mul_of_pos_left _ hk
      omega
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    rintro ⟨h1, h2⟩
    rw [hO] at h2
    apply hc
    refine ⟨by nlinarith, b - b₀, ?_⟩
    have : k * (b - b₀) = k * b - k * b₀ := Nat.mul_sub _ _ _
    omega

theorem mk_family (k m b₀ : ℕ) (hk : 0 < k) (hOf : ℕ → ℕ) (hO : ∀ b, hOf b = k * b + m)
    (val : ℕ → ℚ) :
    PowerSeries.mk (family b₀ hOf val) = X ^ (k * b₀ + m) * spread k (fun j => val (b₀ + j)) := by
  ext h
  rw [coeff_mk, family_coeff k m b₀ hk hOf hO, coeff_X_pow_mul', coeff_spread]
  by_cases h1 : k * b₀ + m ≤ h
  · by_cases h2 : k ∣ h - (k * b₀ + m) <;> simp [h1, h2]
  · simp [h1]

theorem mk_family_geom2 (k m b₀ : ℕ) (hk : 0 < k) (hOf : ℕ → ℕ) (hO : ∀ b, hOf b = k * b + m)
    (val : ℕ → ℚ) (c₀ c₁ r : ℚ) (h0 : ∀ i, val (b₀ + 2 * i) = c₀ * r ^ i)
    (h1 : ∀ i, val (b₀ + (2 * i + 1)) = c₁ * r ^ i) :
    PowerSeries.mk (family b₀ hOf val) =
      C c₀ * X ^ (k * b₀ + m) * spread (2 * k) (fun i => r ^ i) +
      C c₁ * X ^ (k * b₀ + m + k) * spread (2 * k) (fun i => r ^ i) := by
  rw [mk_family k m b₀ hk hOf hO, spread_split k hk]
  simp only [h0, h1, spread_smul]
  rw [pow_add]
  ring

theorem mk_family_geom (k m b₀ : ℕ) (hk : 0 < k) (hOf : ℕ → ℕ) (hO : ∀ b, hOf b = k * b + m)
    (val : ℕ → ℚ) (c r : ℚ) (h0 : ∀ i, val (b₀ + i) = c * r ^ i) :
    PowerSeries.mk (family b₀ hOf val) = C c * X ^ (k * b₀ + m) * spread k (fun i => r ^ i) := by
  rw [mk_family k m b₀ hk hOf hO]
  simp only [h0, spread_smul]
  ring


theorem family20_coeff (val : ℕ → ℕ → ℚ) (h : ℕ) :
    family20 val h =
      if 12 ≤ h then
        ∑ a ∈ (range (h - 12 + 1)).filter (fun a => 2 * a ≤ h - 12), val (3 + a) (a + 6 + (h - 12 - 2 * a))
      else 0 := by
  unfold family20
  have inner : ∀ b ∈ range (h + 1), (∑ c ∈ range (h + 1), if 3 ≤ b ∧ b + 3 ≤ c ∧ b + c + 3 = h then val b c else 0)
      = if 3 ≤ b ∧ b + 3 ≤ h - b - 3 ∧ b + (h - b - 3) + 3 = h then val b (h - b - 3) else 0 := by
    intro b hb
    rw [Finset.sum_eq_single (h - b - 3)]
    · intro c _ hc
      rw [if_neg]
      rintro ⟨_, _, h3⟩
      omega
    · intro hn; exfalso; apply hn; rw [Finset.mem_range]; omega
  rw [Finset.sum_congr rfl inner]
  by_cases h12 : 12 ≤ h
  · rw [if_pos h12, Finset.sum_ite, Finset.sum_const_zero, add_zero]
    refine Finset.sum_nbij' (fun b => b - 3) (fun a => a + 3) ?_ ?_ ?_ ?_ ?_
    · intro b hb
      simp only [mem_filter, mem_range] at hb ⊢
      omega
    · intro a ha
      simp only [mem_filter, mem_range] at ha ⊢
      omega
    · intro b hb
      simp only [mem_filter, mem_range] at hb
      omega
    · intro a _
      omega
    · intro b hb
      simp only [mem_filter, mem_range] at hb
      have e1 : 3 + (b - 3) = b := by omega
      have e2 : b - 3 + 6 + (h - 12 - 2 * (b - 3)) = h - b - 3 := by omega
      rw [e1, e2]
  · rw [if_neg h12]
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    omega

theorem mk_family20 (val : ℕ → ℕ → ℚ) (φ ψ : ℕ → ℚ) (hv : ∀ a e, val (3 + a) (a + 6 + e) = φ a * ψ e) :
    PowerSeries.mk (family20 val) = X ^ 12 * (spread 2 φ * PowerSeries.mk ψ) := by
  rw [spread_mul_mk 2 (by norm_num)]
  ext h
  rw [coeff_mk, family20_coeff, coeff_X_pow_mul', coeff_mk]
  by_cases h12 : 12 ≤ h
  · rw [if_pos h12, if_pos h12]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hv]
  · rw [if_neg h12, if_neg h12]


theorem inj_K {a b : PowerSeries ℚ}
    (h : HahnSeries.ofPowerSeries ℤ ℚ a = HahnSeries.ofPowerSeries ℤ ℚ b) : a = b :=
  HahnSeries.ofPowerSeries_injective h

theorem charZero_laurent : CharZero (LaurentSeries ℚ) :=
  charZero_of_injective_ringHom (f := (HahnSeries.C : ℚ →+* LaurentSeries ℚ)) HahnSeries.C_injective

theorem p8 (i : ℕ) : (1 / 8 : ℚ) ^ i = (1 / 2) ^ (3 * i) := by rw [pow_mul]; norm_num
theorem p4 (i : ℕ) : (1 / 4 : ℚ) ^ i = (1 / 2) ^ (2 * i) := by rw [pow_mul]; norm_num
theorem p16 (i : ℕ) : (1 / 16 : ℚ) ^ i = (1 / 2) ^ (4 * i) := by rw [pow_mul]; norm_num
theorem p64 (i : ℕ) : (1 / 64 : ℚ) ^ i = (1 / 2) ^ (6 * i) := by rw [pow_mul]; norm_num


theorem mk_family20_oo (val : ℕ → ℕ → ℚ) (c : ℚ)
    (hv : ∀ a e, val (3 + a) (a + 6 + e) =
      if a % 2 = 1 ∧ e % 2 = 1 then c * (1 / 8 : ℚ) ^ a * (1 / 2 : ℚ) ^ e else 0) :
    PowerSeries.mk (family20 val) = C (c * (1 / 8) * (1 / 2)) * X ^ 15 *
      (spread 4 (fun i => (1 / 64 : ℚ) ^ i) * spread 2 (fun i => (1 / 4 : ℚ) ^ i)) := by
  rw [mk_family20 val (fun a => if a % 2 = 1 then c * (1 / 8 : ℚ) ^ a else 0)
    (fun e => if e % 2 = 1 then (1 / 2 : ℚ) ^ e else 0)
    (by
      intro a e
      rw [hv]
      by_cases ha : a % 2 = 1 <;> by_cases he : e % 2 = 1 <;> simp [ha, he]), ← spread_one, spread_split 2 two_pos, spread_split 1 one_pos]
  have e1 : (fun i => if 2 * i % 2 = 1 then c * (1 / 8 : ℚ) ^ (2 * i) else 0) = fun i => 0 * (1 / 64 : ℚ) ^ i := by
    funext i; rw [if_neg (by omega)]; ring
  have e2 : (fun i => if (2 * i + 1) % 2 = 1 then c * (1 / 8 : ℚ) ^ (2 * i + 1) else 0) =
      fun i => (c * (1 / 8)) * (1 / 64 : ℚ) ^ i := by
    funext i; rw [if_pos (by omega)]; simp only [p8, p64]; ring
  have e3 : (fun i => if 2 * i % 2 = 1 then (1 / 2 : ℚ) ^ (2 * i) else 0) = fun i => 0 * (1 / 4 : ℚ) ^ i := by
    funext i; rw [if_neg (by omega)]; ring
  have e4 : (fun i => if (2 * i + 1) % 2 = 1 then (1 / 2 : ℚ) ^ (2 * i + 1) else 0) =
      fun i => (1 / 2) * (1 / 4 : ℚ) ^ i := by
    funext i; rw [if_pos (by omega)]; simp only [p4]; ring
  simp only [e1, e2, e3, e4, spread_smul]
  simp only [map_zero, zero_mul, zero_add, map_mul]
  ring

theorem mk_dyadicB (εu : ℤˣ) :
    PowerSeries.mk (dyadicB εu) = C (-((εu : ℤ) : ℚ) / 4) * PowerSeries.mk dyadicBmag := by
  ext h
  rw [coeff_mk, coeff_C_mul, coeff_mk, dyadicB]
  ring

theorem mkBmag :
    PowerSeries.mk dyadicBmag * (1 - C (1 / 4 : ℚ) * X ^ 2) =
      C 4 * (X * (1 + C (1 / 4 : ℚ) * X + C (1 / 16 : ℚ) * X ^ 2)) := by
  have r3 : PowerSeries.mk (family 3 (fun b => b + 3)
        (fun b => if Even b then 3 * (1 / 2 : ℚ) ^ (b + 4) else 0)) =
      C 0 * X ^ 6 * spread 2 (fun i => (1 / 4 : ℚ) ^ i) +
      C (3 * (1 / 2 : ℚ) ^ 8) * X ^ 7 * spread 2 (fun i => (1 / 4 : ℚ) ^ i) :=
    mk_family_geom2 1 3 3 one_pos _ (fun b => by simp) _ _ _ _
      (fun i => by
        rw [if_neg (by rw [Nat.even_iff]; omega)]; ring)
      (fun i => by
        rw [if_pos (by rw [Nat.even_iff]; omega)]; simp only [p4]; ring)
  have r5 : PowerSeries.mk (family 1 (fun b => b + 1)
        (fun b => if Even b then 4 * (1 / 2 : ℚ) ^ b else 2 * (1 / 2 : ℚ) ^ b)) =
      C 1 * X ^ 2 * spread 2 (fun i => (1 / 4 : ℚ) ^ i) +
      C 1 * X ^ 3 * spread 2 (fun i => (1 / 4 : ℚ) ^ i) :=
    mk_family_geom2 1 1 1 one_pos _ (fun b => by simp) _ _ _ _
      (fun i => by
        rw [if_neg (by rw [Nat.even_iff]; omega)]; simp only [p4]; ring)
      (fun i => by
        rw [if_pos (by rw [Nat.even_iff]; omega)]; simp only [p4]; ring)
  have r7 : PowerSeries.mk (family 3 (fun b => 2 * b + 3)
        (fun b => if Even b then 3 * (1 / 2 : ℚ) ^ (3 * b + 4) else 0)) =
      C 0 * X ^ 9 * spread 4 (fun i => (1 / 64 : ℚ) ^ i) +
      C (3 * (1 / 2 : ℚ) ^ 16) * X ^ 11 * spread 4 (fun i => (1 / 64 : ℚ) ^ i) :=
    mk_family_geom2 2 3 3 two_pos _ (fun b => by simp) _ _ _ _
      (fun i => by
        rw [if_neg (by rw [Nat.even_iff]; omega)]; ring)
      (fun i => by
        rw [if_pos (by rw [Nat.even_iff]; omega)]; simp only [p64]; ring)
  have r9 : PowerSeries.mk (family 2 (fun b => 2 * b + 3)
        (fun b => if Even b then (1 / 2 : ℚ) ^ (3 * b + 4) else (1 / 2 : ℚ) ^ (3 * b + 3))) =
      C ((1 / 2 : ℚ) ^ 10) * X ^ 7 * spread 4 (fun i => (1 / 64 : ℚ) ^ i) +
      C ((1 / 2 : ℚ) ^ 12) * X ^ 9 * spread 4 (fun i => (1 / 64 : ℚ) ^ i) :=
    mk_family_geom2 2 3 2 two_pos _ (fun b => by simp) _ _ _ _
      (fun i => by
        rw [if_pos (by rw [Nat.even_iff]; omega)]; simp only [p64]; ring)
      (fun i => by
        rw [if_neg (by rw [Nat.even_iff]; omega)]; simp only [p64]; ring)
  have r11 : PowerSeries.mk (family 3 (fun b => 2 * b + 5)
        (fun b => if Even b then 3 * (1 / 2 : ℚ) ^ (3 * b + 6) else 0)) =
      C 0 * X ^ 11 * spread 4 (fun i => (1 / 64 : ℚ) ^ i) +
      C (3 * (1 / 2 : ℚ) ^ 18) * X ^ 13 * spread 4 (fun i => (1 / 64 : ℚ) ^ i) :=
    mk_family_geom2 2 5 3 two_pos _ (fun b => by simp) _ _ _ _
      (fun i => by
        rw [if_neg (by rw [Nat.even_iff]; omega)]; ring)
      (fun i => by
        rw [if_pos (by rw [Nat.even_iff]; omega)]; simp only [p64]; ring)
  have r12 : PowerSeries.mk (family 5 (fun b => b + 5)
        (fun b => if Even b then 3 * (1 / 2 : ℚ) ^ (b + 8) else 0)) =
      C 0 * X ^ 10 * spread 2 (fun i => (1 / 4 : ℚ) ^ i) +
      C (3 * (1 / 2 : ℚ) ^ 14) * X ^ 11 * spread 2 (fun i => (1 / 4 : ℚ) ^ i) :=
    mk_family_geom2 1 5 5 one_pos _ (fun b => by simp) _ _ _ _
      (fun i => by
        rw [if_neg (by rw [Nat.even_iff]; omega)]; ring)
      (fun i => by
        rw [if_pos (by rw [Nat.even_iff]; omega)]; simp only [p4]; ring)
  have r13 : PowerSeries.mk (family20 (fun b c =>
        if Even b ∧ Even c then 3 * (1 / 2 : ℚ) ^ (2 * b + c + 4) else 0)) =
      C (3 * (1 / 2 : ℚ) ^ 16 * (1 / 8) * (1 / 2)) * X ^ 15 *
        (spread 4 (fun i => (1 / 64 : ℚ) ^ i) * spread 2 (fun i => (1 / 4 : ℚ) ^ i)) := by
    apply mk_family20_oo
    intro a e
    by_cases ha : a % 2 = 1 <;> by_cases he : e % 2 = 1
    · rw [if_pos ⟨by rw [Nat.even_iff]; omega, by rw [Nat.even_iff]; omega⟩, if_pos ⟨ha, he⟩]
      simp only [p8]; ring
    all_goals
      rw [if_neg (by
        rintro ⟨h1, h2⟩
        rw [Nat.even_iff] at h1 h2
        omega), if_neg (by omega)]
  unfold dyadicBmag
  simp only [mk_add', mk_single, r3, r5, r7, r9, r11, r12, r13]
  have h2 := congrArg (HahnSeries.ofPowerSeries ℤ ℚ) (spread_geom_mul 2 two_pos (1 / 4 : ℚ))
  have h4 := congrArg (HahnSeries.ofPowerSeries ℤ ℚ) (spread_geom_mul 4 (by norm_num) (1 / 64 : ℚ))
  apply inj_K
  simp only [map_mul, map_add, map_sub, map_one, map_zero, map_pow, HahnSeries.ofPowerSeries_X,
    HahnSeries.ofPowerSeries_C, map_div₀, map_ofNat, pow_one] at h2 h4 ⊢
  generalize HahnSeries.ofPowerSeries ℤ ℚ (spread 2 fun m => (1 / 4 : ℚ) ^ m) = g2 at h2 ⊢
  generalize HahnSeries.ofPowerSeries ℤ ℚ (spread 4 fun m => (1 / 64 : ℚ) ^ m) = g4 at h4 ⊢
  set x : LaurentSeries ℚ := HahnSeries.single (1 : ℤ) (1 : ℚ) with hx
  have := charZero_laurent
  linear_combination
    ((3 * (1 / 2) ^ 8 * x ^ 7 + x ^ 2 + x ^ 3 + 3 * (1 / 2) ^ 14 * x ^ 11) +
      3 * (1 / 2) ^ 16 * (1 / 8) * (1 / 2) * x ^ 15 * g4) * h2 + (x ^ 7 / 1024) * h4

theorem mk_dyadicA : PowerSeries.mk dyadicA = C (1 / 4 : ℚ) * PowerSeries.mk dyadicA4 := by
  ext h
  rw [coeff_mk, coeff_C_mul, coeff_mk, dyadicA]
  ring

theorem aux_6_1 :
    PowerSeries.mk dyadicA * ((1 - C (1 / 2 : ℚ) * X) * (1 - C (1 / 8 : ℚ) * X ^ 2)) =
      X * (1 - C (1 / 64 : ℚ) * X ^ 3) := by
  have r4 : PowerSeries.mk (family 3 (fun b => b + 3) (fun b => 3 * (1 / 2 : ℚ) ^ (b + 3))) =
      C (3 * (1 / 2 : ℚ) ^ 6) * X ^ (1 * 3 + 3) * spread 1 (fun i => (1 / 2 : ℚ) ^ i) :=
    mk_family_geom 1 3 3 one_pos _ (fun b => by simp) _ _ _ (fun i => by ring)
  have r6 : PowerSeries.mk (family 1 (fun b => b + 1) (fun b => 4 * (1 / 2 : ℚ) ^ b)) =
      C (4 * (1 / 2 : ℚ) ^ 1) * X ^ (1 * 1 + 1) * spread 1 (fun i => (1 / 2 : ℚ) ^ i) :=
    mk_family_geom 1 1 1 one_pos _ (fun b => by simp) _ _ _ (fun i => by ring)
  have r9 : PowerSeries.mk (family 3 (fun b => 2 * b + 3) (fun b => 3 * (1 / 2 : ℚ) ^ (3 * b + 3))) =
      C (3 * (1 / 2 : ℚ) ^ 12) * X ^ (2 * 3 + 3) * spread 2 (fun i => (1 / 8 : ℚ) ^ i) :=
    mk_family_geom 2 3 3 two_pos _ (fun b => by simp) _ _ _ (fun i => by simp only [p8]; ring)
  have r11 : PowerSeries.mk (family 2 (fun b => 2 * b + 3) (fun b => (1 / 2 : ℚ) ^ (3 * b + 3))) =
      C ((1 / 2 : ℚ) ^ 9) * X ^ (2 * 2 + 3) * spread 2 (fun i => (1 / 8 : ℚ) ^ i) :=
    mk_family_geom 2 3 2 two_pos _ (fun b => by simp) _ _ _ (fun i => by simp only [p8]; ring)
  have r16 : PowerSeries.mk (family 4 (fun b => b + 4) (fun b => 3 * (1 / 2 : ℚ) ^ (b + 5))) =
      C (3 * (1 / 2 : ℚ) ^ 9) * X ^ (1 * 4 + 4) * spread 1 (fun i => (1 / 2 : ℚ) ^ i) :=
    mk_family_geom 1 4 4 one_pos _ (fun b => by simp) _ _ _ (fun i => by ring)
  have r17 : PowerSeries.mk (family 3 (fun b => 2 * b + 4) (fun b => 3 * (1 / 2 : ℚ) ^ (3 * b + 4))) =
      C (3 * (1 / 2 : ℚ) ^ 13) * X ^ (2 * 3 + 4) * spread 2 (fun i => (1 / 8 : ℚ) ^ i) :=
    mk_family_geom 2 4 3 two_pos _ (fun b => by simp) _ _ _ (fun i => by simp only [p8]; ring)
  have r18 : PowerSeries.mk (family 3 (fun b => 2 * b + 5) (fun b => 3 * (1 / 2 : ℚ) ^ (3 * b + 5))) =
      C (3 * (1 / 2 : ℚ) ^ 14) * X ^ (2 * 3 + 5) * spread 2 (fun i => (1 / 8 : ℚ) ^ i) :=
    mk_family_geom 2 5 3 two_pos _ (fun b => by simp) _ _ _ (fun i => by simp only [p8]; ring)
  have r19 : PowerSeries.mk (family 5 (fun b => b + 5) (fun b => 3 * (1 / 2 : ℚ) ^ (b + 7))) =
      C (3 * (1 / 2 : ℚ) ^ 12) * X ^ (1 * 5 + 5) * spread 1 (fun i => (1 / 2 : ℚ) ^ i) :=
    mk_family_geom 1 5 5 one_pos _ (fun b => by simp) _ _ _ (fun i => by ring)
  have r20 : PowerSeries.mk (family20 (fun b c => 3 * (1 / 2 : ℚ) ^ (2 * b + c + 3))) =
      X ^ 12 * (C (3 * (1 / 2 : ℚ) ^ 15) * spread 2 (fun i => (1 / 8 : ℚ) ^ i) *
        spread 1 (fun i => (1 / 2 : ℚ) ^ i)) := by
    rw [mk_family20 _ (fun a => (3 * (1 / 2 : ℚ) ^ 15) * (1 / 8 : ℚ) ^ a) (fun e => (1 / 2 : ℚ) ^ e)
      (fun a e => by simp only [p8]; ring), spread_smul, spread_one]
  rw [mk_dyadicA]
  unfold dyadicA4
  simp only [mk_add', mk_single, r4, r6, r9, r11, r16, r17, r18, r19, r20]
  have h1 := congrArg (HahnSeries.ofPowerSeries ℤ ℚ) (spread_geom_mul 1 one_pos (1 / 2 : ℚ))
  have h2 := congrArg (HahnSeries.ofPowerSeries ℤ ℚ) (spread_geom_mul 2 two_pos (1 / 8 : ℚ))
  apply inj_K
  simp only [map_mul, map_add, map_sub, map_one, map_pow, HahnSeries.ofPowerSeries_X,
    HahnSeries.ofPowerSeries_C, map_div₀, map_ofNat, pow_one] at h1 h2 ⊢
  generalize HahnSeries.ofPowerSeries ℤ ℚ (spread 1 fun m => (1 / 2 : ℚ) ^ m) = g1 at h1 ⊢
  generalize HahnSeries.ofPowerSeries ℤ ℚ (spread 2 fun m => (1 / 8 : ℚ) ^ m) = g2 at h2 ⊢
  set x : LaurentSeries ℚ := HahnSeries.single (1 : ℤ) (1 : ℚ) with hx
  have := charZero_laurent
  linear_combination (1 / 4 : LaurentSeries ℚ) *
    (((3 * (1 / 2) ^ 6 * x ^ 6 + 4 * (1 / 2) * x ^ 2 + 3 * (1 / 2) ^ 9 * x ^ 8 + 3 * (1 / 2) ^ 12 * x ^ 10) *
        (1 - 1 / 8 * x ^ 2) + 3 * (1 / 2) ^ 15 * x ^ 12 * g2 * (1 - 1 / 8 * x ^ 2)) * h1 +
      ((3 * (1 / 2) ^ 12 * x ^ 9 + (1 / 2) ^ 9 * x ^ 7 + 3 * (1 / 2) ^ 13 * x ^ 10 + 3 * (1 / 2) ^ 14 * x ^ 11) *
        (1 - 1 / 2 * x) + 3 * (1 / 2) ^ 15 * x ^ 12) * h2)


theorem rescale_C' (a c : ℚ) : rescale a (C c) = C c := by
  ext n
  rw [coeff_rescale, coeff_C]
  rcases n with _ | n <;> simp

/-- **Lemma 6.1** (Hanke 2011, p. 22): for $\mathfrak p \mid 2$, $F_{\mathfrak p} = \mathbb{Q}_2$ and a fixed unit
square class $u$,
$$\sum_{\substack{S_{\mathfrak p}\\ \widetilde S_{\mathfrak p} = u}}
\frac{A^*_{\mathfrak p;3}(S_{\mathfrak p})}{N_{F/\mathbb{Q}}(I(S_{\mathfrak p}))^s}
= \frac{(1 - 2^{-(3s+6)})\cdot 2^{-s}}{(1 - 2^{-(s+1)})(1 - 2^{-(2s+3)})},$$
i.e. with $X = 2^{-s}$: $\big(\sum_h A^*(2^h u)X^h\big)(1 - X/2)(1 - X^2/8) = X(1 - X^3/64)$. The values
$A^*(2^hu)$ are those of Table 5.3 (`dyadicA`), which do not depend on $u$. -/
@[kb "hanke2011ternary" "§6, Lemma 6.1, p. 22"]
theorem lemma_6_1 :
    PowerSeries.mk dyadicA * ((1 - C (1 / 2 : ℚ) * X) * (1 - C (1 / 8 : ℚ) * X ^ 2)) =
      X * (1 - C (1 / 64 : ℚ) * X ^ 3) :=
  aux_6_1

/-- **Lemma 6.2** (Hanke 2011, p. 23): for $\mathfrak p \mid 2$, $F_{\mathfrak p} = \mathbb{Q}_2$ and a fixed unit
square class $u$ with $\varepsilon_u = (-1, u)_{\mathfrak p}$ (`εu`),
$$\sum_{\substack{S_{\mathfrak p}\\ \widetilde S_{\mathfrak p} = u}}
\frac{B^*_{\mathfrak p;3}(S_{\mathfrak p})}{N_{F/\mathbb{Q}}(I(S_{\mathfrak p}))^s}
= \frac{-\varepsilon_u(1 + 2^{-(s+2)} + 2^{-(2s+4)})\cdot 2^{-s}}{1 - 2^{-(2s+2)}},$$
i.e. with $X = 2^{-s}$: $\big(\sum_h B^*(2^hu)X^h\big)(1 - X^2/4) = -\varepsilon_u X(1 + X/4 + X^2/16)$. -/
@[kb "hanke2011ternary" "§6, Lemma 6.2, p. 23"]
theorem lemma_6_2 (εu : ℤˣ) :
    PowerSeries.mk (dyadicB εu) * (1 - C (1 / 4 : ℚ) * X ^ 2) =
      -(C ((εu : ℤ) : ℚ) * X * (1 + C (1 / 4 : ℚ) * X + C (1 / 16 : ℚ) * X ^ 2)) := by
  rw [mk_dyadicB, mul_assoc, mkBmag]
  have h : C (-((εu : ℤ) : ℚ) / 4) * C (4 : ℚ) = -C ((εu : ℤ) : ℚ) := by
    rw [← map_mul, ← map_neg]; congr 1; ring
  rw [← mul_assoc, h]
  ring

/-- **Lemma 6.4, $A^*$** (Hanke 2011, p. 25): the Euler factor at $\mathfrak p \mid 2$ ($F_{\mathfrak p} = \mathbb{Q}_2$)
of $D_{A^*,\lambda;3}(s)$ is $\dfrac{(1 - 2^{-(3s+6)})\,2^{-s}}{(1 - 2^{-(s+1)})(1 - 2^{-(2s+3)})}$ for every
distinguished family $\lambda$: the coefficients `dyadicA h` do not depend on the unit part of $\lambda(\mathfrak p^h)$. -/
@[kb "hanke2011ternary" "§6, Lemma 6.4, p. 25"]
theorem lemma_6_4_A :
    PowerSeries.mk dyadicA * ((1 - C (1 / 2 : ℚ) * X) * (1 - C (1 / 8 : ℚ) * X ^ 2)) =
      X * (1 - C (1 / 64 : ℚ) * X ^ 3) :=
  lemma_6_1

/-- **Lemma 6.4, $B^*$** (Hanke 2011, p. 25): for a distinguished family $\lambda$ with
$\varepsilon_{\mathfrak p} := (-1, \lambda(\mathfrak p))_{\mathfrak p}$ (`εp`), the coefficient at $h$ is
$B^*(\lambda(\mathfrak p)^h) = $ `dyadicB (εp ^ h) h`, and the Euler factor is
$$\frac{-\varepsilon_{\mathfrak p}(1 + \varepsilon_{\mathfrak p}2^{-(s+2)} + 2^{-(2s+4)})\cdot 2^{-s}}{1 - 2^{-(2s+2)}},$$
i.e. $\big(\sum_h B^*(\lambda(\mathfrak p)^h)X^h\big)(1 - X^2/4)
= -\varepsilon_{\mathfrak p}X(1 + \varepsilon_{\mathfrak p}X/4 + X^2/16)$. -/
@[kb "hanke2011ternary" "§6, Lemma 6.4, p. 25"]
theorem lemma_6_4_B (εp : ℤˣ) :
    PowerSeries.mk (fun h => dyadicB (εp ^ h) h) * (1 - C (1 / 4 : ℚ) * X ^ 2) =
      -(C ((εp : ℤ) : ℚ) * X *
        (1 + C (((εp : ℤ) : ℚ) * (1 / 4)) * X + C (1 / 16 : ℚ) * X ^ 2)) := by
  have hsq : ((εp : ℤ) : ℚ) * ((εp : ℤ) : ℚ) = 1 := by
    rcases Int.units_eq_one_or εp with h | h <;> simp [h]
  have ha : C ((εp : ℤ) : ℚ) * C ((εp : ℤ) : ℚ) = 1 := by
    rw [← map_mul, hsq, map_one]
  have hmk : PowerSeries.mk (fun h => dyadicB (εp ^ h) h) =
      rescale ((εp : ℤ) : ℚ) (PowerSeries.mk (dyadicB 1)) := by
    ext n
    rw [coeff_rescale, coeff_mk, coeff_mk]
    simp only [dyadicB, Units.val_pow_eq_pow_val, Units.val_one]
    push_cast
    ring
  have h := congrArg (rescale ((εp : ℤ) : ℚ)) (lemma_6_2 1)
  simp only [map_mul, map_sub, map_neg, map_add, map_one, rescale_X, rescale_C', map_pow] at h
  rw [hmk, map_mul C]
  have h1 : C (((1 : ℤˣ) : ℤ) : ℚ) = 1 := by simp
  rw [h1] at h
  linear_combination h +
    (rescale ((εp : ℤ) : ℚ) (PowerSeries.mk (dyadicB 1)) * C (1 / 4 : ℚ) * X ^ 2 -
      C ((εp : ℤ) : ℚ) * X ^ 3 * C (1 / 16 : ℚ)) * ha

end QuadFormsKB.Hanke2011Ternary
