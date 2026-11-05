/-
# Cassels, Chapter 5, Examples 1 and 2: two and four squares by Minkowski's theorem

**Proves** (Cassels, *Rational Quadratic Forms*, Chapter 5, Examples, p. 74)
* Example 1 (i): if $r^2 \equiv -1 \pmod m$, then on $\Lambda = \{(x, y) : x \equiv ry \pmod m\}$ one has
  $x^2 + y^2 \equiv 0 \pmod m$, $\Lambda$ has a point $(a, b) \ne 0$ with $a^2 + b^2 < 2m$, and $m = a^2 + b^2$
  (`ex1_i`); (ii) the condition holds for primes $m \equiv 1 \pmod 4$ (`ex1_ii`); (iii) and for $m = m_1$, $2m_1$ with
  all prime factors of $m_1$ congruent to $1 \bmod 4$ (`ex1_iii`);
* Example 2 (i): if $r^2 + s^2 + 1 \equiv 0 \pmod m$, then on $\Lambda = \{(x, y, z, w) : x \equiv rz + sw,\
  y \equiv sz - rw \pmod m\}$ there is a point $\ne 0$ with $a^2 + b^2 + c^2 + d^2 < 2m$, and
  $m = a^2 + b^2 + c^2 + d^2$ (`ex2_i`); (ii) the condition holds for $m$ odd or twice an odd number (`ex2_ii`), and
  every positive integer is a sum of four squares (`ex2_four_squares`).

**Proof notes.** As Cassels intends: Ch. 5, Theorem 2.3 (`minkowski_congruences`) applied to the open disc
$x^2 + y^2 < 2m$ of area $2\pi m > 2^2m$, respectively the open ball $\sum x_i^2 < 2m$ in $\mathbb R^4$ of volume
$\frac{\pi^2}{2}(2m)^2 = 2\pi^2m^2 > 2^4m^2$ ($\Lambda$ is cut out by congruences with moduli of product $m$,
respectively $m^2$).
-/
import QuadFormsKB.Literature.Cassels.Ch5.Minkowski

namespace QuadFormsKB.Cassels.Ch5

open MeasureTheory Real

/-- Volume of the open ball `∑ xᵢ² < R` in `ℝ^ι` (Mathlib's `volume_sum_rpow_lt` with `p = 2`). -/
private lemma ex_vol_ball (ι : Type) [Fintype ι] [Nonempty ι] (R : ℝ) (hR : 0 < R) :
    volume {x : ι → ℝ | ∑ i, x i ^ 2 < R} = ENNReal.ofReal (R ^ (Fintype.card ι / 2 : ℝ)) *
      ENNReal.ofReal ((2 * Real.Gamma (1 / 2 + 1)) ^ Fintype.card ι / Real.Gamma (Fintype.card ι / 2 + 1)) := by
  have h := volume_sum_rpow_lt (ι := ι) (p := 2) (by norm_num) (√R)
  have hset : {x : ι → ℝ | ∑ i, x i ^ 2 < R} =
      {x : ι → ℝ | (∑ i, |x i| ^ (2:ℝ)) ^ (1 / (2:ℝ)) < √R} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    have : ∑ i, |x i| ^ (2:ℝ) = ∑ i, x i ^ 2 := by simp [sq_abs]
    rw [this, ← Real.sqrt_eq_rpow, Real.sqrt_lt_sqrt_iff (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  rw [hset, h, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _)]
  congr 2
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hR.le]
  congr 1
  ring

private lemma ex_gamma_half : Real.Gamma (1 / 2 + 1) = √π / 2 := by
  rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]; ring

/-- Area of the open disc `x² + y² < 2m`. -/
private lemma ex_vol2 (m : ℝ) (hm : 0 < m) :
    volume {x : Fin 2 → ℝ | ∑ i, x i ^ 2 < 2 * m} = ENNReal.ofReal (2 * π * m) := by
  rw [ex_vol_ball (Fin 2) _ (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [Fintype.card_fin, ex_gamma_half]
  have h1 : (2 * m) ^ (((2:ℕ):ℝ) / 2) = 2 * m := by norm_num
  have h2 : Real.Gamma (((2:ℕ):ℝ) / 2 + 1) = 1 := by
    rw [show ((2:ℕ):ℝ) / 2 + 1 = 2 by norm_num]; exact Real.Gamma_two
  rw [h1, h2]
  have hsq : √π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  have : (2 * (√π / 2)) ^ 2 = π := by rw [mul_div_cancel₀ _ (two_ne_zero)]; exact hsq
  rw [this]; ring

/-- Volume of the open ball `∑ xᵢ² < 2m` in `ℝ⁴`. -/
private lemma ex_vol4 (m : ℝ) (hm : 0 < m) :
    volume {x : Fin 4 → ℝ | ∑ i, x i ^ 2 < 2 * m} = ENNReal.ofReal (2 * π ^ 2 * m ^ 2) := by
  rw [ex_vol_ball (Fin 4) _ (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [Fintype.card_fin, ex_gamma_half]
  have h1 : (2 * m) ^ (((4:ℕ):ℝ) / 2) = 4 * m ^ 2 := by
    rw [show (((4:ℕ):ℝ) / 2) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; ring
  have h2 : Real.Gamma (((4:ℕ):ℝ) / 2 + 1) = 2 := by
    rw [show ((4:ℕ):ℝ) / 2 + 1 = 1 + 1 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_add_one (by norm_num), Real.Gamma_one]; norm_num
  rw [h1, h2]
  have hsq : √π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  have : (2 * (√π / 2)) ^ 4 = π ^ 2 := by
    rw [mul_div_cancel₀ _ (two_ne_zero), show (4:ℕ) = 2 * 2 from rfl, pow_mul, hsq]
  rw [this]; ring

/-- The open ball `∑ xᵢ² < c` is convex. -/
private lemma ex_ball_convex (n : ℕ) (c : ℝ) :
    Convex ℝ {x : Fin n → ℝ | ∑ i, x i ^ 2 < c} := by
  intro x hx y hy s t hs ht hst
  simp only [Set.mem_ofPred_eq] at *
  have key : ∀ i, (s * x i + t * y i) ^ 2 ≤ s * x i ^ 2 + t * y i ^ 2 := by
    intro i
    have h1 : s * x i ^ 2 + t * y i ^ 2 - (s * x i + t * y i) ^ 2 = s * t * (x i - y i) ^ 2 := by
      have : t = 1 - s := by linarith
      subst this; ring
    have h2 : 0 ≤ s * t * (x i - y i) ^ 2 := by positivity
    linarith
  calc ∑ i, (s • x + t • y) i ^ 2
      ≤ ∑ i, (s * x i ^ 2 + t * y i ^ 2) :=
        Finset.sum_le_sum (fun i _ => by simpa using key i)
    _ = s * ∑ i, x i ^ 2 + t * ∑ i, y i ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ < c := by
        rcases hs.eq_or_lt with h0 | h0
        · have : t = 1 := by linarith
          subst this; rw [← h0]; simpa using hy
        · have := mul_lt_mul_of_pos_left hx h0
          have := mul_le_mul_of_nonneg_left hy.le ht
          have hc : (s + t) * c = c := by rw [hst]; ring
          nlinarith

/-- The open ball `∑ xᵢ² < c` is symmetric. -/
private lemma ex_ball_symm (n : ℕ) (c : ℝ) (x : Fin n → ℝ) (hx : x ∈ {x : Fin n → ℝ | ∑ i, x i ^ 2 < c}) :
    -x ∈ {x : Fin n → ℝ | ∑ i, x i ^ 2 < c} := by
  simpa using hx

/-- Hensel step for `r² + c` modulo `p^k`, `k ≥ 1`, `p` odd and `p ∤ r`. -/
private lemma ex_hensel_step (p k : ℕ) (hk : 1 ≤ k) (c r : ℤ) (hr : IsCoprime (2 * r) (p : ℤ))
    (h : (p : ℤ) ^ k ∣ r ^ 2 + c) :
    ∃ r' : ℤ, (p : ℤ) ^ (k + 1) ∣ r' ^ 2 + c ∧ (p : ℤ) ∣ r' - r := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨q, hq⟩ := h
  obtain ⟨u, v, huv⟩ := hr
  refine ⟨r + (-q * u) * (p : ℤ) ^ (j + 1), ⟨q * v + q ^ 2 * u ^ 2 * (p : ℤ) ^ j, ?_⟩, ?_⟩
  · linear_combination hq - ((p : ℤ) ^ (j + 1) * q) * huv
  · exact ⟨(-q * u) * (p : ℤ) ^ j, by ring⟩

/-- Lifting a root of `r² + c` from `p` to `p^k`, `p` an odd prime, `p ∤ r`. -/
private lemma ex_hensel_lift (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (c r : ℤ) (hr : ¬ (p : ℤ) ∣ r)
    (h : (p : ℤ) ∣ r ^ 2 + c) :
    ∀ k : ℕ, 1 ≤ k → ∃ r' : ℤ, (p : ℤ) ^ k ∣ r' ^ 2 + c ∧ (p : ℤ) ∣ r' - r := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact ⟨r, by simpa using h, by simp⟩
  | succ k hk ih =>
    obtain ⟨r', h1, h2⟩ := ih
    have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hr' : ¬ (p : ℤ) ∣ r' := by
      intro hd
      exact hr (by have := dvd_sub hd h2; simpa using this)
    have h2' : ¬ (p : ℤ) ∣ 2 * r' := by
      intro hd
      rcases hpi.dvd_or_dvd hd with hd | hd
      · have : p ∣ 2 := by exact_mod_cast hd
        have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this
        exact hp2 this
      · exact hr' hd
    have hcop : IsCoprime (2 * r') (p : ℤ) := (hpi.irreducible.coprime_iff_not_dvd.mpr h2').symm
    obtain ⟨r'', h3, h4⟩ := ex_hensel_step p k hk c r' hcop h1
    exact ⟨r'', h3, by simpa using dvd_add h4 h2⟩

/-- Chinese remainder for two coprime moduli. -/
private lemma ex_crt (a b : ℕ) (hab : Nat.Coprime a b) (x y : ℤ) :
    ∃ z : ℤ, (a : ℤ) ∣ z - x ∧ (b : ℤ) ∣ z - y := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hab
  exact ⟨x * (v * b) + y * (u * a), ⟨(y - x) * u, by linear_combination x * huv⟩,
    ⟨(x - y) * v, by linear_combination y * huv⟩⟩


/-- Multiplicativity of "`-1` is a square" for coprime moduli. -/
private lemma ex_mul1 (a b : ℕ) (hab : Nat.Coprime a b) (h1 : ∃ r : ℤ, (a : ℤ) ∣ r ^ 2 + 1)
    (h2 : ∃ r : ℤ, (b : ℤ) ∣ r ^ 2 + 1) : ∃ r : ℤ, ((a * b : ℕ) : ℤ) ∣ r ^ 2 + 1 := by
  obtain ⟨r1, h1⟩ := h1
  obtain ⟨r2, h2⟩ := h2
  obtain ⟨z, hz1, hz2⟩ := ex_crt a b hab r1 r2
  refine ⟨z, ?_⟩
  push_cast
  refine (Nat.isCoprime_iff_coprime.mpr hab).mul_dvd ?_ ?_
  · have : z ^ 2 + 1 = (z - r1) * (z + r1) + (r1 ^ 2 + 1) := by ring
    rw [this]; exact dvd_add (Dvd.dvd.mul_right hz1 _) h1
  · have : z ^ 2 + 1 = (z - r2) * (z + r2) + (r2 ^ 2 + 1) := by ring
    rw [this]; exact dvd_add (Dvd.dvd.mul_right hz2 _) h2

/-- Multiplicativity of "`-1` is a sum of two squares" for coprime moduli. -/
private lemma ex_mul2 (a b : ℕ) (hab : Nat.Coprime a b) (h1 : ∃ r s : ℤ, (a : ℤ) ∣ r ^ 2 + s ^ 2 + 1)
    (h2 : ∃ r s : ℤ, (b : ℤ) ∣ r ^ 2 + s ^ 2 + 1) : ∃ r s : ℤ, ((a * b : ℕ) : ℤ) ∣ r ^ 2 + s ^ 2 + 1 := by
  obtain ⟨r1, s1, h1⟩ := h1
  obtain ⟨r2, s2, h2⟩ := h2
  obtain ⟨z, hz1, hz2⟩ := ex_crt a b hab r1 r2
  obtain ⟨w, hw1, hw2⟩ := ex_crt a b hab s1 s2
  refine ⟨z, w, ?_⟩
  push_cast
  refine (Nat.isCoprime_iff_coprime.mpr hab).mul_dvd ?_ ?_
  · have : z ^ 2 + w ^ 2 + 1 = (z - r1) * (z + r1) + (w - s1) * (w + s1) + (r1 ^ 2 + s1 ^ 2 + 1) := by ring
    rw [this]; exact dvd_add (dvd_add (Dvd.dvd.mul_right hz1 _) (Dvd.dvd.mul_right hw1 _)) h1
  · have : z ^ 2 + w ^ 2 + 1 = (z - r2) * (z + r2) + (w - s2) * (w + s2) + (r2 ^ 2 + s2 ^ 2 + 1) := by ring
    rw [this]; exact dvd_add (dvd_add (Dvd.dvd.mul_right hz2 _) (Dvd.dvd.mul_right hw2 _)) h2

/-- A positive multiple of `m` below `2m` is `m`. -/
private lemma ex_eq_of_dvd (m S : ℤ) (hm : 0 < m) (hd : m ∣ S) (h0 : 0 < S) (h1 : S < 2 * m) : S = m := by
  obtain ⟨k, rfl⟩ := hd
  have hk0 : 0 < k := by
    by_contra h; push Not at h; nlinarith
  have hk1 : k < 2 := by
    by_contra h; push Not at h; nlinarith
  have : k = 1 := by omega
  subst this; ring


/-- **Cassels, Ch. 5, Example 1 (i)**: *let $m \ge 1$ and $r^2 \equiv -1 \pmod m$, and let $\Lambda$ be the set of
$(x, y) \in \mathbb Z^2$ with $x \equiv ry \pmod m$. Then $x^2 + y^2 \equiv 0 \pmod m$ on $\Lambda$; there is an
$(a, b) \ne (0, 0)$ in $\Lambda$ with $a^2 + b^2 < 2m$; and so $a^2 + b^2 = m$.* -/
@[kb "cassels1978" "Ch. 5, Ex. 1 (i), p. 74"]
theorem ex1_i (m : ℕ) (hm : 0 < m) (r : ℤ) (hr : (m : ℤ) ∣ r ^ 2 + 1) :
    (∀ x y : ℤ, (m : ℤ) ∣ x - r * y → (m : ℤ) ∣ x ^ 2 + y ^ 2) ∧
    (∃ a b : ℤ, (a, b) ≠ (0, 0) ∧ (m : ℤ) ∣ a - r * b ∧ a ^ 2 + b ^ 2 < 2 * m) ∧
    ∃ a b : ℤ, a ^ 2 + b ^ 2 = m := by
  have hdiv : ∀ x y : ℤ, (m : ℤ) ∣ x - r * y → (m : ℤ) ∣ x ^ 2 + y ^ 2 := by
    intro x y h
    have : x ^ 2 + y ^ 2 = (x - r * y) * (x + r * y) + y ^ 2 * (r ^ 2 + 1) := by ring
    rw [this]; exact dvd_add (Dvd.dvd.mul_right h _) (Dvd.dvd.mul_left hr _)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hex : ∃ a b : ℤ, (a, b) ≠ (0, 0) ∧ (m : ℤ) ∣ a - r * b ∧ a ^ 2 + b ^ 2 < 2 * m := by
    obtain ⟨u, hu0, hud, huC⟩ := minkowski_congruences (n := 2) (r := 1) (fun _ => ![1, -r])
      (fun _ => m) (fun _ => hm) (C := {x : Fin 2 → ℝ | ∑ i, x i ^ 2 < 2 * m})
      (fun x hx => ex_ball_symm 2 _ x hx) (ex_ball_convex 2 _) (by
        rw [ex_vol2 m hm']
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one]
        have : (2 : ENNReal) ^ 2 * (m : ENNReal) = ENNReal.ofReal (4 * m) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast]
          norm_num
        rw [this, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
        nlinarith [Real.pi_gt_three])
    refine ⟨u 0, u 1, ?_, ?_, ?_⟩
    · intro h
      apply hu0
      simp only [Prod.mk.injEq] at h
      ext i; fin_cases i <;> simp [h.1, h.2]
    · have := hud 0
      simpa [Fin.sum_univ_two, sub_eq_add_neg] using this
    · have : ∑ i, (u i : ℝ) ^ 2 < 2 * m := huC
      rw [Fin.sum_univ_two] at this
      exact_mod_cast this
  obtain ⟨a, b, hab, hd, hlt⟩ := hex
  have hpos : 0 < a ^ 2 + b ^ 2 := by
    by_contra hle
    apply hab
    have ha : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hb : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    rw [pow_eq_zero_iff two_ne_zero] at ha hb
    rw [ha, hb]
  have hmz : (0 : ℤ) < m := by exact_mod_cast hm
  exact ⟨hdiv, ⟨a, b, hab, hd, hlt⟩, a, b, ex_eq_of_dvd m _ hmz (hdiv a b hd) hpos hlt⟩

/-- **Cassels, Ch. 5, Example 1 (ii)**: *the conditions of (i) hold when $m$ is an odd prime $\equiv 1 \pmod 4$.* -/
@[kb "cassels1978" "Ch. 5, Ex. 1 (ii), p. 74"]
theorem ex1_ii (p : ℕ) (hp : p.Prime) (h4 : p % 4 = 1) : ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 + 1 := by
  have := Fact.mk hp
  obtain ⟨y, hy⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by omega)
  refine ⟨(y.val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val]
  linear_combination (-1 : ZMod p) * hy

/-- **Cassels, Ch. 5, Example 1 (iii)**: *the conditions of (i) hold whenever $m = m_1$ or $m = 2m_1$ and all prime
factors of $m_1$ are $\equiv 1 \pmod 4$.* -/
@[kb "cassels1978" "Ch. 5, Ex. 1 (iii), p. 74"]
theorem ex1_iii (m₁ : ℕ) (hm₁ : 0 < m₁) (h : ∀ q : ℕ, q.Prime → q ∣ m₁ → q % 4 = 1) (m : ℕ)
    (hm : m = m₁ ∨ m = 2 * m₁) : ∃ r : ℤ, (m : ℤ) ∣ r ^ 2 + 1 := by
  have key : ∀ n : ℕ, (∀ q : ℕ, q.Prime → q ∣ n → q % 4 = 1) → ∃ r : ℤ, (n : ℤ) ∣ r ^ 2 + 1 := by
    intro n
    induction n using Nat.recOnPosPrimePosCoprime with
    | zero => intro h; exact absurd (h 2 Nat.prime_two (dvd_zero 2)) (by norm_num)
    | one => intro _; exact ⟨0, by simp⟩
    | prime_pow p k hp hk =>
      intro h
      have hp4 : p % 4 = 1 := h p hp (dvd_pow_self p hk.ne')
      have hp2 : p ≠ 2 := by omega
      obtain ⟨r0, hr0⟩ := ex1_ii p hp hp4
      have hnd : ¬ (p : ℤ) ∣ r0 := by
        intro hd
        have h1 : (p : ℤ) ∣ r0 ^ 2 := Dvd.dvd.pow hd two_ne_zero
        have h2 : (p : ℤ) ∣ 1 := (dvd_add_right h1).mp hr0
        have h3 : p ∣ 1 := by exact_mod_cast h2
        exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
      obtain ⟨r', h1, -⟩ := ex_hensel_lift p hp hp2 1 r0 hnd hr0 k hk
      exact ⟨r', by push_cast; exact h1⟩
    | coprime a b ha hb hab iha ihb =>
      intro h
      exact ex_mul1 a b hab (iha fun q hq hqa => h q hq (dvd_mul_of_dvd_left hqa b))
        (ihb fun q hq hqb => h q hq (dvd_mul_of_dvd_right hqb a))
  rcases hm with rfl | rfl
  · exact key m h
  · have h2 : ¬ 2 ∣ m₁ := fun hd => by have := h 2 Nat.prime_two hd; omega
    exact ex_mul1 2 m₁ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2) ⟨1, by norm_num⟩
      (key m₁ h)

/-- **Cassels, Ch. 5, Example 2 (i)**: *let $m \ge 1$ and $r^2 + s^2 + 1 \equiv 0 \pmod m$, and let $\Lambda$ be the set
of $(x, y, z, w) \in \mathbb Z^4$ with $x \equiv rz + sw$, $y \equiv sz - rw \pmod m$. Then there is a point
$(a, b, c, d) \ne 0$ of $\Lambda$ with $a^2 + b^2 + c^2 + d^2 < 2m$; and so $m = a^2 + b^2 + c^2 + d^2$.* -/
@[kb "cassels1978" "Ch. 5, Ex. 2 (i), p. 74"]
theorem ex2_i (m : ℕ) (hm : 0 < m) (r s : ℤ) (hrs : (m : ℤ) ∣ r ^ 2 + s ^ 2 + 1) :
    (∃ a b c d : ℤ, (a, b, c, d) ≠ (0, 0, 0, 0) ∧ (m : ℤ) ∣ a - (r * c + s * d) ∧ (m : ℤ) ∣ b - (s * c - r * d) ∧
      a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 < 2 * m) ∧
    ∃ a b c d : ℤ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hex : ∃ a b c d : ℤ, (a, b, c, d) ≠ (0, 0, 0, 0) ∧ (m : ℤ) ∣ a - (r * c + s * d) ∧
      (m : ℤ) ∣ b - (s * c - r * d) ∧ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 < 2 * m := by
    obtain ⟨u, hu0, hud, huC⟩ := minkowski_congruences (n := 4) (r := 2)
      (fun l => if l = 0 then ![1, 0, -r, -s] else ![0, 1, -s, r])
      (fun _ => m) (fun _ => hm) (C := {x : Fin 4 → ℝ | ∑ i, x i ^ 2 < 2 * m})
      (fun x hx => ex_ball_symm 4 _ x hx) (ex_ball_convex 4 _) (by
        rw [ex_vol4 m hm']
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        have : (2 : ENNReal) ^ 4 * ((m ^ 2 : ℕ) : ENNReal) = ENNReal.ofReal (16 * m ^ 2) := by
          rw [ENNReal.ofReal_mul (by norm_num)]
          push_cast
          rw [ENNReal.ofReal_pow hm'.le, ENNReal.ofReal_natCast]
          norm_num
        rw [this, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
        have h3 := Real.pi_gt_three
        have hpi2 : 8 < π ^ 2 := by nlinarith
        nlinarith [mul_pos (sub_pos.2 hpi2) (pow_pos hm' 2)])
    refine ⟨u 0, u 1, u 2, u 3, ?_, ?_, ?_, ?_⟩
    · intro h
      apply hu0
      simp only [Prod.mk.injEq] at h
      ext i; fin_cases i <;> simp [h.1, h.2.1, h.2.2.1, h.2.2.2]
    · have := hud 0
      simp [Fin.sum_univ_four] at this
      convert this using 1; ring
    · have := hud 1
      simp [Fin.sum_univ_four] at this
      convert this using 1; ring
    · have : ∑ i, (u i : ℝ) ^ 2 < 2 * m := huC
      rw [Fin.sum_univ_four] at this
      exact_mod_cast this
  refine ⟨hex, ?_⟩
  obtain ⟨a, b, c, d, hne, h1, h2, hlt⟩ := hex
  have hpos : 0 < a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
    by_contra hle
    apply hne
    have ha : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have hb : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have hc : c ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have hd : d ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    rw [pow_eq_zero_iff two_ne_zero] at ha hb hc hd
    rw [ha, hb, hc, hd]
  have hdv : (m : ℤ) ∣ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
    have e : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = (a - (r * c + s * d)) * (a + (r * c + s * d)) +
        (b - (s * c - r * d)) * (b + (s * c - r * d)) + (r ^ 2 + s ^ 2 + 1) * (c ^ 2 + d ^ 2) := by ring
    rw [e]
    exact dvd_add (dvd_add (Dvd.dvd.mul_right h1 _) (Dvd.dvd.mul_right h2 _)) (Dvd.dvd.mul_right hrs _)
  have hmz : (0 : ℤ) < m := by exact_mod_cast hm
  exact ⟨a, b, c, d, ex_eq_of_dvd m _ hmz hdv hpos hlt⟩

/-- **Cassels, Ch. 5, Example 2 (ii)**, first part: *the conditions of (i) hold whenever $m$ is odd or twice an odd
integer.* -/
@[kb "cassels1978" "Ch. 5, Ex. 2 (ii), p. 74"]
theorem ex2_ii (m : ℕ) (h : ¬ 4 ∣ m) : ∃ r s : ℤ, (m : ℤ) ∣ r ^ 2 + s ^ 2 + 1 := by
  revert h
  induction m using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; exact absurd (dvd_zero 4) h
  | one => intro _; exact ⟨0, 0, by simp⟩
  | prime_pow p k hp hk =>
    intro h
    by_cases hp2 : p = 2
    · subst hp2
      have hk1 : k = 1 := by
        by_contra hne
        exact h (by
          have : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
          simpa using this)
      subst hk1
      exact ⟨1, 0, by norm_num⟩
    · have := Fact.mk hp
      obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p (-1)
      have hdv : (p : ℤ) ∣ (a.val : ℤ) ^ 2 + (b.val : ℤ) ^ 2 + 1 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
        linear_combination hab
      have hnd : ∀ x y : ℤ, (p : ℤ) ∣ x ^ 2 + y ^ 2 + 1 → (p : ℤ) ∣ x → ¬ (p : ℤ) ∣ y := by
        intro x y hxy hx hy
        have h1 : (p : ℤ) ∣ x ^ 2 + y ^ 2 :=
          dvd_add (Dvd.dvd.pow hx two_ne_zero) (Dvd.dvd.pow hy two_ne_zero)
        have h2 : (p : ℤ) ∣ 1 := (dvd_add_right h1).mp hxy
        have h3 : p ∣ 1 := by exact_mod_cast h2
        exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
      by_cases hr : (p : ℤ) ∣ (a.val : ℤ)
      · have hs := hnd _ _ hdv hr
        obtain ⟨s', h1, -⟩ := ex_hensel_lift p hp hp2 ((a.val : ℤ) ^ 2 + 1) (b.val : ℤ) hs
          (by have e : (b.val : ℤ) ^ 2 + ((a.val : ℤ) ^ 2 + 1) = (a.val : ℤ) ^ 2 + (b.val : ℤ) ^ 2 + 1 := by ring
              rw [e]; exact hdv) k hk
        refine ⟨(a.val : ℤ), s', ?_⟩
        push_cast
        have e : (a.val : ℤ) ^ 2 + s' ^ 2 + 1 = s' ^ 2 + ((a.val : ℤ) ^ 2 + 1) := by ring
        rw [e]; exact h1
      · obtain ⟨r', h1, -⟩ := ex_hensel_lift p hp hp2 ((b.val : ℤ) ^ 2 + 1) (a.val : ℤ) hr
          (by have e : (a.val : ℤ) ^ 2 + ((b.val : ℤ) ^ 2 + 1) = (a.val : ℤ) ^ 2 + (b.val : ℤ) ^ 2 + 1 := by ring
              rw [e]; exact hdv) k hk
        refine ⟨r', (b.val : ℤ), ?_⟩
        push_cast
        have e : r' ^ 2 + (b.val : ℤ) ^ 2 + 1 = r' ^ 2 + ((b.val : ℤ) ^ 2 + 1) := by ring
        rw [e]; exact h1
  | coprime a b ha hb hab iha ihb =>
    intro h
    exact ex_mul2 a b hab (iha fun hd => h (dvd_mul_of_dvd_left hd b))
      (ihb fun hd => h (dvd_mul_of_dvd_right hd a))

/-- **Cassels, Ch. 5, Example 2 (ii)**, the deduction: *every positive integer is the sum of four squares* (from
`ex2_i` and `ex2_ii`, writing $n = 4^k m$ with $4 \nmid m$). -/
@[kb "cassels1978" "Ch. 5, Ex. 2 (ii), p. 74 (every positive integer is a sum of four squares)"]
theorem ex2_four_squares (n : ℕ) : ∃ a b c d : ℤ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, 0, 0, 0, by simp⟩
    by_cases h4 : 4 ∣ n
    · obtain ⟨k, rfl⟩ := h4
      obtain ⟨a, b, c, d, h⟩ := ih k (by omega)
      exact ⟨2 * a, 2 * b, 2 * c, 2 * d, by push_cast; linear_combination 4 * h⟩
    · obtain ⟨r, s, hrs⟩ := ex2_ii n h4
      exact (ex2_i n hn r s hrs).2

end QuadFormsKB.Cassels.Ch5
