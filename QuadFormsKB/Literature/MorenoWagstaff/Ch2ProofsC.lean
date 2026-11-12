/-
# Moreno–Wagstaff 2005, §7.11: Corollary 7.4

**Proves**
* `corollary74` (Corollary 7.4, **proved**): from `theorem77Corrected` by dividing out the gcd.
-/
import QuadFormsKB.Literature.MorenoWagstaff.Ch6to8Proofs

namespace QuadFormsKB.MorenoWagstaff

private lemma cor74_split (x y z : ℤ) (hx : 0 < x) :
    ∃ k x' y' z' : ℤ, 0 < k ∧ x = k * x' ∧ y = k * y' ∧ z = k * z' ∧
      Int.gcd (Int.gcd x' y') z' = 1 := by
  set d : ℕ := Int.gcd (Int.gcd x y) z with hd
  have hd1 : (d : ℤ) ∣ z := Int.gcd_dvd_right _ _
  have hd2 : (d : ℤ) ∣ (Int.gcd x y : ℤ) := Int.gcd_dvd_left _ _
  have hd3 : (d : ℤ) ∣ x := hd2.trans (Int.gcd_dvd_left _ _)
  have hd4 : (d : ℤ) ∣ y := hd2.trans (Int.gcd_dvd_right _ _)
  have hdpos : 0 < d := by
    rw [hd]
    apply Int.gcd_pos_of_ne_zero_left
    have : 0 < Int.gcd x y := Int.gcd_pos_of_ne_zero_left _ hx.ne'
    omega
  obtain ⟨x', hx'⟩ := hd3
  obtain ⟨y', hy'⟩ := hd4
  obtain ⟨z', hz'⟩ := hd1
  refine ⟨d, x', y', z', by exact_mod_cast hdpos, hx', hy', hz', ?_⟩
  have h1 : Int.gcd x y = d * Int.gcd x' y' := by
    rw [hx', hy', Int.gcd_mul_left]; simp
  have h2 : d = d * Int.gcd (Int.gcd x' y') z' := by
    conv_lhs => rw [hd, h1, hz']
    push_cast
    rw [Int.gcd_mul_left]; simp
  have := Nat.eq_of_mul_eq_mul_left hdpos (by linarith : d * 1 = d * Int.gcd (Int.gcd x' y') z')
  omega

/-- **Moreno–Wagstaff, Corollary 7.4** (p. 315), proved: for `→`, divide by `k = gcd(x, y, z)`, so that
`x' < z'` and `theorem77Corrected` applies; for `←`, `y² - x² = z² - y² = 4k²rs(r+s)(r-s) > 0` by `ring`. -/
@[kb "morenowagstaff2005" "Corollary 7.4, p. 315"]
theorem corollary74 :Corollary74 := by
  intro x y z hx hy hz
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨k, x', y', z', hk, rfl, rfl, rfl, hg⟩ := cor74_split x y z hx
    have hx' : 0 < x' := pos_of_mul_pos_right hx hk.le
    have hy' : 0 < y' := pos_of_mul_pos_right hy hk.le
    have hz' : 0 < z' := pos_of_mul_pos_right hz hk.le
    have hk2 : 0 < k ^ 2 := by positivity
    have hxz : x' < z' := by
      by_contra hc
      rw [not_lt] at hc
      have : z' ^ 2 ≤ x' ^ 2 := by nlinarith
      have : k ^ 2 * z' ^ 2 ≤ k ^ 2 * x' ^ 2 := by nlinarith
      nlinarith
    have hsum : x' ^ 2 + z' ^ 2 = 2 * y' ^ 2 := by
      have : k ^ 2 * (x' ^ 2 + z' ^ 2) = k ^ 2 * (2 * y' ^ 2) := by nlinarith
      exact mul_left_cancel₀ hk2.ne' this
    obtain ⟨r, s, hs, hsr, hc, hpar, e1, e2, e3⟩ :=
      theorem77Corrected x' y' z' hx' hxz hsum hy' hg
    exact ⟨r, s, k, hs, hsr, hc, hpar, hk, by rw [e1], by rw [e2], by rw [e3]⟩
  · rintro ⟨r, s, k, hs, hsr, hc, hpar, hk, rfl, rfl, rfl⟩
    have hk2 : 0 < k ^ 2 := by positivity
    have hP : 0 < r * s * (r + s) * (r - s) := by
      have : 0 < r := by omega
      have : 0 < r + s := by omega
      have : 0 < r - s := by omega
      positivity
    have hsq : (|r ^ 2 - s ^ 2 - 2 * r * s|) ^ 2 = (r ^ 2 - s ^ 2 - 2 * r * s) ^ 2 := sq_abs _
    have e1 : (k * (r ^ 2 + s ^ 2)) ^ 2 - (k * |r ^ 2 - s ^ 2 - 2 * r * s|) ^ 2 =
        4 * k ^ 2 * (r * s * (r + s) * (r - s)) := by
      rw [mul_pow, mul_pow, hsq]; ring
    have e2 : (k * (r ^ 2 - s ^ 2 + 2 * r * s)) ^ 2 - (k * (r ^ 2 + s ^ 2)) ^ 2 =
        4 * k ^ 2 * (r * s * (r + s) * (r - s)) := by ring
    have hpos : 0 < 4 * k ^ 2 * (r * s * (r + s) * (r - s)) := by positivity
    refine ⟨by linarith, by linarith, by linarith⟩

end QuadFormsKB.MorenoWagstaff
