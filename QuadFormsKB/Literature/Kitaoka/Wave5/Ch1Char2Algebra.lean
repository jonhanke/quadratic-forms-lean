/-
# Kitaoka 1993, Theorem 1.3.2 in characteristic $2$: the algebra of $r'(V, W)$

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §1.3, proof of Theorem 1.3.2, p. 16 (printed page):
"It is easy to verify $r'(U \perp U_1, U \perp U_2) = r'(U, U \perp U_2)\,r'(U_1, U_2)$ … for a hyperbolic plane $U$ if
$\operatorname{ch} F = 2$", here for every regular plane $U$ (with $\chi(U_2) = \chi(U)\chi(U \perp U_2)$).

**Proves** identities for `rForm` (Kitaoka's $r'$) with $v = \dim V$ and $w = \dim W$ even:
* `rForm_two`: the value for $v = 2$;
* `rForm_step_plane`: $r'(2, w)\,r'(2n, w - 2) = r'(2n + 2, w)$ with the $\chi$ values of a plane;
* `rForm_hyp`, `rForm_aniso`, `rForm_aniso_two`: the three plane counts of `Ch1Char2PlaneCount.lean` agree with
  $r'$.
-/
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch1IsometryCountProof

open Module

noncomputable section

namespace QuadFormsKB.Kitaoka.FqCount

/-- Real powers with an integral exponent. -/
theorem rpow_int' {q : ℝ} (hq : 0 < q) {x : ℝ} (z : ℤ) (hx : x = z) : q ^ x = q ^ z := by
  rw [hx, Real.rpow_intCast]

/-- $r'(2n, 2m)$ with natural-number exponents ($n \le m$). -/
theorem rForm_even {q : ℝ} (hq : 0 < q) (n m : ℕ) (hnm : n ≤ m) (cW c : ℝ) :
    rForm q (2 * n) (2 * m) cW c = q ^ (4 * n * m) / q ^ (n * (2 * n + 1)) * (1 - cW * (q ^ m)⁻¹) *
      (1 + c * (q ^ (m - n))⁻¹) * ∏ e ∈ (Finset.Icc (2 * m - 2 * n + 1) (2 * m - 1)).filter Even, (1 - (q ^ e)⁻¹) := by
  have e1 : (-((2 * m : ℕ) : ℝ) / 2) = ((-(m : ℤ) : ℤ) : ℝ) := by push_cast; ring
  have e2 : (((2 * n : ℕ) : ℝ) - ((2 * m : ℕ) : ℝ)) / 2 = ((-((m - n : ℕ) : ℤ) : ℤ) : ℝ) := by
    push_cast [Nat.cast_sub hnm]; ring
  have e3 : ((2 * n : ℕ) : ℤ) * ((2 * m : ℕ) : ℤ) - ((2 * n * (2 * n + 1) / 2 : ℕ) : ℤ) =
      ((4 * n * m : ℕ) : ℤ) - ((n * (2 * n + 1) : ℕ) : ℤ) := by
    rw [show 2 * n * (2 * n + 1) / 2 = n * (2 * n + 1) by
      rw [show 2 * n * (2 * n + 1) = 2 * (n * (2 * n + 1)) by ring]; omega]
    push_cast; ring
  unfold rForm
  rw [e1, e2, e3, Real.rpow_intCast, Real.rpow_intCast, zpow_sub₀ hq.ne', zpow_natCast, zpow_natCast]
  simp only [zpow_neg, zpow_natCast, div_eq_mul_inv]

/-- $r'(2, 2k + 2) = q^{4k+1}(1 - \chi(W)q^{-(k+1)})(1 + c\,q^{-k})$. -/
theorem rForm_two {q : ℝ} (hq : 0 < q) (k : ℕ) (cW c : ℝ) :
    rForm q 2 (2 * k + 2) cW c = q ^ (4 * k + 1) * (1 - cW * (q ^ (k + 1))⁻¹) * (1 + c * (q ^ k)⁻¹) := by
  have h := rForm_even hq 1 (k + 1) (by omega) cW c
  have hempty : (Finset.Icc (2 * (k + 1) - 2 * 1 + 1) (2 * (k + 1) - 1)).filter Even = ∅ := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false, Nat.even_iff]
    omega
  rw [hempty, Finset.prod_empty, mul_one, show k + 1 - 1 = k by omega] at h
  rw [show (2 : ℕ) = 2 * 1 from rfl, show 2 * k + 2 = 2 * (k + 1) by ring, h]
  have : q ^ (4 * 1 * (k + 1)) / q ^ (1 * (2 * 1 + 1)) = q ^ (4 * k + 1) := by
    rw [div_eq_iff (pow_ne_zero _ hq.ne'), ← pow_add]; ring_nf
  rw [this, mul_one]

/-- **The step**: for $1 \le n \le k$, $c_A^2 = c_W^2 = 1$,
$r'(2, 2k+2; c_W, c_Ac_W)\,r'(2n, 2k; c_Ac_W, c) = r'(2n + 2, 2k + 2; c_W, c)$. -/
theorem rForm_step_plane {q : ℝ} (hq : 0 < q) {n k : ℕ} (hn : 1 ≤ n) (hnk : n ≤ k) {cA cW : ℝ}
    (hA : cA * cA = 1) (hW : cW * cW = 1) (c : ℝ) :
    rForm q 2 (2 * k + 2) cW (cA * cW) * rForm q (2 * n) (2 * k) (cA * cW) c =
      rForm q (2 * n + 2) (2 * k + 2) cW c := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, k = p + 1 + d := ⟨k - (p + 1), by omega⟩
  have hnot : 2 * (p + 1 + d) ∉ (Finset.Icc (2 * (p + 1 + d) - 2 * (p + 1) + 1) (2 * (p + 1 + d) - 1)).filter Even := by
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have hP : (Finset.Icc (2 * (p + 1 + d + 1) - 2 * (p + 1 + 1) + 1) (2 * (p + 1 + d + 1) - 1)).filter Even =
      insert (2 * (p + 1 + d)) ((Finset.Icc (2 * (p + 1 + d) - 2 * (p + 1) + 1) (2 * (p + 1 + d) - 1)).filter Even) := by
    ext e
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc, Nat.even_iff]
    omega
  rw [rForm_two hq, rForm_even hq _ _ (by omega), show 2 * (p + 1) + 2 = 2 * (p + 1 + 1) by ring,
    show 2 * (p + 1 + d) + 2 = 2 * (p + 1 + d + 1) by ring, rForm_even hq _ _ (by omega), hP,
    Finset.prod_insert hnot, show p + 1 + d - (p + 1) = d by omega, show p + 1 + d + 1 - (p + 1 + 1) = d by omega]
  have h1 : (q ^ (p + 1 + d + 1)) ≠ 0 := pow_ne_zero _ hq.ne'
  have h2 : (q ^ (p + 1 + d)) ≠ 0 := pow_ne_zero _ hq.ne'
  have h3 : (q ^ d) ≠ 0 := pow_ne_zero _ hq.ne'
  have h4 : q ^ (2 * (p + 1 + d)) = q ^ (p + 1 + d) * q ^ (p + 1 + d) := by rw [← pow_add]; ring_nf
  rw [h4]
  rcases mul_self_eq_one_iff.mp hA with rfl | rfl <;> rcases mul_self_eq_one_iff.mp hW with rfl | rfl <;>
    field_simp <;> ring

end QuadFormsKB.Kitaoka.FqCount
