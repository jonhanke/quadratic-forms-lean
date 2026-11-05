import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Berkovich2012.Densities

/-!
# Berkovich–Hanke–Jagy, Lemma 6.3: two identities between the local density formulas

Source: A. Berkovich, J. Hanke and W. Jagy, *A proof of the S-genus identities for ternary
quadratic forms*, arXiv:1010.1926v2 (bib key `berkovich2012`), §6, Lemma 6.3, p. 9.

For an odd prime $p$ and an integer $m \ne 0$, with $\beta_{G,p}$ (`betaG`) the formula of
Lemma 4.2, $\beta_{x^2+y^2+z^2,\,p}$ (`beta3`) the formula of Lemma 4.1, and $\varepsilon = \pm 1$:

* `lemma63_sum`: $\sum_{\varepsilon = \pm 1} \beta_{G,p}(m)\,\frac{p + \varepsilon}{2p}
  = \beta_{x^2+y^2+z^2,\,p}(m)$, where the term with sign $\varepsilon$ uses the genus of sign
  $\varepsilon$;
* `lemma63_signed_sum`: $\sum_{\varepsilon = \pm 1} \varepsilon\,\beta_{G,p}(m)\,
  \frac{p + \varepsilon}{2p} = \beta_{x^2+y^2+z^2,\,p}(m/p^2)$ (`beta3Div`), for $p \mid m$.

*Update (missing hypothesis):* the second identity of Lemma 6.3 requires $p \mid m$ (for
$p \nmid m$ the left side is $(1 + p\chi)/p \ne 0$ while $\beta(m/p^2) = 0$); in Theorem 6.1 it
is applied only for $p \mid W \mid m$. The printed proof also omits the case
$\operatorname{ord}_p(m) = 1$, where both sides are $0$. The failure for $p \nmid m$ is
`lemma63_signed_sum_needs_dvd` ($p = 3$, $m = 1$, where the left side is $-2/3$).
-/

namespace QuadFormsKB.Berkovich2012

/-- If $\operatorname{ord}_p(m)$ is even and $m \ne 0$, then $\chi = \pm 1$. -/
theorem chiOf_eq_one_or_neg_one (p : ℕ) [Fact p.Prime] {m : ℤ} (hm : m ≠ 0)
    (hv : padicValInt p m % 2 = 0) : chiOf p m = 1 ∨ chiOf p m = -1 := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold chiOf
  apply legendreSym.eq_one_or_neg_one
  intro h
  rw [Int.cast_neg, neg_eq_zero, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  obtain ⟨s, hs⟩ : (p : ℤ) ^ padicValInt p m ∣ m := padicValInt_dvd m
  have h2 : 2 * (padicValInt p m / 2) = padicValInt p m := by omega
  have hsf : sqFree p m = s := by
    unfold sqFree
    rw [h2]
    have := Int.mul_ediv_cancel_left s (pow_ne_zero (padicValInt p m) hp0)
    rwa [← hs] at this
  rw [hsf] at h
  obtain ⟨t, ht⟩ := h
  have : (p : ℤ) ^ (padicValInt p m + 1) ∣ m := by
    refine ⟨t, ?_⟩
    rw [pow_succ]
    calc m = (p : ℤ) ^ padicValInt p m * s := hs
      _ = _ := by rw [ht]; ring
  rw [padicValInt_dvd_iff] at this
  omega

/-- If $p^2 \mid m$, $m \ne 0$, then $m/p^2 \ne 0$, its $p$-adic order drops by $2$, and its
$p$-free part `sqFree` is unchanged. -/
theorem div_sq_facts (p : ℕ) [Fact p.Prime] {m : ℤ} (hm : m ≠ 0) (h : (p : ℤ) ^ 2 ∣ m) :
    m / (p : ℤ) ^ 2 ≠ 0 ∧ padicValInt p (m / (p : ℤ) ^ 2) + 2 = padicValInt p m ∧
      sqFree p (m / (p : ℤ) ^ 2) = sqFree p m := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨n, rfl⟩ := h
  have hn : n ≠ 0 := by rintro rfl; simp at hm
  have hd : (p : ℤ) ^ 2 * n / (p : ℤ) ^ 2 = n := Int.mul_ediv_cancel_left _ (pow_ne_zero _ hp0)
  rw [hd]
  have hv : padicValInt p ((p : ℤ) ^ 2 * n) = padicValInt p n + 2 := by
    have : (p : ℤ) ^ 2 * n = n * p * p := by ring
    rw [this, padicValInt_mul_eq_succ _ (mul_ne_zero hn hp0), padicValInt_mul_eq_succ _ hn]
  refine ⟨hn, by omega, ?_⟩
  unfold sqFree
  rw [hv]
  have e : 2 * ((padicValInt p n + 2) / 2) = 2 + 2 * (padicValInt p n / 2) := by omega
  rw [e, pow_add]
  have hq : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero _ hp0
  have hq' : (0 : ℤ) < (p : ℤ) ^ 2 := by
    have : 0 < p := (Fact.out : p.Prime).pos
    positivity
  exact (Int.mul_ediv_mul_of_pos _ _ hq').symm

theorem chiOf_div_sq (p : ℕ) [Fact p.Prime] {m : ℤ} (hm : m ≠ 0) (h : (p : ℤ) ^ 2 ∣ m) :
    chiOf p (m / (p : ℤ) ^ 2) = chiOf p m := by
  unfold chiOf
  rw [(div_sq_facts p hm h).2.2]

theorem geomSum_succ (p k : ℕ) : geomSum p (k + 1) = geomSum p k + (1 / (p : ℚ)) ^ k := by
  unfold geomSum
  rw [Finset.sum_range_succ]

/-- **Lemma 6.3, first identity.** For an odd prime $p$ and $m \ne 0$:
$\sum_{\varepsilon = \pm 1} \beta_{G,p}(m)\,\frac{p + \varepsilon}{2p} = \beta_{x^2+y^2+z^2,\,p}(m)$. -/
@[kb "berkovich2012" "§6, Lemma 6.3, p. 9"]
theorem lemma63_sum (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {m : ℤ} (hm : m ≠ 0) :
    betaG p 1 m * (p + 1) / (2 * p) + betaG p (-1) m * (p - 1) / (2 * p) = beta3 p m := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨k, hk | hk⟩ : ∃ k, padicValInt p m = 2 * k ∨ padicValInt p m = 2 * k + 1 :=
    ⟨padicValInt p m / 2, by omega⟩
  · have h1 : 2 * k / 2 = k := by omega
    have h2 : 2 * k % 2 = 0 := by omega
    rcases chiOf_eq_one_or_neg_one p hm (by omega) with hc | hc <;>
    · simp only [betaG, beta3, hk, h1, h2, ite_true, hc]
      simp only [one_div, inv_pow]
      push_cast
      field_simp
      ring
  · have h1 : (2 * k + 1) / 2 = k := by omega
    have h2 : ¬ (2 * k + 1) % 2 = 0 := by omega
    simp only [betaG, beta3, hk, h1, h2, ite_false, geomSum_succ]
    simp only [one_div, inv_pow]
    push_cast
    field_simp
    ring

/-- **Lemma 6.3, second identity** (with the hypothesis $p \mid m$; see the file header).
$\sum_{\varepsilon = \pm 1} \varepsilon\,\beta_{G,p}(m)\,\frac{p + \varepsilon}{2p}
= \beta_{x^2+y^2+z^2,\,p}(m/p^2)$, interpreted as $0$ when $p^2 \nmid m$. -/
@[kb "berkovich2012" "§6, Lemma 6.3, p. 9"]
theorem lemma63_signed_sum (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {m : ℤ} (hm : m ≠ 0)
    (hpm : (p : ℤ) ∣ m) :
    betaG p 1 m * (p + 1) / (2 * p) - betaG p (-1) m * (p - 1) / (2 * p) = beta3Div p m := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hv1 : 1 ≤ padicValInt p m := by
    have := (padicValInt_dvd_iff (p := p) 1 m).1 (by simpa using hpm)
    omega
  have hdiv : ((p : ℤ) ^ 2 ∣ m) ↔ 2 ≤ padicValInt p m := by
    rw [padicValInt_dvd_iff]; simp [hm]
  obtain ⟨k, hk | hk⟩ : ∃ k, padicValInt p m = 2 * k ∨ padicValInt p m = 2 * k + 1 :=
    ⟨padicValInt p m / 2, by omega⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hd : (p : ℤ) ^ 2 ∣ m := hdiv.2 (by omega)
    obtain ⟨hne, hv, -⟩ := div_sq_facts p hm hd
    have hv' : padicValInt p (m / (p : ℤ) ^ 2) = 2 * j := by omega
    have h1 : 2 * (j + 1) / 2 = j + 1 := by omega
    have h2 : 2 * (j + 1) % 2 = 0 := by omega
    have h3 : 2 * j / 2 = j := by omega
    have h4 : 2 * j % 2 = 0 := by omega
    have hchi := chiOf_div_sq p hm hd
    rcases chiOf_eq_one_or_neg_one p hm (by omega) with hc | hc <;>
    · rw [hc] at hchi
      simp only [beta3Div, hd, betaG, beta3, hk, hv', h1, h2, h3, h4, ite_true, hc, hchi,
        geomSum_succ]
      simp only [one_div, inv_pow]
      push_cast
      field_simp
      ring
  · rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have hnd : ¬ (p : ℤ) ^ 2 ∣ m := fun h => by have := hdiv.1 h; omega
      have h2 : ¬ (2 * 0 + 1) % 2 = 0 := by omega
      simp only [beta3Div, hnd, betaG, hk, h2, ite_false]
      simp [geomSum]
      field_simp
      ring
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hd : (p : ℤ) ^ 2 ∣ m := hdiv.2 (by omega)
      obtain ⟨hne, hv, -⟩ := div_sq_facts p hm hd
      have hv' : padicValInt p (m / (p : ℤ) ^ 2) = 2 * j + 1 := by omega
      have h1 : (2 * (j + 1) + 1) / 2 = j + 1 := by omega
      have h2 : ¬ (2 * (j + 1) + 1) % 2 = 0 := by omega
      have h3 : (2 * j + 1) / 2 = j := by omega
      have h4 : ¬ (2 * j + 1) % 2 = 0 := by omega
      simp only [beta3Div, hd, betaG, beta3, hk, hv', h1, h2, h3, h4, ite_false,
        geomSum_succ]
      simp only [one_div, inv_pow]
      push_cast
      field_simp
      ring

/-- The hypothesis $p \mid m$ in `lemma63_signed_sum` is needed: for $p = 3$, $m = 1$ the left
side is $-2/3$, while $\beta_{x^2+y^2+z^2,\,3}(1/9) = 0$ (`beta3Div 3 1 = 0`). -/
theorem lemma63_signed_sum_needs_dvd :
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    betaG 3 1 1 * (3 + 1) / (2 * 3) - betaG 3 (-1) 1 * (3 - 1) / (2 * 3) = -2 / 3 ∧
      beta3Div 3 1 = 0 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hv : padicValInt 3 1 = 0 := by simp
  have hs : sqFree 3 1 = 1 := by simp [sqFree, hv]
  have hc : chiOf 3 1 = -1 := by
    unfold chiOf
    rw [hs]
    have : legendreSym 3 (-1) = -1 := by
      rw [legendreSym.at_neg_one (by decide)]
      decide
    simpa using this
  refine ⟨?_, ?_⟩
  · simp only [betaG, hv, hc]
    norm_num [geomSum]
  · simp [beta3Div]

end QuadFormsKB.Berkovich2012
