/-
# Moreno–Wagstaff 2005, §2.2: Legendre's theorem on sums of five polygonal numbers

**Source.** A.-M. Legendre (1830); C. J. Moreno and S. S. Wagstaff Jr., *Sums of Squares of Integers* (2005),
Theorem 2.10 (p. 57), which the book cites without proof; the proof here is Nathanson's version
(*Additive Number Theory: The Classical Bases*, Ch. 1).

**Proves**
* `theorem210` (**proved**, unconditional): for $m \ge 3$ and $n \ge 28 m^3$, $n$ is a sum of four
  $(m+2)$-gonal numbers if $m$ is odd, and of five of them (the fifth being $0$ or $1$) if $m$ is even.

**Method.** Nathanson's interval argument via Cauchy's lemma (`lemma27`, through `adm_realized`): it suffices to
write $N = m a + s$ with `Adm a s`, since then four $(m+2)$-gonal numbers sum to $N$ (`poly_sum`). The admissible
$s$ form an interval whose length exceeds $2m$ once $N \ge 28 m^3 - 1$ (this is the role of the constant $28 m^3$),
so it contains an $s$ in the residue class modulo $m$ (and modulo $2$, i.e. $s$ odd) that is needed. Here the
interval is found explicitly: $s_0$ is the least $s$ with $6N + ms < ms^2 + 6s + 4m$ (the first inequality of
`Adm`, times $m$), and all of $s_0, \dots, s_0 + 2m - 1$ satisfy the second inequality.
-/
import QuadFormsKB.Literature.MorenoWagstaff.Ch2Cauchy

namespace QuadFormsKB.MorenoWagstaff

namespace Legendre

open QuadFormsKB.MorenoWagstaff.Cauchy

/-- Step 2 of the interval argument (in $\mathbb Z$). -/
theorem key (m N u : ℤ) (hm : 3 ≤ m) (hN : 28 * m ^ 3 ≤ N + 1) (hu : 0 ≤ u)
    (hnP : m * u ^ 2 + 6 * u + 4 * m ≤ 6 * N + m * u) :
    (4 * m ^ 2 - 3 * m + 2) * u + 4 * m ^ 3 - 8 * m ^ 2 + 12 * m < 2 * N := by
  by_contra h
  push_neg at h
  have hm0 : 0 < m := by linarith
  have h3 : m * u ^ 2 ≤ (12 * m ^ 2 - 8 * m) * u + 12 * m ^ 3 - 24 * m ^ 2 + 32 * m := by
    nlinarith
  have hu13 : u < 13 * m := by
    by_contra hc
    push_neg at hc
    have hq : u ^ 2 ≤ (12 * m - 8) * u + 12 * m ^ 2 - 24 * m + 32 := by
      by_contra hq
      push_neg at hq
      have := mul_lt_mul_of_pos_left hq hm0
      nlinarith
    nlinarith [mul_nonneg (sub_nonneg.2 hc) (show (0:ℤ) ≤ u - 12 * m + 8 by linarith),
      mul_nonneg hm0.le (sub_nonneg.2 hc)]
  have hpos : 0 ≤ 4 * m ^ 2 - 3 * m + 2 := by nlinarith
  have := mul_le_mul_of_nonneg_left hu13.le hpos
  nlinarith

/-- Step 3 of the interval argument (in $\mathbb Z$): the second inequality of `Adm`, times $m$. -/
theorem step3 (m N u s : ℤ) (hm : 3 ≤ m) (hu : 0 ≤ u)
    (hnP : m * u ^ 2 + 6 * u + 4 * m ≤ 6 * N + m * u)
    (H2 : (4 * m ^ 2 - 3 * m + 2) * u + 4 * m ^ 3 - 8 * m ^ 2 + 12 * m < 2 * N)
    (h1 : u + 1 ≤ s) (h2 : s ≤ u + 2 * m) :
    m * s ^ 2 + 8 * s < 8 * N + 4 * m * s := by
  have hf : m * s ^ 2 - (4 * m - 8) * s ≤ m * (u + 2 * m) ^ 2 - (4 * m - 8) * (u + 2 * m) := by
    nlinarith [mul_nonneg (sub_nonneg.2 h2)
      (show (0:ℤ) ≤ m * (u + 2 * m + s) - (4 * m - 8) by nlinarith)]
  nlinarith

/-- Residue selection: in any window of length `L` there is an element of each residue class. -/
theorem exists_d (L s₀ c : ℤ) (hL : 0 < L) :
    ∃ d q : ℤ, 0 ≤ d ∧ d < L ∧ s₀ + d = c + L * q := by
  refine ⟨(c - s₀) % L, -((c - s₀) / L), Int.emod_nonneg _ hL.ne', Int.emod_lt_of_pos _ hL, ?_⟩
  have := Int.emod_add_mul_ediv (c - s₀) L
  have h2 : (c - s₀) % L = c - s₀ - L * ((c - s₀) / L) := by linarith
  rw [h2]; ring

/-- Choice of the residue data: `N = c + m k` with `c` odd and `m e` even, `e ∈ {1, 2}`. -/
theorem residue_data (m N : ℕ) (hm : 3 ≤ m) (hNm : m ≤ N) (hpar : Even m → Odd N) :
    ∃ c k e : ℕ, 0 < e ∧ e ≤ 2 ∧ Even (m * e) ∧ Odd c ∧ N = c + m * k := by
  have hdm := Nat.mod_add_div N m
  rcases Nat.even_or_odd m with he | ho
  · refine ⟨N % m, N / m, 1, by omega, by omega, by simpa using he, ?_, hdm.symm⟩
    have hev : Even (m * (N / m)) := he.mul_right _
    obtain ⟨r, hr⟩ := hev
    obtain ⟨j, hj⟩ := hpar he
    refine ⟨j - r, ?_⟩
    omega
  · have h2 : Even (m * 2) := ⟨m, by ring⟩
    have hd : 1 ≤ N / m := Nat.div_pos hNm (by omega)
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le' hd
    rcases Nat.even_or_odd (N % m) with hc | hc
    · refine ⟨N % m + m, j, 2, by omega, le_rfl, h2, hc.add_odd ho, ?_⟩
      have : m * (N / m) = m * j + m := by rw [hj]; ring
      omega
    · exact ⟨N % m, N / m, 2, by omega, le_rfl, h2, hc, hdm.symm⟩

/-- The core lemma: every `N ≥ 28 m³ - 1` (odd if `m` is even) is `m a + s` with `Adm a s`. -/
theorem core (m N : ℕ) (hm : 3 ≤ m) (hN : 28 * m ^ 3 ≤ N + 1) (hpar : Even m → Odd N) :
    ∃ a s : ℕ, N = m * a + s ∧ Adm a s := by
  have hm3 : m ^ 3 = m * m * m := by ring
  have hmN : m ≤ N := by nlinarith [Nat.mul_le_mul hm hm]
  have hex : ∃ s : ℕ, 6 * N + m * s < m * s ^ 2 + 6 * s + 4 * m :=
    ⟨N + 1, by nlinarith⟩
  obtain ⟨s₀, hP, hmin⟩ : ∃ s₀ : ℕ, 6 * N + m * s₀ < m * s₀ ^ 2 + 6 * s₀ + 4 * m ∧
      ∀ j < s₀, ¬ (6 * N + m * j < m * j ^ 2 + 6 * j + 4 * m) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  obtain ⟨u, rfl⟩ : ∃ u, s₀ = u + 1 := by
    rcases s₀ with _ | u
    · exfalso
      simp at hP
      nlinarith [Nat.mul_le_mul hm hm]
    · exact ⟨u, rfl⟩
  have hnP := hmin u (Nat.lt_succ_self u)
  push_neg at hnP
  obtain ⟨c, k, e, he0, he2, hE, hc, hNck⟩ := residue_data m N hm hmN hpar
  -- integer versions
  have hmZ : (3:ℤ) ≤ m := by exact_mod_cast hm
  have hNZ : 28 * (m:ℤ) ^ 3 ≤ N + 1 := by exact_mod_cast hN
  have hnPZ : (m:ℤ) * u ^ 2 + 6 * u + 4 * m ≤ 6 * N + m * u := by exact_mod_cast hnP
  have hPZ : 6 * (N:ℤ) + m * (u + 1) < m * (u + 1) ^ 2 + 6 * (u + 1) + 4 * m := by
    exact_mod_cast hP
  have H2 := key m N u hmZ hNZ (by positivity) hnPZ
  have hNckZ : (N:ℤ) = c + m * k := by exact_mod_cast hNck
  have heZ : (0:ℤ) < e := by exact_mod_cast he0
  have heZ2 : (e:ℤ) ≤ 2 := by exact_mod_cast he2
  obtain ⟨d, q, hd0, hdL, hdq⟩ :=
    exists_d ((m:ℤ) * e) ((u:ℤ) + 1) c (by positivity)
  have hme : (m:ℤ) * e ≤ 2 * m := by nlinarith
  set s : ℤ := c + m * e * q with hs
  have hs1 : (u:ℤ) + 1 ≤ s := by linarith
  have hs2 : s ≤ u + 2 * m := by linarith
  have hsN : s ≤ N := by nlinarith
  have hs0 : 0 ≤ s := by linarith
  have hma : (m:ℤ) * (k - e * q) = N - s := by rw [hNckZ, hs]; ring
  have ha0 : 0 ≤ (k:ℤ) - e * q := by
    by_contra h
    push_neg at h
    nlinarith
  obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le ha0
  obtain ⟨s', hs'⟩ := Int.eq_ofNat_of_zero_le hs0
  rw [ha] at hma
  rw [hs'] at hma hs1 hs2 hsN
  have hmaN : (m:ℤ) * a + s' = N := by linarith
  have hsodd : Odd s' := by
    have hcZ : Odd (c:ℤ) := (Int.odd_coe_nat c).2 hc
    have hEZ : Even ((m:ℤ) * e) := by exact_mod_cast hE
    have : Odd ((c:ℤ) + m * e * q) := hcZ.add_even (hEZ.mul_right q)
    rw [← hs, hs'] at this
    exact (Int.odd_coe_nat s').1 this
  refine ⟨a, s', by exact_mod_cast hmaN.symm, hsodd, ?_, ?_⟩
  · -- first inequality
    have hge : (u:ℤ) + 1 ≤ s' := hs1
    have hP' : 6 * (N:ℤ) + m * s' < m * s' ^ 2 + 6 * s' + 4 * m := by
      have hq : (0:ℤ) ≤ m * (s' + u) := by positivity
      have hq2 : (0:ℤ) ≤ m * (s' + (u + 1)) + 6 - m := by linarith
      linarith [mul_nonneg (sub_nonneg.2 hge) hq2]
    have : (6 * a + s' : ℤ) < s' ^ 2 + 4 := by
      by_contra h
      push_neg at h
      have := mul_le_mul_of_nonneg_left h (show (0:ℤ) ≤ m by linarith)
      linarith
    exact_mod_cast this
  · have h3 := step3 m N u s' hmZ (by positivity) hnPZ H2 hs1 hs2
    have : (s' ^ 2 : ℤ) < 8 * a + 4 * s' := by
      by_contra h
      push_neg at h
      have := mul_le_mul_of_nonneg_left h (show (0:ℤ) ≤ m by linarith)
      linarith
    exact_mod_cast this

end Legendre

/-- **Moreno–Wagstaff, Theorem 2.10** (Legendre 1830; p. 57): for $m \ge 3$ and $n \ge 28 m^3$, $n$ is a sum of
four $(m+2)$-gonal numbers when $m$ is odd, and of five when $m$ is even (the fifth being $0$ or $1$).
Proved unconditionally via Nathanson's interval argument (`Legendre.core`) and Cauchy's lemma. -/
theorem theorem210 : Theorem210 := by
  intro m n hm hn
  have hn' : 28 * m ^ 3 ≤ n + 1 := Nat.le_succ_of_le hn
  have hpos : 0 < m ^ 3 := by positivity
  refine ⟨fun he => ?_, fun ho => ?_⟩
  · by_cases hodd : Odd n
    · obtain ⟨a, s, hN, hadm⟩ := Legendre.core m n hm hn' (fun _ => hodd)
      obtain ⟨t, u, v, w, e⟩ := Cauchy.poly_sum m a s (Cauchy.adm_realized hadm)
      refine ⟨t, u, v, w, 0, by omega, ?_⟩
      have h0 : polygonal (m + 2) 0 = 0 := by simp [polygonal]
      rw [h0]; linarith
    · have hev : Even n := Nat.not_odd_iff_even.1 hodd
      have hodd' : Odd (n - 1) := by
        obtain ⟨r, hr⟩ := hev
        exact ⟨r - 1, by omega⟩
      obtain ⟨a, s, hN, hadm⟩ :=
        Legendre.core m (n - 1) hm (by omega) (fun _ => hodd')
      obtain ⟨t, u, v, w, e⟩ := Cauchy.poly_sum m a s (Cauchy.adm_realized hadm)
      refine ⟨t, u, v, w, 1, le_rfl, ?_⟩
      have h1 : polygonal (m + 2) 1 = 1 := by simp [polygonal]
      have h3 : n - 1 + 1 = n := by omega
      rw [h1]; linarith
  · obtain ⟨a, s, hN, hadm⟩ := Legendre.core m n hm hn'
      (fun h => absurd h (Nat.not_even_iff_odd.2 ho))
    obtain ⟨t, u, v, w, e⟩ := Cauchy.poly_sum m a s (Cauchy.adm_realized hadm)
    exact ⟨t, u, v, w, by linarith⟩

end QuadFormsKB.MorenoWagstaff
