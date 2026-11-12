/-
# Moreno–Wagstaff 2005, Chapters 6–8: proofs

**Source.** C. J. Moreno and S. S. Wagstaff Jr., *Sums of Squares of Integers* (2005), Chapters 6–8.

**Proves**
* `theorem81` (Theorem 8.1, **proved**): with $P = ad + bc$, $M = ad - bc$ one has $n^2 = (ac-bd)^2 + P^2$,
  $PM = (d^2 - b^2) n$, hence $0 < |M| < P < n$ and neither gcd can be $1$.
* `lemma61` (Lemma 6.1, **proved**): injectivity by the Chinese-remainder argument, then equal cardinalities.
-/
import QuadFormsKB.Literature.MorenoWagstaff.Ch6to8Statements

namespace QuadFormsKB.MorenoWagstaff

/-- **Moreno–Wagstaff, Theorem 8.1** (p. 318), proved: $0 < |ad-bc| < ad+bc < n$ and $n \mid (ad+bc)(ad-bc)$,
so a gcd equal to $1$ would force $n$ to divide the other factor. -/
@[kb "morenowagstaff2005" "Theorem 8.1, p. 318"]
theorem theorem81 : Theorem81 := by
  intro n a b c d ha hb hc hd hn1 hn2 hab hcd hne1 hne2
  have hn1' : (n : ℤ) = a ^ 2 + b ^ 2 := by exact_mod_cast hn1
  have hn2' : (n : ℤ) = c ^ 2 + d ^ 2 := by exact_mod_cast hn2
  have hab' : IsCoprime (a : ℤ) b := Nat.isCoprime_iff_coprime.2 hab
  have hcd' : IsCoprime (c : ℤ) d := Nat.isCoprime_iff_coprime.2 hcd
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  have hc' : (0 : ℤ) < c := by exact_mod_cast hc
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have hnpos : (0 : ℤ) < n := by rw [hn1']; positivity
  have hP : (0 : ℤ) < a * d + b * c := by positivity
  have key : ((a : ℤ) * c - b * d) ^ 2 + (a * d + b * c) ^ 2 = (n : ℤ) ^ 2 := by
    calc ((a : ℤ) * c - b * d) ^ 2 + (a * d + b * c) ^ 2 = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by ring
      _ = (n : ℤ) ^ 2 := by rw [← hn1', ← hn2']; ring
  have hc2 : (c : ℤ) ^ 2 = a ^ 2 + b ^ 2 - d ^ 2 := by linarith
  have hPM : ((a : ℤ) * d + b * c) * (a * d - b * c) = n * (d ^ 2 - b ^ 2) := by
    linear_combination (-((b : ℤ) ^ 2)) * hc2 - ((d : ℤ) ^ 2 - b ^ 2) * hn1'
  have hlt : (a : ℤ) * d + b * c < n := by
    by_contra h
    push Not at h
    have h0 : ((a : ℤ) * c - b * d) ^ 2 = 0 := by
      nlinarith [sq_nonneg ((a : ℤ) * c - b * d), mul_self_le_mul_self hnpos.le h]
    have h1 : (a : ℤ) * c = b * d := by
      have := pow_eq_zero_iff (two_ne_zero) |>.1 h0
      linarith
    have h2 : (a : ℤ) ∣ d := by
      have : (a : ℤ) ∣ d * b := ⟨c, by linarith⟩
      exact hab'.dvd_of_dvd_mul_right this
    have h3 : (d : ℤ) ∣ a := by
      have : (d : ℤ) ∣ a * c := ⟨b, by linarith⟩
      exact hcd'.symm.dvd_of_dvd_mul_right this
    have h4 : (a : ℤ) = d := le_antisymm (Int.le_of_dvd hd' h2) (Int.le_of_dvd ha' h3)
    have h5 : (c : ℤ) = b := by
      rw [← h4] at h1
      exact (mul_left_cancel₀ ha'.ne' (by linarith : (a : ℤ) * c = a * b))
    apply hne2
    exact ⟨by exact_mod_cast h4, by exact_mod_cast h5.symm⟩
  have hM0 : (a : ℤ) * d - b * c ≠ 0 := by
    intro h
    have h1 : (a : ℤ) * d = b * c := by linarith
    have h2 : (a : ℤ) ∣ c := by
      have : (a : ℤ) ∣ c * b := ⟨d, by linarith⟩
      exact hab'.dvd_of_dvd_mul_right this
    have h3 : (c : ℤ) ∣ a := by
      have : (c : ℤ) ∣ a * d := ⟨b, by linarith⟩
      exact hcd'.dvd_of_dvd_mul_right this
    have h4 : (a : ℤ) = c := le_antisymm (Int.le_of_dvd hc' h2) (Int.le_of_dvd ha' h3)
    have h5 : (d : ℤ) = b := by
      rw [← h4] at h1
      exact (mul_left_cancel₀ ha'.ne' (by linarith : (a : ℤ) * d = a * b))
    apply hne1
    exact ⟨by exact_mod_cast h4, by exact_mod_cast h5.symm⟩
  have hMabs : |(a : ℤ) * d - b * c| < a * d + b * c := by
    rw [abs_lt]; constructor <;> nlinarith [mul_pos ha' hd', mul_pos hb' hc']
  have hdvd : (n : ℤ) ∣ ((a : ℤ) * d + b * c) * (a * d - b * c) := ⟨_, hPM⟩
  have hPn : (a * d + b * c : ℕ) < n := by zify; exact hlt
  have hPpos : 0 < a * d + b * c := by positivity
  constructor
  · refine ⟨?_, lt_of_le_of_lt (Nat.le_of_dvd hPpos (Nat.gcd_dvd_left _ _)) hPn⟩
    have hg0 : Nat.gcd (a * d + b * c) n ≠ 0 := by
      intro h; rw [Nat.gcd_eq_zero_iff] at h; omega
    by_contra hg
    have hg1 : Nat.gcd (a * d + b * c) n = 1 := by omega
    have hcop : IsCoprime ((n : ℤ)) ((a * d + b * c : ℕ) : ℤ) :=
      (Nat.isCoprime_iff_coprime.2 (Nat.coprime_comm.1 hg1))
    have hdM : (n : ℤ) ∣ (a : ℤ) * d - b * c := hcop.dvd_of_dvd_mul_left hdvd
    have := Int.le_of_dvd (abs_pos.2 hM0) ((dvd_abs _ _).2 hdM)
    have : (n : ℤ) < n := by linarith
    exact lt_irrefl _ this
  · have hbd : Int.gcd ((a * d : ℤ) - b * c) n ≤ ((a : ℤ) * d - b * c).natAbs := by
      have h1 : Int.gcd ((a * d : ℤ) - b * c) n = Nat.gcd ((a * d : ℤ) - b * c).natAbs n := rfl
      rw [h1]
      exact Nat.gcd_le_left _ (Int.natAbs_pos.2 hM0)
    have hMn : ((a : ℤ) * d - b * c).natAbs < n := by
      have : (((a : ℤ) * d - b * c).natAbs : ℤ) < n := by
        rw [Int.natCast_natAbs]; exact lt_trans hMabs hlt
      exact_mod_cast this
    refine ⟨?_, lt_of_le_of_lt hbd hMn⟩
    have hg0 : Int.gcd ((a * d : ℤ) - b * c) n ≠ 0 := by
      intro h; rw [Int.gcd_eq_zero_iff] at h; exact hM0 h.1
    by_contra hg
    have hg1 : Int.gcd ((a * d : ℤ) - b * c) n = 1 := by omega
    have hcop : IsCoprime ((n : ℤ)) ((a : ℤ) * d - b * c) :=
      (Int.isCoprime_iff_gcd_eq_one.2 hg1).symm
    have hdP : (n : ℤ) ∣ (a : ℤ) * d + b * c := hcop.dvd_of_dvd_mul_right hdvd
    have := Int.le_of_dvd hP hdP
    linarith

/-- **Moreno–Wagstaff, Lemma 6.1** (p. 201), proved: injectivity from the Chinese-remainder argument
($k'(j - i) \equiv 0 \bmod k$ etc.), then bijectivity since both sides have $k k'$ elements. -/
@[kb "morenowagstaff2005" "Lemma 6.1, p. 201"]
theorem lemma61 : Lemma61 := by
  intro k k' hk hk' hcop
  have : NeZero k := ⟨hk.ne'⟩
  have : NeZero k' := ⟨hk'.ne'⟩
  have : NeZero (k * k') := ⟨(Nat.mul_pos hk hk').ne'⟩
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp [ZMod.card]⟩
  rintro ⟨i, i'⟩ ⟨j, j'⟩ h
  simp only at h
  rw [ZMod.natCast_eq_natCast_iff] at h
  have h1 : k' * i ≡ k' * j [MOD k] := by
    have := h.of_mul_right k'
    unfold Nat.ModEq at *
    simpa [Nat.add_mod, Nat.mul_mod_right] using this
  have h2 : k * i' ≡ k * j' [MOD k'] := by
    have := h.of_mul_left k
    unfold Nat.ModEq at *
    simpa [Nat.add_mod, Nat.mul_mod_right] using this
  have h1' := Nat.ModEq.cancel_left_of_coprime hcop.gcd_eq_one h1
  have h2' := Nat.ModEq.cancel_left_of_coprime (by simpa [Nat.gcd_comm] using hcop.gcd_eq_one) h2
  have e1 : i.val = j.val := Nat.ModEq.eq_of_lt_of_lt h1' i.isLt j.isLt
  have e2 : i'.val = j'.val := Nat.ModEq.eq_of_lt_of_lt h2' i'.isLt j'.isLt
  exact Prod.ext (Fin.ext e1) (Fin.ext e2)

/-! ### Theorem 6.6 -/

open Complex in
/-- The summand $e^{2\pi i h t^2/N}$ of the Gauss sum, for a natural number $t$. -/
private noncomputable def gterm (h : ℤ) (N t : ℕ) : ℂ := cexp (2 * Real.pi * I * h * (t : ℂ) ^ 2 / N)

open Complex in
private lemma gterm_mod (h : ℤ) (N t : ℕ) (hN : 0 < N) : gterm h N (t % N) = gterm h N t := by
  unfold gterm
  symm
  have hdm : N * (t / N) + t % N = t := Nat.div_add_mod t N
  generalize t / N = q at hdm
  generalize t % N = r at hdm ⊢
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨h * (N * q ^ 2 + 2 * q * r : ℕ), ?_⟩
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have ht : (t : ℂ) = N * q + r := by exact_mod_cast hdm.symm
  rw [ht]
  push_cast
  field_simp
  ring

open Complex in
private lemma gterm_mul (h : ℤ) (k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (j j' : ℕ) :
    gterm h (k₁ * k₂) (k₁ * j' + k₂ * j) = gterm (h * k₂) k₁ j * gterm (h * k₁) k₂ j' := by
  unfold gterm
  rw [← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨2 * h * j * j', ?_⟩
  have h1 : (k₁ : ℂ) ≠ 0 := by exact_mod_cast hk₁.ne'
  have h2 : (k₂ : ℂ) ≠ 0 := by exact_mod_cast hk₂.ne'
  push_cast
  field_simp
  ring

open Complex in
private lemma gaussSum_range (h : ℤ) (k : ℕ) (hk : 0 < k) :
    gaussSumMW h k = ∑ i ∈ Finset.range k, gterm h k i := by
  have h0 : gterm h k 0 = 1 := by simp [gterm]
  have hk' : gterm h k k = 1 := by
    unfold gterm
    have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    have : 2 * (Real.pi : ℂ) * I * h * (k : ℂ) ^ 2 / k = ((h * k : ℤ) : ℂ) * (2 * Real.pi * I) := by
      push_cast; try field_simp
    rw [this]
    exact Complex.exp_int_mul_two_pi_mul_I _
  have hIcc : Finset.Icc 1 k = Finset.Ico 1 (k + 1) := by ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have e1 : gaussSumMW h k = ∑ j ∈ Finset.Ico 1 (k + 1), gterm h k j := by
    unfold gaussSumMW gterm; rw [hIcc]
  have e2 : ∑ i ∈ Finset.range (k + 1), gterm h k i = ∑ i ∈ Finset.range k, gterm h k i + gterm h k k :=
    Finset.sum_range_succ _ _
  have e3 : ∑ i ∈ Finset.range (k + 1), gterm h k i = gterm h k 0 + ∑ i ∈ Finset.Ico 1 (k + 1), gterm h k i := by
    rw [Finset.range_eq_Ico]; exact Finset.sum_eq_sum_Ico_succ_bot (by omega) _
  rw [h0] at e3
  rw [hk'] at e2
  rw [e1]
  linear_combination e2 - e3

/-- **Moreno–Wagstaff, Theorem 6.6** (p. 201), proved (without needing the coprimality of $h$): by Lemma 6.1 the
residues mod $k_1 k_2$ are $k_1 j' + k_2 j$, and $e^{2\pi i h (k_1 j' + k_2 j)^2/(k_1 k_2)}$ factors as
$e^{2\pi i h k_2 j^2/k_1}\, e^{2\pi i h k_1 j'^2/k_2}$ (the cross term is $2 h j j'$, an integer). -/
@[kb "morenowagstaff2005" "Theorem 6.6, p. 201"]
theorem theorem66 : Theorem66 := by
  intro k₁ k₂ h hk₁ hk₂ hcop _ _
  have hN : 0 < k₁ * k₂ := Nat.mul_pos hk₁ hk₂
  have : NeZero (k₁ * k₂) := ⟨hN.ne'⟩
  let e := Equiv.ofBijective _ (lemma61 k₁ k₂ hk₁ hk₂ hcop)
  let G : ZMod (k₁ * k₂) → ℂ := fun x => gterm h (k₁ * k₂) x.val
  have key1 : ∀ t : ℕ, G (t : ZMod (k₁ * k₂)) = gterm h (k₁ * k₂) t := by
    intro t
    simp only [G, ZMod.val_natCast, gterm_mod h _ t hN]
  have hS : gaussSumMW h (k₁ * k₂) = ∑ x : ZMod (k₁ * k₂), G x := by
    rw [gaussSum_range h _ hN]
    refine Finset.sum_bij (fun j _ => (j : ZMod (k₁ * k₂))) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro a ha b hb hab
      rw [Finset.mem_range] at ha hb
      rw [ZMod.natCast_eq_natCast_iff'] at hab
      rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hab
    · intro x _
      exact ⟨x.val, Finset.mem_range.2 (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
    · intro a _
      exact (key1 a).symm
  have hE : ∀ p : Fin k₁ × Fin k₂,
      G (e p) = gterm h (k₁ * k₂) (k₁ * p.2.val + k₂ * p.1.val) := fun p => key1 _
  have hA := Fin.sum_univ_eq_sum_range (fun j => gterm (h * k₂) k₁ j) k₁
  have hB := Fin.sum_univ_eq_sum_range (fun j => gterm (h * k₁) k₂ j) k₂
  have hT : ∑ x, G x = ∑ p : Fin k₁ × Fin k₂, G (e p) := (Equiv.sum_comp e G).symm
  rw [gaussSum_range _ _ hk₁, gaussSum_range _ _ hk₂, hS, hT, ← hA, ← hB, Fintype.sum_mul_sum,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  rw [hE (j, j'), gterm_mul h k₁ k₂ hk₁ hk₂]

/-! ### Theorem 6.7 -/

private lemma sq_mul_cases (x c : ℤ) :
    (∃ w, x ^ 2 * c = 4 * w) ∨ (∃ w, x ^ 2 * c = c + 4 * w) := by
  rcases Int.even_or_odd' x with ⟨k, rfl | rfl⟩
  · exact Or.inl ⟨k ^ 2 * c, by ring⟩
  · exact Or.inr ⟨(k ^ 2 + k) * c, by ring⟩

private lemma sq_mul_odd (x c : ℤ) (hx : Odd x) : ∃ w, x ^ 2 * c = c + 4 * w := by
  obtain ⟨k, rfl⟩ := hx
  exact ⟨(k ^ 2 + k) * c, by ring⟩

/-- If $f_1 a^2 = f_2 b^2$ with $\gcd(a, b) = 1$, $a > 0$, and both $f_i$ fundamental discriminants, then $a = 1$. -/
private lemma fund_a_eq_one (f₁ f₂ : ℤ) (a b : ℕ) (ha : 0 < a) (hcop : a.Coprime b)
    (hf₁ : Int.IsFundamentalDiscr f₁) (hf₂ : Int.IsFundamentalDiscr f₂)
    (h : f₁ * (a : ℤ) ^ 2 = f₂ * (b : ℤ) ^ 2) : a = 1 := by
  by_contra ha1
  have ha' : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  have hdvd : (a : ℤ) ^ 2 ∣ f₂ * (b : ℤ) ^ 2 := ⟨f₁, by rw [← h]; ring⟩
  have hc2 : IsCoprime ((a : ℤ) ^ 2) ((b : ℤ) ^ 2) := (Nat.isCoprime_iff_coprime.2 hcop).pow
  obtain ⟨c, hc⟩ := hc2.dvd_of_dvd_mul_right hdvd
  have hf1c : f₁ = c * (b : ℤ) ^ 2 := by
    have : f₁ * (a : ℤ) ^ 2 = (c * (b : ℤ) ^ 2) * (a : ℤ) ^ 2 := by rw [h, hc]; ring
    exact mul_right_cancel₀ (pow_ne_zero 2 ha') this
  have h1 := hf₁.1
  have h2 := hf₂.1
  have hcmod : c % 4 = 0 ∨ c % 4 = 1 := by
    rcases Nat.even_or_odd a with hae | hao
    · have hbo : Odd b := by
        rcases Nat.even_or_odd b with hbe | hbo
        · exfalso
          have h2' : 2 ∣ Nat.gcd a b := Nat.dvd_gcd (even_iff_two_dvd.1 hae) (even_iff_two_dvd.1 hbe)
          rw [Nat.Coprime.gcd_eq_one hcop] at h2'
          omega
        · exact hbo
      obtain ⟨w, hw⟩ := sq_mul_odd (b : ℤ) c hbo.natCast
      have : f₁ = c + 4 * w := by rw [hf1c, mul_comm, hw]
      omega
    · obtain ⟨w, hw⟩ := sq_mul_odd (a : ℤ) c hao.natCast
      have : f₂ = c + 4 * w := by rw [hc, hw]
      omega
  obtain ⟨p, hp, c', hc'⟩ := Nat.exists_prime_and_dvd ha1
  refine (Int.isFundamentalDiscr_iff_forall_prime.1 hf₂).2 p hp ⟨(c' : ℤ) ^ 2 * c, ?_, ?_⟩
  · rw [hc, hc']; push_cast; ring
  · rcases sq_mul_cases (c' : ℤ) c with ⟨w, hw⟩ | ⟨w, hw⟩
    · rw [hw]; omega
    · rw [hw]; omega

/-- **Moreno–Wagstaff, Theorem 6.7** (Landau; p. 230), proved. Existence: take the largest $m > 0$ with
$m^2 \mid d$ and $d/m^2 \equiv 0, 1 \pmod 4$; maximality is exactly Mathlib's prime-by-prime criterion for a
fundamental discriminant (`Int.isFundamentalDiscr_iff_forall_prime`). Uniqueness: from $f_1 m_1^2 = f_2 m_2^2$
cancel $g = \gcd(m_1, m_2)$; coprimality gives $f_2 = a^2 e$, and a prime $p \mid a$ would give
$p^2 \mid f_2$ with quotient $\equiv 0, 1 \pmod 4$, contradicting fundamentality; so $a = 1$ and likewise $b = 1$. -/
@[kb "morenowagstaff2005" "Theorem 6.7, p. 230"]
theorem theorem67 : Theorem67 := by
  classical
  intro d hd4 hsq
  have hd0 : d ≠ 0 := by rintro rfl; exact hsq ⟨0, by simp⟩
  -- the admissible multipliers
  let P : ℕ → Prop := fun m => 0 < m ∧ (m : ℤ) ^ 2 ∣ d ∧ (d / (m : ℤ) ^ 2 % 4 = 0 ∨ d / (m : ℤ) ^ 2 % 4 = 1)
  have hbound : ∀ m : ℕ, 0 < m → (m : ℤ) ^ 2 ∣ d → m ≤ d.natAbs := by
    intro m hm hdv
    have h1 : m ^ 2 ∣ d.natAbs := by
      have := Int.natAbs_dvd_natAbs.2 hdv
      simpa [Int.natAbs_pow] using this
    have h2 : m ^ 2 ≤ d.natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hd0) h1
    nlinarith
  have P1 : P 1 := ⟨one_pos, by simp, by simpa using hd4⟩
  have hb1 : 1 ≤ d.natAbs := Int.natAbs_pos.2 hd0
  set m₀ := Nat.findGreatest P d.natAbs with hm₀
  have hPm₀ : P m₀ := Nat.findGreatest_spec (P := P) hb1 P1
  obtain ⟨hm0, hdv, hf4⟩ := hPm₀
  have hmax : ∀ m : ℕ, P m → m ≤ m₀ := fun m hm =>
    Nat.le_findGreatest (hbound m hm.1 hm.2.1) hm
  obtain ⟨f, hf⟩ := hdv
  have hm0' : (m₀ : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hm0.ne')
  have hfd : d / (m₀ : ℤ) ^ 2 = f := by rw [hf]; exact Int.mul_ediv_cancel_left _ hm0'
  rw [hfd] at hf4
  have hfund : Int.IsFundamentalDiscr f := by
    rw [Int.isFundamentalDiscr_iff_forall_prime]
    refine ⟨hf4, fun p hp ⟨e, hfe, he4⟩ => ?_⟩
    have hdv' : ((m₀ * p : ℕ) : ℤ) ^ 2 ∣ d := ⟨e, by rw [hf, hfe]; push_cast; ring⟩
    have hmp : 0 < m₀ * p := Nat.mul_pos hm0 hp.pos
    have hPmp : P (m₀ * p) := by
      refine ⟨hmp, hdv', ?_⟩
      have : d / ((m₀ * p : ℕ) : ℤ) ^ 2 = e := by
        have hne : ((m₀ * p : ℕ) : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hmp.ne')
        have : d = ((m₀ * p : ℕ) : ℤ) ^ 2 * e := by rw [hf, hfe]; push_cast; ring
        rw [this]; exact Int.mul_ediv_cancel_left _ hne
      rw [this]; exact he4
    have := hmax _ hPmp
    have h2 := hp.two_le
    nlinarith
  have hfns : ¬ IsSquare f := by
    rintro ⟨r, hr⟩
    exact hsq ⟨r * m₀, by rw [hf, hr]; ring⟩
  refine ⟨(f, m₀), ⟨hm0, ⟨hfund, hfns⟩, by simpa [mul_comm] using hf⟩, ?_⟩
  rintro ⟨f', m'⟩ ⟨hm', ⟨hfund', _⟩, hdf'⟩
  simp only at hm' hdf'
  obtain ⟨a, b, hcop, ha, hb⟩ := Nat.exists_coprime m₀ m'
  set g := Nat.gcd m₀ m'
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hm0
  have hg' : (g : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hg.ne')
  have hapos : 0 < a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · simp at ha; omega
    · exact h
  have hbpos : 0 < b := by
    rcases Nat.eq_zero_or_pos b with rfl | h
    · simp at hb; omega
    · exact h
  have key : f * (a : ℤ) ^ 2 = f' * (b : ℤ) ^ 2 := by
    have h1 : d = f * (m₀ : ℤ) ^ 2 := by rw [hf]; ring
    have : (f * (a : ℤ) ^ 2) * (g : ℤ) ^ 2 = (f' * (b : ℤ) ^ 2) * (g : ℤ) ^ 2 := by
      have e1 : (m₀ : ℤ) = a * g := by exact_mod_cast ha
      have e2 : (m' : ℤ) = b * g := by exact_mod_cast hb
      calc (f * (a : ℤ) ^ 2) * (g : ℤ) ^ 2 = f * (m₀ : ℤ) ^ 2 := by rw [e1]; ring
        _ = d := h1.symm
        _ = f' * (m' : ℤ) ^ 2 := hdf'
        _ = (f' * (b : ℤ) ^ 2) * (g : ℤ) ^ 2 := by rw [e2]; ring
    exact mul_right_cancel₀ hg' this
  have ha1 : a = 1 := fund_a_eq_one f f' a b hapos hcop hfund hfund' key
  have hb1' : b = 1 := fund_a_eq_one f' f b a hbpos hcop.symm hfund' hfund key.symm
  subst ha1 hb1'
  have hmm : m₀ = m' := by omega
  subst hmm
  have : f = f' := by
    have h2 : f * (m₀ : ℤ) ^ 2 = f' * (m₀ : ℤ) ^ 2 := by rw [← hdf']; rw [hf]; ring
    exact mul_right_cancel₀ hm0' h2
  rw [this]

/-- **Moreno–Wagstaff, Theorem 7.7, corrected** (p. 314), proved: with $a = (z+x)/2$, $b = (z-x)/2$ one has
$a^2 + b^2 = y^2$, $\gcd(a, b) = 1$; Mathlib's classification of primitive Pythagorean triples gives
$\{a, b\} = \{r^2 - s^2, 2rs\}$, $y = r^2 + s^2$, and $x = a - b$, $z = a + b$. -/
@[kb "morenowagstaff2005" "Theorem 7.7 (with x < z), p. 314"]
theorem theorem77Corrected : Theorem77Corrected := by
  intro x y z hx hxz h hy hg
  have hz : 0 < z := by omega
  have hpar : Even (z + x) := by
    have h2 : Even (x ^ 2 + z ^ 2) := ⟨y ^ 2, by rw [h]; ring⟩
    simp only [Int.even_add, Int.even_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      and_true] at h2 ⊢
    tauto
  obtain ⟨a, ha⟩ := hpar
  obtain ⟨b, hb⟩ : ∃ b, b = z - a := ⟨_, rfl⟩
  have hzab : z = a + b := by omega
  have hxab : x = a - b := by omega
  have hab : a ^ 2 + b ^ 2 = y ^ 2 := by
    have : 2 * (a ^ 2 + b ^ 2) = 2 * y ^ 2 := by
      rw [← h, hzab, hxab]; ring
    linarith
  have hbpos : 0 < b := by omega
  have hapos : 0 < a := by omega
  have hcop : Int.gcd a b = 1 := by
    set d : ℤ := (Int.gcd a b : ℤ) with hd
    have hda : d ∣ a := Int.gcd_dvd_left a b
    have hdb : d ∣ b := Int.gcd_dvd_right a b
    have hdy : d ∣ y := by
      have : d ^ 2 ∣ y ^ 2 := by
        rw [← hab]; exact dvd_add (pow_dvd_pow_of_dvd hda 2) (pow_dvd_pow_of_dvd hdb 2)
      exact (Int.pow_dvd_pow_iff two_ne_zero).1 this
    have hdx : d ∣ x := by rw [hxab]; exact dvd_sub hda hdb
    have hdz : d ∣ z := by rw [hzab]; exact dvd_add hda hdb
    have h1 : Int.gcd a b ∣ Int.gcd x y := Int.dvd_gcd hdx hdy
    have h2 : Int.gcd a b ∣ Int.gcd (Int.gcd x y) z :=
      Int.dvd_gcd (Int.natCast_dvd_natCast.2 h1) hdz
    rw [hg] at h2
    exact Nat.dvd_one.1 h2
  have htrip : PythagoreanTriple a b y := by
    unfold PythagoreanTriple; nlinarith
  obtain ⟨m, n, hmn1, hmn2, hmn3, hmn4⟩ :=
    PythagoreanTriple.coprime_classification.mp ⟨htrip, hcop⟩
  have hmn : 0 < m * n := by
    rcases hmn1 with ⟨_, h2⟩ | ⟨h2, _⟩ <;> nlinarith
  have hrs : |m| * |n| = m * n := by rw [← abs_mul, abs_of_pos hmn]
  have hrs0 : 0 < |m| * |n| := by rw [hrs]; exact hmn
  have hr0 : 0 ≤ |m| := abs_nonneg _
  have hs0 : 0 ≤ |n| := abs_nonneg _
  have hs : 0 < |n| := by
    rcases hs0.eq_or_lt with h' | h'
    · rw [← h'] at hrs0; simp at hrs0
    · exact h'
  have hm2 : m ^ 2 = |m| ^ 2 := (sq_abs m).symm
  have hn2 : n ^ 2 = |n| ^ 2 := (sq_abs n).symm
  have hyr : y = |m| ^ 2 + |n| ^ 2 := by
    rcases hmn2 with h' | h'
    · rw [h', hm2, hn2]
    · exfalso; nlinarith [sq_nonneg m, sq_nonneg n]
  have hcase : (a = |m| ^ 2 - |n| ^ 2 ∧ b = 2 * (|m| * |n|)) ∨
      (a = 2 * (|m| * |n|) ∧ b = |m| ^ 2 - |n| ^ 2) := by
    rw [hrs, hm2.symm, hn2.symm]
    rcases hmn1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨h1, by linarith⟩
    · right; exact ⟨by linarith, h2⟩
  have hlt : |n| < |m| := by
    by_contra hh
    push Not at hh
    have hsq : |m| ^ 2 ≤ |n| ^ 2 := pow_le_pow_left₀ hr0 hh 2
    rcases hcase with ⟨h1, _⟩ | ⟨_, h1⟩ <;> linarith
  refine ⟨|m|, |n|, hs, hlt, ?_, ?_, ?_, hyr, ?_⟩
  · apply Int.isCoprime_iff_gcd_eq_one.2
    simpa [Int.gcd_eq_natAbs, Int.natAbs_abs] using hmn3
  · intro hmod
    unfold Int.ModEq at hmod
    rcases hmn4 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases abs_cases m with ⟨e1, _⟩ | ⟨e1, _⟩ <;> rcases abs_cases n with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
      omega
  · rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e : x = |m| ^ 2 - |n| ^ 2 - 2 * |m| * |n| := by rw [hxab, h1, h2]; ring
      rw [← e]; exact (abs_of_pos hx).symm
    · have e : x = -(|m| ^ 2 - |n| ^ 2 - 2 * |m| * |n|) := by rw [hxab, h1, h2]; ring
      rw [abs_of_neg (by linarith)]; exact e
  · rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (rw [hzab, h1, h2]; ring)

/-- **Moreno–Wagstaff, Theorem 7.7 as printed is false** (p. 314): $(x, y, z) = (1, 1, 1)$ is a primitive
solution of $x^2 + z^2 = 2y^2$, but $r^2 - s^2 + 2rs \ge r^2 + s^2 > 1$ for $r > s > 0$. The corrected
statement is `theorem77Corrected`. -/
@[kb "morenowagstaff2005" "Theorem 7.7 (as printed), counterexample, p. 314"]
theorem not_theorem77 : ¬ Theorem77 := by
  intro h
  obtain ⟨r, s, hs, hsr, -, -, -, -, hz⟩ := h 1 1 1 one_pos one_pos one_pos (by norm_num) (by norm_num)
  nlinarith

end QuadFormsKB.MorenoWagstaff
