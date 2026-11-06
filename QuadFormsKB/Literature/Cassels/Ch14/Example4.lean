/-
# Cassels, Chapter 14, Example 4: Nagell's lower bound for the class number

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, Examples, Ex. 4, p. 359 (Nagell 1922): *let $D < 0$ be a
discriminant and $q$ a prime with $(D/q) = +1$. Then the number $h(D)$ of classes of forms of discriminant $D$
satisfies $1 + h(D) \ge \log(\tfrac14(|D| - 1))/\log q$.* [Hint: a form $g$ of discriminant $D$ represents $q$; if
$g$ has order $M$ in the class group, then $q^M$ is represented by the principal form $f_0$ (1.11), so
$q^M \ge \tfrac14(|D| - 1)$.]

$h(D)$ is the order of Cassels' group $\mathcal G$ (`FormClass D`), which for $D < 0$ contains the classes of positive
and of negative definite forms. *Erratum:* Cassels writes "forms of determinant $D$"; $D$ is the discriminant
(as in Ex. 6). (The machine-read text has "$>$"; the page image, p. 359, has "$\ge$".)

*Proof (formalized).* Choose $B$ with $B^2 \equiv D \pmod{4q^{h+1}}$, $h = h(D)$ (Hensel, `exists_sqrt_mod`). The forms
$g_k = [q^k, B, q^{h+1-k}e]$ ($1 \le k \le h+1$) satisfy $[g_1]^k = [g_k]$ (as in Lemma 2.5). If $M \le h$ is the
order of $[g_1]$, then $g_M \sim f_0$, so $f_0$ represents $q^M$ primitively, whence $4q^M \ge |D|$.
-/
import QuadFormsKB.Literature.Cassels.Ch14.Group
import QuadFormsKB.Siegel.ThetaCharacter

namespace QuadFormsKB.Composition

open BinQF Binary

/-! ### Number-theoretic helpers (Hensel lifting of square roots) -/

private theorem sq_mod_four_cases (B : ℤ) :
    (B % 2 = 0 ∧ B ^ 2 % 4 = 0) ∨ (B % 2 = 1 ∧ B ^ 2 % 4 = 1) := by
  have h : B % 4 = 0 ∨ B % 4 = 1 ∨ B % 4 = 2 ∨ B % 4 = 3 := by omega
  rcases h with h | h | h | h <;> [left; right; left; right] <;>
    refine ⟨by omega, ?_⟩ <;> simp [pow_two, Int.mul_emod, h]

private theorem four_dvd_sq_sub {B D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) (hBD : B % 2 = D % 2) :
    4 ∣ B ^ 2 - D := by
  have := sq_mod_four_cases B
  generalize B ^ 2 = S at this
  omega

/-- Hensel lifting for an odd prime $q$ (elementary). -/
theorem exists_sqrt_mod_odd {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {D : ℤ} (hDq : ¬ (q : ℤ) ∣ D)
    (hD4 : D % 4 = 0 ∨ D % 4 = 1) (hsq : ∃ x : ℤ, (q : ℤ) ∣ x ^ 2 - D) :
    ∀ k : ℕ, ∃ B : ℤ, 4 * (q : ℤ) ^ (k + 1) ∣ B ^ 2 - D := by
  have hqp : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  have hq2' : ¬ (q : ℤ) ∣ 2 := by
    intro h
    have : q ∣ 2 := by exact_mod_cast h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 this)
  have hqodd : q % 2 = 1 := by
    rcases hq.eq_two_or_odd with h | h
    · exact absurd h hq2
    · exact h
  intro k
  induction k with
  | zero =>
    obtain ⟨x, hx⟩ := hsq
    have key : ∃ B : ℤ, (q : ℤ) ∣ B ^ 2 - D ∧ B % 2 = D % 2 := by
      by_cases h : x % 2 = D % 2
      · exact ⟨x, hx, h⟩
      · refine ⟨x + q, ?_, by omega⟩
        have : (x + q) ^ 2 - D = (x ^ 2 - D) + q * (2 * x + q) := by ring
        rw [this]
        exact dvd_add hx (dvd_mul_right _ _)
    obtain ⟨B, hB1, hB2⟩ := key
    refine ⟨B, ?_⟩
    have h4 := four_dvd_sq_sub hD4 hB2
    have hcop : IsCoprime (4 : ℤ) (q : ℤ) := by
      have : IsCoprime (q : ℤ) 4 := by
        have : IsCoprime (q : ℤ) 2 := (Prime.coprime_iff_not_dvd hqp).2 hq2'
        simpa using this.pow_right (n := 2)
      exact this.symm
    simpa using hcop.mul_dvd h4 hB1
  | succ k ih =>
    obtain ⟨B, u, hu⟩ := ih
    have hqB : ¬ (q : ℤ) ∣ B := by
      intro h
      apply hDq
      have h1 : (q : ℤ) ∣ B ^ 2 - D := by
        rw [hu]; exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _) _
      have h2 : (q : ℤ) ∣ B ^ 2 := dvd_pow h (by norm_num)
      have := dvd_sub h2 h1
      simpa using this
    have hq2B : ¬ (q : ℤ) ∣ 2 * B := by
      intro h
      rcases hqp.dvd_or_dvd h with h | h
      · exact hq2' h
      · exact hqB h
    obtain ⟨a, s, hs⟩ := (Prime.coprime_iff_not_dvd hqp).2 hq2B
    refine ⟨B + 4 * (q : ℤ) ^ (k + 1) * (-(u * s)), u * a + 4 * (-(u * s)) ^ 2 * (q : ℤ) ^ k, ?_⟩
    linear_combination hu - (4 * (q : ℤ) ^ (k + 1) * u) * hs

/-- Lifting square roots modulo powers of $2$: for $D \equiv 1 \pmod 8$ there are odd $B$ with
$B^2 \equiv D \pmod{2^{k+3}}$. -/
theorem exists_sqrt_mod_two {D : ℤ} (hD : D % 8 = 1) :
    ∀ k : ℕ, ∃ B : ℤ, B % 2 = 1 ∧ (2 : ℤ) ^ (k + 3) ∣ B ^ 2 - D := by
  intro k
  induction k with
  | zero => exact ⟨1, by norm_num, ⟨(1 - D) / 8, by omega⟩⟩
  | succ k ih =>
    obtain ⟨B, hB, u, hu⟩ := ih
    rcases Int.even_or_odd' u with ⟨v, hv | hv⟩
    · exact ⟨B, hB, v, by rw [pow_succ]; linear_combination hu + (2 : ℤ) ^ (k + 3) * hv⟩
    · obtain ⟨w, hw⟩ : ∃ w, B = 2 * w + 1 := ⟨B / 2, by omega⟩
      refine ⟨B + 2 ^ (k + 2), ?_, v + w + 1 + 2 ^ k, ?_⟩
      · have : (2 : ℤ) ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
        omega
      · subst hw
        rw [hv] at hu
        linear_combination hu

/-- **Square roots of $D$ modulo $4 q^{k+1}$.** -/
theorem exists_sqrt_mod {q : ℕ} (hq : q.Prime) {D : ℤ} (hDq : ¬ (q : ℤ) ∣ D)
    (hD4 : D % 4 = 0 ∨ D % 4 = 1) (hq2 : q = 2 → D % 8 = 1)
    (hsq : q ≠ 2 → ∃ x : ℤ, (q : ℤ) ∣ x ^ 2 - D) (k : ℕ) :
    ∃ B : ℤ, 4 * (q : ℤ) ^ (k + 1) ∣ B ^ 2 - D := by
  by_cases h2 : q = 2
  · subst h2
    obtain ⟨B, -, hB⟩ := exists_sqrt_mod_two (hq2 rfl) k
    refine ⟨B, ?_⟩
    have : 4 * ((2 : ℕ) : ℤ) ^ (k + 1) = 2 ^ (k + 3) := by push_cast; ring
    rw [this]; exact hB
  · exact exists_sqrt_mod_odd hq h2 hDq hD4 (hsq h2) k

/-- A primitive value $V > 1$ of $x^2 + \beta xy + \gamma y^2$ (discriminant $D < 0$) satisfies $|D| \le 4V$. -/
theorem principal_lower {D β γ x y V : ℤ} (hD : D < 0) (hdisc : β ^ 2 - 4 * γ = D) (hxy : IsCoprime x y)
    (hv : x ^ 2 + β * x * y + γ * y ^ 2 = V) (hV : 1 < V) : -D ≤ 4 * V := by
  by_cases hy : y = 0
  · subst hy
    have hu : IsUnit x := isCoprime_zero_right.1 hxy
    have : x ^ 2 = 1 := by
      rcases Int.isUnit_iff.1 hu with h | h <;> simp [h]
    simp at hv
    omega
  · have hy1 : 1 ≤ y ^ 2 := by
      have : 0 < y ^ 2 := by positivity
      omega
    have h4 : 4 * V = (2 * x + β * y) ^ 2 - D * y ^ 2 := by
      rw [← hv, ← hdisc]; ring
    nlinarith [sq_nonneg (2 * x + β * y)]

/-- The final real-analysis step. -/
theorem log_le (x : ℝ) (hx0 : 0 ≤ x) (q : ℕ) (hq : 2 ≤ q) (M : ℕ) (hx : x ≤ (q : ℝ) ^ M) (n : ℝ)
    (hMn : (M : ℝ) ≤ 1 + n) : Real.log x / Real.log q ≤ 1 + n := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hlq : 0 < Real.log q := Real.log_pos hq1
  rw [div_le_iff₀ hlq]
  have hn : 0 ≤ 1 + n := le_trans (Nat.cast_nonneg M) hMn
  rcases hx0.eq_or_lt with h0 | h0
  · rw [← h0]; simp; positivity
  · calc Real.log x ≤ Real.log ((q : ℝ) ^ M) := Real.log_le_log h0 hx
      _ = M * Real.log q := by rw [Real.log_pow]
      _ ≤ (1 + n) * Real.log q := mul_le_mul_of_nonneg_right hMn hlq.le

/-! ### The theorem -/

/-- Consequences of $\left(\frac{D}{q}\right)_{\mathrm{Kronecker}} = 1$ used by the Hensel lifting: $q \nmid D$,
$D \equiv 1 \pmod 8$ if $q = 2$, and $D$ is a square mod $q$ if $q$ is odd. -/
theorem kronecker_facts {D : ℤ} (hD4 : D % 4 = 0 ∨ D % 4 = 1) {q : ℕ} (hq : q.Prime) (h : Siegel.kroneckerSym D q = 1) :
    ¬ (q : ℤ) ∣ D ∧ (q = 2 → D % 8 = 1) ∧ (q ≠ 2 → ∃ x : ℤ, (q : ℤ) ∣ x ^ 2 - D) := by
  by_cases h2 : q = 2
  · subst h2
    have hf : (2 : ℕ).factorization 2 = 1 := by simp [Nat.Prime.factorization_self Nat.prime_two]
    rw [Siegel.kroneckerSym, hf] at h
    rw [show 2 / 2 ^ 1 = 1 by norm_num, jacobiSym.one_right, mul_one, pow_one] at h
    by_cases he : Even D
    · simp [he] at h
    · simp only [he, ite_false] at h
      rw [ZMod.χ₈_int_eq_if_mod_eight] at h
      have hodd : D % 2 = 1 := by
        rcases Int.even_or_odd D with h' | h'
        · exact absurd h' he
        · exact Int.odd_iff.1 h'
      have h8 : D % 8 = 1 := by
        split_ifs at h with h1 h3 <;> simp at h
        omega
      refine ⟨?_, fun _ => h8, fun h => absurd rfl h⟩
      intro hd; omega
  · have hodd : Odd q := hq.odd_of_ne_two h2
    rw [Siegel.kroneckerSym_of_odd D hodd] at h
    have : Fact q.Prime := ⟨hq⟩
    rw [← jacobiSym.legendreSym.to_jacobiSym] at h
    have h0 : (D : ZMod q) ≠ 0 := by
      intro h0
      have := (legendreSym.eq_zero_iff q D).2 h0
      omega
    refine ⟨?_, fun h => absurd h h2, fun _ => ?_⟩
    · intro hd
      exact h0 ((ZMod.intCast_zmod_eq_zero_iff_dvd D q).2 hd)
    · obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff q h0).1 h
      refine ⟨(r.val : ℤ), ?_⟩
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val, hr]
      ring

namespace FormClass

variable {D : ℤ}

/-- The form $[w^{j+1}, b, w^t e]$, primitive of discriminant $D$ when $\gcd(w, b) = 1$ and
$b^2 - 4w^{m+1}e = D$, $j + t = m$ (a copy of the helper of Lemma 2.5, which is private there). -/
private def ex4Form {w b e : ℤ} {m : ℕ} (hcop : IsCoprime w b) (hD : b ^ 2 - 4 * w ^ (m + 1) * e = D)
    (j t : ℕ) (h : j + t = m) : PrimForm D :=
  ⟨BinQF.mk (w ^ (j + 1)) b (w ^ t * e),
    by
      intro d h1 h2 _
      simp only [a_mk, b_mk] at h1 h2
      exact (hcop.pow_left).isUnit_of_dvd' h1 h2,
    by
      simp only [BinQF.disc, a_mk, b_mk, c_mk]
      subst h
      linear_combination hD⟩

private theorem ex4Form_val {w b e : ℤ} {m : ℕ} (hcop : IsCoprime w b)
    (hD : b ^ 2 - 4 * w ^ (m + 1) * e = D) (j t : ℕ) (h : j + t = m) :
    (ex4Form hcop hD j t h).1 = BinQF.mk (w ^ (j + 1)) b (w ^ t * e) := rfl

variable [NonzeroDisc D]

/-- $\mathfrak C^{j+1}$ for $\mathfrak C = [w, b, w^m e]$ is $[w^{j+1}, b, w^{m-j} e]$. -/
private theorem ex4Form_pow {w b e : ℤ} {m : ℕ} (hw : w ≠ 0) (hcop : IsCoprime w b)
    (hD : b ^ 2 - 4 * w ^ (m + 1) * e = D) :
    ∀ (j t : ℕ) (h : j + t = m),
      (mk (ex4Form hcop hD 0 m (zero_add m))) ^ (j + 1) = mk (ex4Form hcop hD j t h) := by
  intro j
  induction j with
  | zero =>
    intro t h
    have ht : t = m := by omega
    subst ht
    rw [zero_add, pow_one]
  | succ j ih =>
    intro t h
    have h' : j + (t + 1) = m := by omega
    have ih' := ih (t + 1) h'
    have hD' : b ^ 2 - 4 * w ^ (j + (t + 1) + 1) * e = D := by rw [h']; exact hD
    have hc : Concordant (ex4Form hcop hD j (t + 1) h').1 (ex4Form hcop hD 0 m (zero_add m)).1 := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [ex4Form_val, a_mk]
        exact mul_ne_zero (pow_ne_zero _ hw) (pow_ne_zero _ hw)
      · simp only [ex4Form_val, b_mk]
      · exact (ex4Form hcop hD j (t + 1) h').2.2.trans (ex4Form hcop hD 0 m (zero_add m)).2.2.symm
      · rw [(ex4Form hcop hD j (t + 1) h').2.2]
        simp only [ex4Form_val, a_mk, b_mk]
        exact ⟨w ^ t * e, by linear_combination hD'⟩
    have hcomp : (PrimForm.comp (ex4Form hcop hD j (t + 1) h') (ex4Form hcop hD 0 m (zero_add m)) hc).1 =
        (ex4Form hcop hD (j + 1) t h).1 := by
      apply eq_of_a_b_disc
      · simp only [primComp_a, ex4Form_val, a_mk]
        exact mul_ne_zero (pow_ne_zero _ hw) (pow_ne_zero _ hw)
      · simp only [primComp_a, ex4Form_val, a_mk]
        ring
      · simp only [primComp_b, ex4Form_val, b_mk]
      · exact (PrimForm.comp _ _ hc).2.2.trans (ex4Form hcop hD (j + 1) t h).2.2.symm
    rw [pow_succ, ih']
    exact (mk_mul_mk _ _ hc).trans (mk_eq_mk.2 (by rw [hcomp]; exact SLEquiv.refl _))

/-- **Key step of Ex. 4.** If $B^2 - 4q^{n+1}e = D$ with $\gcd(q, B) = 1$, $q \ge 2$, $n = h(D)$, then the principal
form primitively represents $q^M$ for some $1 \le M \le n$. -/
theorem exists_principal_rep {q : ℤ} (hq : 2 ≤ q) {B e : ℤ} (hcop : IsCoprime q B)
    (hD : B ^ 2 - 4 * q ^ (Nat.card (FormClass D) + 1) * e = D) :
    ∃ M : ℕ, 1 ≤ M ∧ M ≤ Nat.card (FormClass D) ∧ ∃ x y : ℤ, IsCoprime x y ∧
      (principalForm D).eval x y = q ^ M := by
  set n := Nat.card (FormClass D) with hn
  have hq0 : q ≠ 0 := by omega
  set x : FormClass D := mk (ex4Form hcop hD 0 n (zero_add n)) with hx
  set M := orderOf x with hM
  have hMpos : 0 < M := orderOf_pos x
  have hMle : M ≤ n := Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard x)
  have hxM : x ^ M = 1 := pow_orderOf_eq_one x
  have h1 : (M - 1) + (n - (M - 1)) = n := by omega
  have hpow := ex4Form_pow hq0 hcop hD (M - 1) (n - (M - 1)) h1
  have hM1 : M - 1 + 1 = M := by omega
  rw [hM1, hxM] at hpow
  have heq : mk (principal D) = mk (ex4Form hcop hD (M - 1) (n - (M - 1)) h1) := hpow
  have hs := mk_eq_mk.1 heq
  obtain ⟨p, q', r, s, hd, hsub⟩ := (sLEquiv_iff _ _).1 hs
  refine ⟨M, hMpos, hMle, p, r, ⟨s, -q', by linear_combination hd⟩, ?_⟩
  have h2 := congrArg (fun f : BinQF => f.eval 1 0) hsub
  simp only [eval_subst] at h2
  rw [show p * 1 + q' * 0 = p by ring, show r * 1 + s * 0 = r by ring] at h2
  have h3 : (principal D).1 = principalForm D := rfl
  rw [h3] at h2
  rw [h2, eval_eq, ex4Form_val]
  simp only [a_mk, b_mk, c_mk]
  rw [hM1]
  ring

end FormClass

/-- **Cassels, Ch. 14, Ex. 4** (p. 359, Nagell): *for a discriminant $D < 0$ and a prime $q$ with $(D/q) = +1$,
$1 + h(D) \ge \log(\tfrac14(|D| - 1))/\log q$*, with $h(D) = |\mathcal G|$. -/
@[kb "cassels1978" "Ch. 14, Ex. 4, p. 359 (Nagell's bound 1 + h(D) ≥ log(¼(|D|−1))/log q)"]
theorem ex4 {D : ℤ} (hD : D < 0) [NonzeroDisc D] {q : ℕ} (hq : q.Prime)
    (hDq : Siegel.kroneckerSym D q = 1) :
    Real.log ((|(D : ℝ)| - 1) / 4) / Real.log q ≤ 1 + (Nat.card (FormClass D) : ℝ) := by
  have hD4 : D % 4 = 0 ∨ D % 4 = 1 := NonzeroDisc.mod_four
  obtain ⟨hqD, hq2, hsq⟩ := kronecker_facts hD4 hq hDq
  obtain ⟨B, e, he⟩ := exists_sqrt_mod hq hqD hD4 hq2 hsq (Nat.card (FormClass D))
  have hqp : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  have hqB : ¬ (q : ℤ) ∣ B := by
    intro h
    apply hqD
    have hDe : D = B ^ 2 - 4 * (q : ℤ) ^ (Nat.card (FormClass D) + 1) * e := by linarith
    rw [hDe]
    exact dvd_sub (dvd_pow h two_ne_zero)
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self _ (by omega)) 4) e)
  have hq2' : (2 : ℤ) ≤ q := by exact_mod_cast hq.two_le
  obtain ⟨M, hM1, hMn, x, y, hxy, hev⟩ := FormClass.exists_principal_rep hq2'
    ((Prime.coprime_iff_not_dvd hqp).2 hqB) (by linarith : B ^ 2 - 4 * (q : ℤ) ^ (Nat.card (FormClass D) + 1) * e = D)
  have hspec := (FormClass.principalForm_spec (NonzeroDisc.mod_four : D % 4 = 0 ∨ D % 4 = 1)).2
  have hlow : -D ≤ 4 * (q : ℤ) ^ M := by
    refine principal_lower (β := D % 2) (γ := (D % 2 - D) / 4) hD ?_ hxy ?_ ?_
    · simpa [BinQF.disc, FormClass.principalForm] using hspec
    · have := eval_eq (FormClass.principalForm D) x y
      rw [hev] at this
      simp only [FormClass.principalForm, a_mk, b_mk, c_mk] at this
      linarith
    · exact one_lt_pow₀ (by omega) (by omega)
  have hreal : (|(D : ℝ)| - 1) / 4 ≤ (q : ℝ) ^ M := by
    rw [abs_of_neg (by exact_mod_cast hD)]
    have : (-D : ℝ) ≤ 4 * (q : ℝ) ^ M := by exact_mod_cast hlow
    linarith
  have hnn : 0 ≤ (|(D : ℝ)| - 1) / 4 := by
    rw [abs_of_neg (by exact_mod_cast hD)]
    have : (D : ℝ) ≤ -1 := by exact_mod_cast (by omega : D ≤ -1)
    linarith
  exact log_le _ hnn q hq.two_le M hreal _ (by
    have : (M : ℝ) ≤ (Nat.card (FormClass D) : ℝ) := by exact_mod_cast hMn
    linarith)

end QuadFormsKB.Composition
