/-
# Siegel's formula: Hanke 2004 §6 "Main results", conditionally

Hanke's §6 (pp. 380–383) decides representability by comparing a lower bound for the main term $a_E(m)$ (§5) with an
upper bound for the cusp-form coefficient $|c(m)|$ ((4.8)–(4.10)): since $r_Q(m) = a_E(m) + a_H(m) + c(m)$, the
inequality $a_E(m) + a_H(m) > |c(m)|$ forces $r_Q(m) > 0$ (`represents_of_abs_lt`). This file proves the §6
statements **conditionally**, from

- the inputs of `Siegel/Inputs.lean` (`ThetaSplit`, `CuspBound`, `CuspBoundSqClass`, `CuspBoundUniform`),
- Siegel's formula (`SiegelFormula`, `SiegelFormula3` relative to the natural-order value of the Euler product),
- the ratio forms of Thm 5.7 (`thm_5_7_a_genus`, `thm_5_7_b_genus`, `thm_5_7_c_even_genus`, `thm_5_7_c_odd_genus`),
- and, where the paper uses it, an **explicit hypothesis for the global lower bound of $a_E(T')$** (the $L$-function
  and $\zeta$ factors of $\hat\Lambda_n$, Thm 5.7, pp. 372–373, which are not formalized).

| Hanke 2004 | Lean | Status |
|---|---|---|
| Thm 6.1, p. 380, first case ($n = 3$, $a_H(m) \ge 0$ or Thm 5.9(a)(ii)) | `thm_6_1` | conditional; threshold $M_3$ corrected (erratum candidate) |
| Thm 6.1, second case ($\tilde T$ exceptional, $a_H(m) < 0$) | — | not formalized (needs Thm 5.6, 5.9(b)(ii)) |
| Thm 6.2, p. 381 ($n = 3$, not in a spinor square class, uniform in $t$) | `thm_6_2` | conditional |
| Thm 6.3, p. 381 ($n = 4$) | `thm_6_3` | conditional |
| Thm 6.4, p. 382 ($n \ge 5$ even / odd) | `thm_6_4_even`, `thm_6_4_odd` | conditional |
| Thm 6.4 ($n \ge 6$ even), non-explicit constant | `thm_6_4_even_uncond` (`Siegel/Tartakowsky.lean`); Hecke in place of Deligne: `thm_6_4_even_hecke` | **unconditional** / conditional on Siegel's formula |
| Lemma 6.5, p. 383 ($F_4$) | `F4`, `F4_mul`, `lemma_6_5` | **unconditional** |
| Remark 6.5.1 | `thm_6_3_F4` | conditional |

Strict inequalities: the paper's thresholds in Thms 6.2 and 6.4 are printed with "$\ge$"; the argument ("solving to
ensure $a_E(m) > |a(m)|$") needs "$>$", which is what is proved (erratum candidate).
-/
import QuadFormsKB.Siegel.Inputs

namespace QuadFormsKB.Siegel

open LocalDensity

variable {n : ℕ}

/-! ### Lemma 6.5: the function $F_4$ -/

open Classical in
/-- **The function $F_4$ of Lemma 6.5** (Hanke 2004, p. 383): for $N \in \mathbb{N}$ and a character $\chi$,
$$F_4(m) = \frac{\sqrt m}{\tau(m)}\prod_{\substack{p \mid m,\ p \nmid N\\ \chi(p) = -1}}\frac{p-1}{p+1},$$
the product over the primes $p$ dividing $m$. Here $\chi$ is any function $\mathbb{N} \to \mathbb{Z}$ (only the condition
$\chi(p) = -1$ is used; the paper takes a quadratic Dirichlet character). *Edge case:* $F_4(0) = 0$. By Remark 6.5.1, for
$m = (m)_{\mathrm{Iso}}$, $N$ the level and $\chi(p) = \left(\frac{\det H}{p}\right)$ it is the left side of Thm 6.3. -/
@[kb "hanke2004" "Lemma 6.5, p. 383"]
noncomputable def F4 (N : ℕ) (χ : ℕ → ℤ) (m : ℕ) : ℝ :=
  √(m : ℝ) / divCount m *
    ∏ p ∈ m.primeFactors.filter (fun p => ¬ p ∣ N ∧ χ p = -1), ((p : ℝ) - 1) / ((p : ℝ) + 1)

theorem F4_one (N : ℕ) (χ : ℕ → ℤ) : F4 N χ 1 = 1 := by
  simp [F4, divCount]

theorem F4_nonneg (N : ℕ) (χ : ℕ → ℤ) (m : ℕ) : 0 ≤ F4 N χ m := by
  unfold F4
  refine mul_nonneg (by positivity) (Finset.prod_nonneg fun p hp => ?_)
  have : (1 : ℝ) ≤ p := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).one_lt.le
  exact div_nonneg (by linarith) (by linarith)

/-- **Lemma 6.5, first part** (Hanke 2004, p. 383): $F_4$ is multiplicative, $F_4(ab) = F_4(a)F_4(b)$ for coprime $a, b$. -/
@[kb "hanke2004" "Lemma 6.5, p. 383 (multiplicativity)"]
theorem F4_mul (N : ℕ) (χ : ℕ → ℤ) {a b : ℕ} (h : Nat.Coprime a b) :
    F4 N χ (a * b) = F4 N χ a * F4 N χ b := by
  classical
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · obtain rfl : b = 1 := Nat.coprime_zero_left _ |>.1 h
    simp [F4_one]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · obtain rfl : a = 1 := Nat.coprime_zero_right _ |>.1 h
    simp [F4_one]
  unfold F4
  rw [Nat.primeFactors_mul ha.ne' hb.ne', Finset.filter_union,
    Finset.prod_union (Finset.disjoint_filter_filter h.disjoint_primeFactors), divCount_mul h]
  push_cast
  rw [Real.sqrt_mul (by positivity)]
  ring

open Classical in
/-- $F_4(p^j) = \frac{\sqrt{p^j}}{j+1}\cdot\big(\frac{p-1}{p+1}$ if $j \ge 1$, $p \nmid N$, $\chi(p) = -1$; else $1\big)$. -/
theorem F4_prime_pow (N : ℕ) (χ : ℕ → ℤ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    F4 N χ (p ^ j) = √((p : ℝ) ^ j) / (j + 1) *
      (if 0 < j ∧ ¬ p ∣ N ∧ χ p = -1 then ((p : ℝ) - 1) / ((p : ℝ) + 1) else 1) := by
  unfold F4
  rw [divCount_prime_pow hp]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · rw [Nat.primeFactors_prime_pow hj.ne' hp, Finset.filter_singleton]
    push_cast
    by_cases hc : ¬ p ∣ N ∧ χ p = -1
    · simp [hc, hj]
    · simp [hc]

/-- The numerical core of Lemma 6.5: $(\nu+1)^2(p+1)^2 \le p^\nu(p-1)^2$ in the four cases of the lemma. -/
theorem lemma_6_5_aux {p ν : ℕ}
    (h : (11 ≤ p ∧ 1 ≤ ν) ∨ ((p = 5 ∨ p = 7) ∧ 2 ≤ ν) ∨ (p = 3 ∧ 5 ≤ ν) ∨ (p = 2 ∧ 11 ≤ ν)) :
    ((ν : ℝ) + 1) ^ 2 * ((p : ℝ) + 1) ^ 2 ≤ (p : ℝ) ^ ν * ((p : ℝ) - 1) ^ 2 := by
  -- induction in `ν` from a base case, with step factor `(ν+2)^2 ≤ p (ν+1)^2`
  have ind : ∀ ν₀ : ℕ, ((ν₀ : ℝ) + 1) ^ 2 * ((p : ℝ) + 1) ^ 2 ≤ (p : ℝ) ^ ν₀ * ((p : ℝ) - 1) ^ 2 →
      (∀ k : ℕ, ν₀ ≤ k → ((k : ℝ) + 2) ^ 2 ≤ (p : ℝ) * ((k : ℝ) + 1) ^ 2) →
      ∀ k : ℕ, ν₀ ≤ k → ((k : ℝ) + 1) ^ 2 * ((p : ℝ) + 1) ^ 2 ≤ (p : ℝ) ^ k * ((p : ℝ) - 1) ^ 2 := by
    intro ν₀ hbase hstep k hk
    induction k, hk using Nat.le_induction with
    | base => exact hbase
    | succ k hk ih =>
      have h1 := hstep k hk
      have hp0 : (0 : ℝ) ≤ p := by positivity
      push_cast
      calc ((k : ℝ) + 1 + 1) ^ 2 * ((p : ℝ) + 1) ^ 2
          = ((k : ℝ) + 2) ^ 2 * ((p : ℝ) + 1) ^ 2 := by ring
        _ ≤ (p : ℝ) * ((k : ℝ) + 1) ^ 2 * ((p : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (p : ℝ) * (((k : ℝ) + 1) ^ 2 * ((p : ℝ) + 1) ^ 2) := by ring
        _ ≤ (p : ℝ) * ((p : ℝ) ^ k * ((p : ℝ) - 1) ^ 2) := mul_le_mul_of_nonneg_left ih hp0
        _ = (p : ℝ) ^ (k + 1) * ((p : ℝ) - 1) ^ 2 := by ring
  rcases h with ⟨hp, hν⟩ | ⟨hp, hν⟩ | ⟨hp, hν⟩ | ⟨hp, hν⟩
  · have hp' : (11 : ℝ) ≤ p := by exact_mod_cast hp
    refine ind 1 ?_ ?_ ν hν
    · push_cast; nlinarith [hp']
    · intro k _
      have : (0 : ℝ) ≤ k := by positivity
      nlinarith
  · have hp' : (5 : ℝ) ≤ p := by rcases hp with rfl | rfl <;> norm_num
    refine ind 2 ?_ ?_ ν hν
    · rcases hp with rfl | rfl <;> norm_num
    · intro k hk
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
  · subst hp
    refine ind 5 (by norm_num) ?_ ν hν
    intro k hk
    have : (5 : ℝ) ≤ k := by exact_mod_cast hk
    push_cast; nlinarith
  · subst hp
    refine ind 11 (by norm_num) ?_ ν hν
    intro k hk
    have : (11 : ℝ) ≤ k := by exact_mod_cast hk
    push_cast; nlinarith

/-- **Lemma 6.5, second part** (Hanke 2004, p. 383): for every $m \in \mathbb{N}$ and prime $p$,
$$F_4(mp^\nu) \ge F_4(m)$$
when $p \ge 11$ and $\nu \ge 1$, or $p \in \{5, 7\}$ and $\nu \ge 2$, or $p = 3$ and $\nu \ge 5$, or $p = 2$ and $\nu \ge 11$.
(Proof as in the paper: with $m = p^{\nu_1}m_1$, $p \nmid m_1$, the ratio is at least
$p^{\nu/2}\frac{p-1}{p+1}\cdot\frac{1+\nu_1}{1+\nu_1+\nu}$, which is $\ge 1$ in these cases; checked here as
$(\nu+1)^2(p+1)^2 \le p^\nu(p-1)^2$.) Holds for every $N$ and every $\chi$. -/
@[kb "hanke2004" "Lemma 6.5, p. 383"]
theorem lemma_6_5 (N : ℕ) (χ : ℕ → ℤ) (m : ℕ) {p ν : ℕ} (hp : p.Prime)
    (h : (11 ≤ p ∧ 1 ≤ ν) ∨ ((p = 5 ∨ p = 7) ∧ 2 ≤ ν) ∨ (p = 3 ∧ 5 ≤ ν) ∨ (p = 2 ∧ 11 ≤ ν)) :
    F4 N χ m ≤ F4 N χ (m * p ^ ν) := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  obtain ⟨k, m₁, hdvd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p hp.ne_one
  have hcop : ∀ j, Nat.Coprime (p ^ j) m₁ := fun j =>
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hdvd)
  rw [show p ^ k * m₁ * p ^ ν = p ^ (k + ν) * m₁ by ring, F4_mul N χ (hcop _), F4_mul N χ (hcop _)]
  refine mul_le_mul_of_nonneg_right ?_ (F4_nonneg N χ m₁)
  -- the key estimate `ν + 1 ≤ √(p^ν) (p-1)/(p+1)`
  have hp1 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hsq : ((ν : ℝ) + 1) * ((p : ℝ) + 1) ≤ √((p : ℝ) ^ ν) * ((p : ℝ) - 1) := by
    have h2 := lemma_6_5_aux h
    rw [← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ (p : ℝ) - 1), ← Real.sqrt_mul (by positivity)]
    exact Real.le_sqrt_of_sq_le (by nlinarith)
  have hg0 : (0 : ℝ) ≤ ((p : ℝ) - 1) / ((p : ℝ) + 1) := div_nonneg (by linarith) (by linarith)
  have hg1 : ((p : ℝ) - 1) / ((p : ℝ) + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hsν : ((ν : ℝ) + 1) ≤ √((p : ℝ) ^ ν) := by
    have : √((p : ℝ) ^ ν) * ((p : ℝ) - 1) ≤ √((p : ℝ) ^ ν) * ((p : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
    nlinarith
  rw [F4_prime_pow N χ hp, F4_prime_pow N χ hp]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `ν₁ = 0`: `F4(1) = 1 ≤ √(p^ν)/(ν+1) · (factor ≥ (p-1)/(p+1))`
    simp only [pow_zero, Real.sqrt_one, CharP.cast_eq_zero, zero_add, div_one, lt_self_iff_false,
      false_and, ite_false, mul_one]
    have hν1 : 0 < ν := by omega
    have hfac : ((p : ℝ) - 1) / ((p : ℝ) + 1) ≤
        (if 0 < ν ∧ ¬ p ∣ N ∧ χ p = -1 then ((p : ℝ) - 1) / ((p : ℝ) + 1) else 1) := by
      split_ifs <;> [exact le_rfl; exact hg1]
    have hmain : 1 ≤ √((p : ℝ) ^ ν) / ((ν : ℝ) + 1) * (((p : ℝ) - 1) / ((p : ℝ) + 1)) := by
      rw [div_mul_div_comm, one_le_div (by positivity)]
      linarith
    calc (1 : ℝ) ≤ _ := hmain
      _ ≤ _ := mul_le_mul_of_nonneg_left hfac (by positivity)
  · -- `ν₁ ≥ 1`: the character factor is the same on both sides
    have hc : (0 < k ∧ ¬ p ∣ N ∧ χ p = -1) ↔ (0 < k + ν ∧ ¬ p ∣ N ∧ χ p = -1) := by
      constructor
      · rintro ⟨_, h2⟩; exact ⟨by omega, h2⟩
      · rintro ⟨_, h2⟩; exact ⟨hk, h2⟩
    rw [if_congr hc rfl rfl]
    refine mul_le_mul_of_nonneg_right ?_ (by split_ifs <;> [exact hg0; exact zero_le_one])
    rw [pow_add, Real.sqrt_mul (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    have hk' : (0 : ℝ) ≤ k := by positivity
    have := Real.sqrt_nonneg ((p : ℝ) ^ k)
    -- `(k+ν+1) ≤ (k+1)(ν+1) ≤ (k+1)√(p^ν)`
    have h3 : (k : ℝ) + ν + 1 ≤ ((k : ℝ) + 1) * √((p : ℝ) ^ ν) := by
      have hν0 : (0 : ℝ) ≤ ν := by positivity
      nlinarith
    nlinarith

/-! ### Helpers -/

/-- A product of factors in $[0, 1]$ over a larger set is smaller. -/
theorem prod_le_prod_of_subset_of_le_one {s t : Finset ℕ} {f : ℕ → ℝ} (h : s ⊆ t)
    (h0 : ∀ i ∈ t, 0 ≤ f i) (h1 : ∀ i ∈ t, f i ≤ 1) : ∏ i ∈ t, f i ≤ ∏ i ∈ s, f i := by
  rw [← Finset.prod_sdiff h]
  calc (∏ i ∈ t \ s, f i) * ∏ i ∈ s, f i ≤ 1 * ∏ i ∈ s, f i :=
        mul_le_mul_of_nonneg_right
          (Finset.prod_le_one₀ (fun i hi => h0 i (Finset.mem_sdiff.1 hi).1)
            (fun i hi => h1 i (Finset.mem_sdiff.1 hi).1))
          (Finset.prod_nonneg fun i hi => h0 i (h hi))
    _ = ∏ i ∈ s, f i := one_mul _

/-- $\sqrt{m} = m^{1/2}$ splits as $\sqrt{(m)_{\mathrm{Iso}}}\sqrt{(m)_{\mathrm{Aniso}}}$, and
$\tau(m) = \tau((m)_{\mathrm{Iso}})\tau((m)_{\mathrm{Aniso}})$. -/
theorem divCount_mul_sqrt_split (Q : QuadForm ℤ n) {m : ℕ} (hm : m ≠ 0) :
    (divCount m : ℝ) * (m : ℝ) ^ (1 / 2 : ℝ) =
      (divCount (isoPart Q m) : ℝ) * divCount (anisoPart Q m) *
        (√(isoPart Q m : ℝ) * √(anisoPart Q m : ℝ)) := by
  conv_lhs => rw [← isoPart_mul_anisoPart Q hm]
  rw [divCount_mul (coprime_isoPart_anisoPart Q m), ← Real.sqrt_eq_rpow]
  push_cast
  rw [Real.sqrt_mul (by positivity)]

/-- $\sqrt{m}$ splits along the isotropic and anisotropic parts, $\sqrt m = \sqrt{(m)_{\mathrm{Iso}}}\sqrt{(m)_{\mathrm{Aniso}}}$,
and so does $\tau(m)^2$. -/
theorem divCount_sq_mul_sqrt_split (Q : QuadForm ℤ n) {m : ℕ} (hm : m ≠ 0) :
    (divCount m : ℝ) ^ 2 * (m : ℝ) ^ (1 / 2 : ℝ) =
      (divCount (isoPart Q m) : ℝ) ^ 2 * (divCount (anisoPart Q m) : ℝ) ^ 2 *
        (√(isoPart Q m : ℝ) * √(anisoPart Q m : ℝ)) := by
  conv_lhs => rw [← isoPart_mul_anisoPart Q hm]
  rw [divCount_mul (coprime_isoPart_anisoPart Q m), ← Real.sqrt_eq_rpow]
  push_cast
  rw [Real.sqrt_mul (by positivity)]
  ring

/-- $T'\big(\prod_{p \in S}p^{\nu_p}\big)^2$ in $\mathbb{N}$ is $T'(m')^2$ in $\mathbb{Z}$ with $m'$ = `sqPart S ν`. -/
theorem natCast_mul_sqPart (S : Finset ℕ) (ν : ℕ → ℕ) (T : ℕ) :
    (((T * (∏ p ∈ S, p ^ ν p) ^ 2 : ℕ)) : ℤ) = (T : ℤ) * sqPart S ν ^ 2 := by
  simp [sqPart]

/-! ### Theorem 6.3 ($n = 4$) -/

open Classical in
/-- **Theorem 6.3** (Hanke 2004, p. 381; proof p. 382), conditional form. Let $Q$ be a positive definite integral
quaternary form, $\chi(p) = \left(\frac{\det H}{p}\right)$, and $m = T'(m')^2$ with $m' = \prod_{p \in S}p^{\nu_p}$, $\nu_p \ge 1$,
under the hypotheses of Thm 5.7(b) (`thm_5_7_b_genus`: $T' > 0$ $p$-stable at $p \in S$, $\mathrm{ord}_p(T') \le 1$ at good
$p \in S$). Assume:
- `hTS`, `hCB`: the theta decomposition and (4.8) with $k = n/2 = 2$: $|c(m)| \le C\,\tau(m)\,m^{1/2}$, $C = \sum_i|\gamma_i|$;
- `hSF`: Siegel's formula;
- `hglob` (**global input**, the lower bound for $a_E(T')$ behind $\hat\Lambda_4$, Thm 5.7(b), p. 373, through
  $L_F(2,\chi)$): $\hat\Lambda_4\,(T')_{\mathrm{Iso}}\prod_{p \mid T'\ \mathrm{good},\ \chi(p) = -1}\frac{p-1}{p+1}
  \le a_E(T')\prod_{p \in S \cap \mathrm{Iso},\ p\ \mathrm{bad}}C'_p(T')$.

Then $Q$ represents $m$ whenever
$$\frac{\sqrt{(m)_{\mathrm{Iso}}}}{\tau((m)_{\mathrm{Iso}})}\prod_{\substack{p \mid m\ \mathrm{good}\\ \chi(p) = -1}}\frac{p-1}{p+1}
  \;>\; \frac{C}{\hat\Lambda_4}\,\tau((m)_{\mathrm{Aniso}})\sqrt{(m)_{\mathrm{Aniso}}}.$$
Proof (as in the paper): Thm 5.7(b) and `hglob` give $a_E(m) \ge \hat\Lambda_4(m)_{\mathrm{Iso}}\prod\frac{p-1}{p+1}$, and (4.8)
gives $|c(m)| \le C\tau(m)\sqrt m$; the threshold makes $a_E(m) > |c(m)|$.

*Differences from the paper:* over $\mathbb{Q}$; "good" (`IsGoodPrime`: $p$ odd, $p \nmid \det H$) in place of $p \nmid N$, so the
product runs over a subset of the paper's and the threshold is no stronger; "a priori bounded divisibility at the
anisotropic primes" and "sufficiently large" are not formalized (they are what makes the threshold eventually hold);
the global bound is the hypothesis `hglob` for the given $T'$ instead of the minimum over $B_{\mathbb T}$.
*Erratum (candidate):* the proof (p. 382) says "(4.8) with $k = n/2 = 4$"; for $n = 4$ it is $k = n/2 = 2$ (which gives the
$\sqrt m$ used). -/
@[kb "hanke2004" "Thm 6.3, p. 381"]
theorem thm_6_3 (Q : IntQF 4) (hQ : IntQF.PosDef Q) (hSF : SiegelFormula Q) {aH c : ℕ → ℝ}
    (hTS : ThetaSplit Q aH c) {C : ℝ} (hCB : CuspBound c (1 / 2) C)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin 4)) {T : ℕ} (hT : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T) (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T)
    (ν : ℕ → ℕ) (hν : ∀ p ∈ S, 1 ≤ ν p) {Λ : ℝ} (hΛ : 0 < Λ)
    (hglob : Λ * isoPart Q T *
        ∏ p ∈ T.primeFactors.filter (fun p => IsGoodPrime Q p ∧ jacobiSym Q.hessian.det p = -1),
          ((p : ℝ) - 1) / ((p : ℝ) + 1) ≤
      genusRepAvg Q T *
        ∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T)
    {m : ℕ} (hm : m = T * (∏ p ∈ S, p ^ ν p) ^ 2)
    (hbound : C / Λ * divCount (anisoPart Q m) * √(anisoPart Q m : ℝ) <
      √(isoPart Q m : ℝ) / divCount (isoPart Q m) *
        ∏ p ∈ m.primeFactors.filter (fun p => IsGoodPrime Q p ∧ jacobiSym Q.hessian.det p = -1),
          ((p : ℝ) - 1) / ((p : ℝ) + 1)) :
    IntQF.Represents Q m := by
  have hm'pos : 0 < ∏ p ∈ S, p ^ ν p := Finset.prod_pos fun p hp => pow_pos (hS p hp).pos _
  have hm0 : m ≠ 0 := by rw [hm]; positivity
  have h57 := thm_5_7_b_genus Q hSF hQ hS S₀ (T := (T : ℤ)) (by exact_mod_cast hT) hst hT2 ν
  rw [← natCast_mul_sqPart, ← hm] at h57
  set I' : ℝ := ∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p with hI'
  set Cb : ℝ := ∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
    localConstC' Q p T with hCb
  set Pg : ℝ := ∏ p ∈ (S.filter (IsGoodPrime Q)).filter
    (fun p => jacobiSym Q.hessian.det p = -1 ∧ ¬ (p : ℤ) ∣ T), (1 + 1 / (p : ℝ))⁻¹ with hPg
  set g : ℕ → ℝ := fun p => ((p : ℝ) - 1) / ((p : ℝ) + 1) with hg
  set P : ℕ → Prop := fun p => IsGoodPrime Q p ∧ jacobiSym Q.hessian.det p = -1 with hP
  set GT : ℝ := ∏ p ∈ T.primeFactors.filter P, g p with hGT
  set Fm : ℝ := ∏ p ∈ m.primeFactors.filter P, g p with hFm
  -- the isotropic part along the square class
  have hiso : (isoPart Q m : ℝ) = isoPart Q T * I' ^ 2 := by
    rw [hm, isoPart_mul Q hT.ne' (pow_ne_zero _ hm'pos.ne'), sq, isoPart_mul Q hm'pos.ne' hm'pos.ne',
      isoPart_prod_pow Q hS ν, hI']
    push_cast; ring
  -- the character product: `F(m) ≤ G(T') · P_good`
  have hg01 : ∀ p : ℕ, p.Prime → 0 ≤ g p ∧ g p ≤ 1 := fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    exact ⟨div_nonneg (by linarith) (by linarith), by rw [hg, div_le_one (by linarith)]; linarith⟩
  have hF : Fm ≤ GT * Pg := by
    set B2 := (S.filter (IsGoodPrime Q)).filter
      (fun p => jacobiSym Q.hessian.det p = -1 ∧ ¬ (p : ℤ) ∣ T) with hB2
    have hdisj : Disjoint (T.primeFactors.filter P) B2 := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      have h1 : p ∣ T := Nat.dvd_of_mem_primeFactors (Finset.mem_filter.1 hp1).1
      exact (Finset.mem_filter.1 hp2).2.2 (Int.natCast_dvd_natCast.2 h1)
    have hsub : T.primeFactors.filter P ∪ B2 ⊆ m.primeFactors.filter P := by
      intro p hp
      rcases Finset.mem_union.1 hp with hp | hp
      · obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
        refine Finset.mem_filter.2 ⟨Nat.primeFactors_mono ?_ hm0 hp1, hp2⟩
        rw [hm]; exact dvd_mul_right _ _
      · obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
        obtain ⟨hpS, hpG⟩ := Finset.mem_filter.1 hp1
        refine Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hS p hpS, ?_, hm0⟩, hpG, hp2.1⟩
        rw [hm]
        exact Dvd.dvd.mul_left (Dvd.dvd.pow (dvd_trans (dvd_pow_self p (Nat.one_le_iff_ne_zero.1 (hν p hpS)))
          (Finset.dvd_prod_of_mem (fun i => i ^ ν i) hpS)) two_ne_zero) _
    calc Fm ≤ ∏ p ∈ T.primeFactors.filter P ∪ B2, g p :=
          prod_le_prod_of_subset_of_le_one hsub
            (fun p hp => (hg01 p (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1)).1)
            (fun p hp => (hg01 p (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1)).2)
      _ = GT * ∏ p ∈ B2, g p := Finset.prod_union hdisj
      _ ≤ GT * Pg := by
          refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀
            (fun p hp => (hg01 p (hS p (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1)).1)
            (fun p hp => ?_)) (Finset.prod_nonneg fun p hp =>
              (hg01 p (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1)).1)
          have : (2 : ℝ) ≤ p := by
            exact_mod_cast (hS p (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1).two_le
          rw [hg, show (1 + 1 / (p : ℝ))⁻¹ = (p : ℝ) / ((p : ℝ) + 1) by field_simp]
          exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  -- the lower bound for the main term
  have hCb0 : 0 ≤ Cb := Finset.prod_nonneg fun p hp => by
    have : Fact p.Prime := ⟨hS p (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1⟩
    exact localConstC'_nonneg Q hQ.nondegenerate (by norm_num) p T (by exact_mod_cast hT.ne')
  have hPg0 : 0 ≤ Pg := Finset.prod_nonneg fun p _ => by positivity
  have hLB : Λ * isoPart Q m * Fm ≤ genusRepAvg Q m := by
    have hI0 : (0 : ℝ) ≤ isoPart Q T := by positivity
    calc Λ * isoPart Q m * Fm = Λ * isoPart Q T * I' ^ 2 * Fm := by rw [hiso]; ring
      _ ≤ Λ * isoPart Q T * I' ^ 2 * (GT * Pg) :=
          mul_le_mul_of_nonneg_left hF (by positivity)
      _ = (Λ * isoPart Q T * GT) * (I' ^ 2 * Pg) := by ring
      _ ≤ (genusRepAvg Q T * Cb) * (I' ^ 2 * Pg) :=
          mul_le_mul_of_nonneg_right hglob (by positivity)
      _ = genusRepAvg Q T * I' ^ 2 * Cb * Pg := by ring
      _ ≤ genusRepAvg Q m := h57
  -- the cusp-form bound
  have hc := hCB.abs_le m (Nat.one_le_iff_ne_zero.2 hm0)
  rw [mul_assoc, divCount_mul_sqrt_split Q hm0] at hc
  set τI : ℝ := (divCount (isoPart Q m) : ℝ)
  set τA : ℝ := (divCount (anisoPart Q m) : ℝ)
  set sI : ℝ := √(isoPart Q m : ℝ) with hsI
  set sA : ℝ := √(anisoPart Q m : ℝ)
  have hτI : 0 < τI := Nat.cast_pos.2 (divCount_pos (isoPart_pos Q m).ne')
  have hsI0 : 0 < sI := Real.sqrt_pos.2 (by exact_mod_cast isoPart_pos Q m)
  have hss : sI * sI = isoPart Q m := Real.mul_self_sqrt (by positivity)
  have key := mul_lt_mul_of_pos_left hbound (by positivity : 0 < Λ * τI * sI)
  have e1 : Λ * τI * sI * (C / Λ * τA * sA) = C * (τI * τA * (sI * sA)) := by
    field_simp
  have e2 : Λ * τI * sI * (sI / τI * Fm) = Λ * (sI * sI) * Fm := by
    field_simp
  rw [e1, e2, hss] at key
  exact represents_of_abs_lt_aE hTS (by norm_num) (Nat.one_le_iff_ne_zero.2 hm0)
    (by linarith)

open Classical in
/-- **Remark 6.5.1** (Hanke 2004, p. 383) with Thm 6.3: when $m = (m)_{\mathrm{Iso}}$ (no anisotropic primes divide $m$), the
left side of Thm 6.3 is $F_4(m)$ with $N = \det H$ and $\chi(p) = \left(\frac{\det H}{p}\right)$ for odd $p$ (the paper's $N$ is
the level; here "good" is $p$ odd, $p \nmid \det H$). So under the hypotheses of `thm_6_3`, $Q$ represents $m$ as soon as
$F_4(m) > C/\hat\Lambda_4$ (Hanke's §8 criterion, $F_4(m) \ge 177.03$ for $x^2+3y^2+5z^2+7w^2$). Here the condition
"$p$ odd" is folded into $\chi$: $\chi(p) = \left(\frac{\det H}{p}\right)$ for $p$ odd, $\chi(2) = 0$. -/
@[kb "hanke2004" "Remark 6.5.1, p. 383; Thm 6.3, p. 381"]
theorem thm_6_3_F4 (Q : IntQF 4) (hQ : IntQF.PosDef Q) (hSF : SiegelFormula Q) {aH c : ℕ → ℝ}
    (hTS : ThetaSplit Q aH c) {C : ℝ} (hCB : CuspBound c (1 / 2) C)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin 4)) {T : ℕ} (hT : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T) (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T)
    (ν : ℕ → ℕ) (hν : ∀ p ∈ S, 1 ≤ ν p) {Λ : ℝ} (hΛ : 0 < Λ)
    (hglob : Λ * isoPart Q T *
        ∏ p ∈ T.primeFactors.filter (fun p => IsGoodPrime Q p ∧ jacobiSym Q.hessian.det p = -1),
          ((p : ℝ) - 1) / ((p : ℝ) + 1) ≤
      genusRepAvg Q T *
        ∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T)
    {m : ℕ} (hm : m = T * (∏ p ∈ S, p ^ ν p) ^ 2) (hiso : isoPart Q m = m)
    (hbound : C / Λ < F4 Q.hessian.det.natAbs
      (fun p : ℕ => if p = 2 then (0 : ℤ) else jacobiSym Q.hessian.det p) m) :
    IntQF.Represents Q m := by
  have hm0 : m ≠ 0 := by
    rw [hm]; exact mul_ne_zero hT.ne' (pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun p hp =>
      pow_ne_zero _ (hS p hp).ne_zero))
  have han : anisoPart Q m = 1 := by
    have h := isoPart_mul_anisoPart Q hm0
    rw [hiso] at h
    exact (Nat.mul_eq_left hm0).1 h
  refine thm_6_3 Q hQ hSF hTS hCB hS S₀ hT hst hT2 ν hν hΛ hglob hm ?_
  have hprod : ∏ p ∈ m.primeFactors.filter
        (fun p => IsGoodPrime Q p ∧ jacobiSym Q.hessian.det p = -1), ((p : ℝ) - 1) / ((p : ℝ) + 1) =
      ∏ p ∈ m.primeFactors.filter (fun p => ¬ p ∣ Q.hessian.det.natAbs ∧
        (if p = 2 then (0 : ℤ) else jacobiSym Q.hessian.det p) = -1),
        ((p : ℝ) - 1) / ((p : ℝ) + 1) := by
    refine Finset.prod_congr (Finset.filter_congr fun p hp => ?_) fun _ _ => rfl
    have hp := Nat.prime_of_mem_primeFactors hp
    constructor
    · rintro ⟨⟨_, h2, h3⟩, h4⟩
      refine ⟨fun hd => h3 (Int.natCast_dvd.2 hd), ?_⟩
      simp [h2, h4]
    · rintro ⟨h1, h2⟩
      by_cases h2' : p = 2
      · simp [h2'] at h2
      · simp only [h2', ite_false] at h2
        exact ⟨⟨hp, h2', fun hd => h1 (Int.natCast_dvd.1 hd)⟩, h2⟩
  rw [han, hiso, hprod]
  unfold F4 at hbound
  simpa [divCount] using hbound

/-! ### Theorem 6.4 ($n \ge 5$) -/

/-- $(XY^2)^a = X^aY^{2a}$ for $X, Y \ge 0$ (real powers). -/
theorem mul_sq_rpow {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (a : ℝ) :
    (X * Y ^ 2) ^ a = X ^ a * Y ^ (2 * a) := by
  rw [Real.mul_rpow hX (by positivity), ← Real.rpow_natCast Y 2, ← Real.rpow_mul hY]
  norm_num

open Classical in
/-- **Theorem 6.4, $n$ even** (Hanke 2004, p. 382), conditional form. Let $Q$ be positive definite in $n \ge 5$ variables,
$n$ even, $m = T'(m')^2$ with $m' = \prod_{p \in S}p^{\nu_p}$ under the hypotheses of Thm 5.7(c) (`thm_5_7_c_even_genus`), and
$Q$ isotropic at every $p \in S$ (`hIso`; true for all $p$ when $n \ge 5$, a classical fact not formalized here). Assume
the theta decomposition, Siegel's formula, (4.8) with $k = n/2$: $|c(m)| \le C\tau(m)m^{(n-2)/4}$, and (**global input**, the
bound behind $\hat\Lambda_n$, Thm 5.7(c), p. 373, through $L_F(n/2, \Phi_n)$, $\zeta_F(n-2)/\zeta_F((n-2)/2)$; `hglob`)
$$\hat\Lambda_n\,(T')^{(n-2)/2} \le a_E(T')\prod_{p \in S \cap \mathrm{Iso},\ p\ \mathrm{bad}}C'_p(T')
  \prod_{\substack{p \in S\ \mathrm{good},\ p \nmid T'\\ \Phi_n(p) = -1}}\frac{X_p}{X_p+1}, \qquad X_p = p^{(n-2)/2}.$$
Then $Q$ represents $m$ whenever $\dfrac{m^{(n-2)/4}}{\tau(m)} > \dfrac{C}{\hat\Lambda_n}$.

*Erratum (candidate):* the paper prints "$\ge$"; the argument (making $a_E(m) > |a(m)|$) needs "$>$". -/
@[kb "hanke2004" "Thm 6.4, p. 382 (n even)"]
theorem thm_6_4_even (Q : IntQF n) (hQ : IntQF.PosDef Q) (hn : 5 ≤ n) (heven : Even n)
    (hSF : SiegelFormula Q) {aH c : ℕ → ℝ} (hTS : ThetaSplit Q aH c) {C : ℝ}
    (hCB : CuspBound c (((n : ℝ) - 2) / 4) C)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hIso : ∀ p ∈ S, IsIsotropicPrime Q p)
    (S₀ : Finset (Fin n)) {T : ℕ} (hT : 0 < T) (hst : ∀ p ∈ S, IsPStable Q S₀ p T)
    (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ → ℕ) {Λ : ℝ} (hΛ : 0 < Λ)
    (hglob : Λ * (T : ℝ) ^ ((n - 2) / 2) ≤ genusRepAvg Q T *
        (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T) *
        ∏ p ∈ (S.filter (IsGoodPrime Q)).filter
            (fun p => jacobiSym ((-1) ^ (n / 2) * Q.hessian.det) p = -1 ∧ ¬ (p : ℤ) ∣ T),
          (p : ℝ) ^ ((n - 2) / 2) / ((p : ℝ) ^ ((n - 2) / 2) + 1))
    {m : ℕ} (hm : m = T * (∏ p ∈ S, p ^ ν p) ^ 2)
    (hbound : C / Λ < (m : ℝ) ^ (((n : ℝ) - 2) / 4) / divCount m) :
    IntQF.Represents Q m := by
  have hm'pos : 0 < ∏ p ∈ S, p ^ ν p := Finset.prod_pos fun p hp => pow_pos (hS p hp).pos _
  have hm0 : m ≠ 0 := by rw [hm]; positivity
  have h57 := thm_5_7_c_even_genus Q hSF hQ (by omega) heven hS S₀ (T := (T : ℤ))
    (by exact_mod_cast hT) hst hT2 ν
  rw [← natCast_mul_sqPart, ← hm, Finset.filter_true_of_mem hIso] at h57
  rw [Finset.filter_true_of_mem hIso] at hglob
  set M : ℝ := ∏ p ∈ S, (p : ℝ) ^ ν p with hM
  have hMm : (m : ℝ) = T * M ^ 2 := by rw [hm, hM]; push_cast; rfl
  set k := (n - 2) / 2 with hk
  have hk2 : 2 * k = n - 2 := Nat.two_mul_div_two_of_even (by
    rcases heven with ⟨j, rfl⟩; exact ⟨j - 1, by omega⟩)
  -- the main term: `a_E(m) ≥ Λ m^k`
  have hLB : Λ * (m : ℝ) ^ k ≤ genusRepAvg Q m := by
    have hrest : 0 ≤ M ^ (n - 2) := by positivity
    calc Λ * (m : ℝ) ^ k = Λ * (T : ℝ) ^ k * M ^ (n - 2) := by
          rw [hMm, mul_pow, ← pow_mul, hk2]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hglob hrest
      _ = _ := by ring
      _ ≤ genusRepAvg Q m := h57
  -- the cusp-form bound and the threshold
  have hc := hCB.abs_le m (Nat.one_le_iff_ne_zero.2 hm0)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  set x : ℝ := (m : ℝ) ^ (((n : ℝ) - 2) / 4) with hx
  have hx0 : 0 < x := Real.rpow_pos_of_pos hmpos _
  have hxx : x * x = (m : ℝ) ^ k := by
    rw [hx, ← Real.rpow_add hmpos, ← Real.rpow_natCast]
    congr 1
    have := congrArg (Nat.cast (R := ℝ)) hk2
    push_cast [Nat.cast_sub (by omega : 2 ≤ n)] at this
    linarith
  set τ : ℝ := (divCount m : ℝ)
  have hτ : 0 < τ := Nat.cast_pos.2 (divCount_pos hm0)
  have key := mul_lt_mul_of_pos_left hbound (by positivity : 0 < Λ * τ * x)
  have e1 : Λ * τ * x * (C / Λ) = C * τ * x := by field_simp
  have e2 : Λ * τ * x * (x / τ) = Λ * (x * x) := by field_simp
  rw [e1, e2, hxx] at key
  exact represents_of_abs_lt_aE hTS (by omega) (Nat.one_le_iff_ne_zero.2 hm0) (by linarith)

open Classical in
/-- **Theorem 6.4, $n$ odd** (Hanke 2004, p. 382, "under Assumption 1", i.e. Assumption 4.4), conditional form. Let $Q$ be
positive definite in $n \ge 5$ variables, $n$ odd, $m = T'(m')^2$ as in Thm 5.7(c) (`thm_5_7_c_odd_genus`) with $Q$ isotropic
at $p \in S$ (`hIso`), and also $m = tm_0^2$ with $t$ squarefree. Assume the theta decomposition, Siegel's formula, (4.10):
$|c(tm_0^2)| \le B\,t^{(n-1)/4-\eta+\varepsilon'}\tau(m_0)^2m_0^{(n-2)/2}$ ($B = B_{\varepsilon'}\sum_k|\delta_k|$), and (**global input**,
the bound (5.14) behind $\hat\Lambda_n$, through $L_F((n-1)/2, \Phi_n)/\zeta_F(n-1)$ and $\zeta_F(n-2)/\zeta_F((n-1)/2)$; `hglob`)
$$\hat\Lambda_n\,(T')^{(n-2)/2} \le a_E(T')\prod_{p \in S \cap \mathrm{Iso},\ p\ \mathrm{bad}}C'_p(T')
  \prod_{\substack{p \in S\ \mathrm{good},\ p \nmid T'\\ \Phi_n(p) = 1}}\frac{1 - p^{-(n-1)/2}}{1 - p^{-(n-2)}}.$$
Then $Q$ represents $m$ whenever
$$\frac{t^{(n-3)/4+\eta-\varepsilon'}\,m_0^{(n-2)/2}}{\tau(m_0)^2} > \frac{B}{\hat\Lambda_n}.$$
*Erratum (candidates):* "Assumption 1" should read "Assumption 4.4"; "$\ge$" should be "$>$" (as for $n$ even). -/
@[kb "hanke2004" "Thm 6.4, p. 382 (n odd)"]
theorem thm_6_4_odd (Q : IntQF n) (hQ : IntQF.PosDef Q) (hn : 5 ≤ n) (hodd : Odd n)
    (hSF : SiegelFormula Q) {aH c : ℕ → ℝ} (hTS : ThetaSplit Q aH c) {B η ε' : ℝ}
    (hCB : CuspBoundUniform c (((n : ℝ) - 2) / 2) (((n : ℝ) - 1) / 4 - η + ε') B)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hIso : ∀ p ∈ S, IsIsotropicPrime Q p)
    (S₀ : Finset (Fin n)) {T : ℕ} (hT : 0 < T) (hst : ∀ p ∈ S, IsPStable Q S₀ p T)
    (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ → ℕ) {Λ : ℝ} (hΛ : 0 < Λ)
    (hglob : Λ * (T : ℝ) ^ (((n : ℝ) - 2) / 2) ≤ genusRepAvg Q T *
        (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T) *
        ∏ p ∈ (S.filter (IsGoodPrime Q)).filter (fun p : ℕ => ¬ (p : ℤ) ∣ T ∧
            jacobiSym ((-1) ^ ((n - 1) / 2) * (2 * Q.hessian.det) * T) p = 1),
          (1 - 1 / (p : ℝ) ^ ((n - 1) / 2)) / (1 - 1 / (p : ℝ) ^ (n - 2)))
    {m : ℕ} (hm : m = T * (∏ p ∈ S, p ^ ν p) ^ 2) {t m₀ : ℕ} (ht : Squarefree t)
    (hmt : m = t * m₀ ^ 2)
    (hbound : B / Λ < (t : ℝ) ^ (((n : ℝ) - 3) / 4 + η - ε') * (m₀ : ℝ) ^ (((n : ℝ) - 2) / 2) /
      (divCount m₀ : ℝ) ^ 2) :
    IntQF.Represents Q m := by
  have hm'pos : 0 < ∏ p ∈ S, p ^ ν p := Finset.prod_pos fun p hp => pow_pos (hS p hp).pos _
  have hm0 : m ≠ 0 := by rw [hm]; positivity
  have ht0 : t ≠ 0 := by rintro rfl; simp at hmt; exact hm0 hmt
  have hm₀0 : m₀ ≠ 0 := by rintro rfl; simp at hmt; exact hm0 hmt
  have h57 := thm_5_7_c_odd_genus Q hSF hQ (by omega) hodd hS S₀ (T := (T : ℤ))
    (by exact_mod_cast hT) hst hT2 ν
  rw [← natCast_mul_sqPart, ← hm, Finset.filter_true_of_mem hIso] at h57
  rw [Finset.filter_true_of_mem hIso] at hglob
  set a : ℝ := ((n : ℝ) - 2) / 2 with ha
  have h2a : 2 * a = ((n - 2 : ℕ) : ℝ) := by rw [ha, Nat.cast_sub (by omega)]; push_cast; ring
  set M : ℝ := ∏ p ∈ S, (p : ℝ) ^ ν p with hM
  have hM0 : 0 ≤ M := by positivity
  have hMm : (m : ℝ) = T * M ^ 2 := by rw [hm, hM]; push_cast; rfl
  have hmt' : (m : ℝ) = t * (m₀ : ℝ) ^ 2 := by rw [hmt]; push_cast; rfl
  -- the main term: `a_E(m) ≥ Λ m^a = Λ t^a m₀^{2a}`
  have hLB : Λ * ((t : ℝ) ^ a * (m₀ : ℝ) ^ (2 * a)) ≤ genusRepAvg Q m := by
    have hrest : 0 ≤ M ^ (n - 2) := by positivity
    calc Λ * ((t : ℝ) ^ a * (m₀ : ℝ) ^ (2 * a)) = Λ * (m : ℝ) ^ a := by
          rw [hmt', mul_sq_rpow (by positivity) (by positivity)]
      _ = Λ * (T : ℝ) ^ a * M ^ (n - 2) := by
          rw [hMm, mul_sq_rpow (by positivity) hM0, h2a, Real.rpow_natCast]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hglob hrest
      _ = _ := by ring
      _ ≤ genusRepAvg Q m := h57
  -- the cusp-form bound (4.10)
  have hc := hCB.abs_le t m₀ ht (Nat.one_le_iff_ne_zero.2 ht0) (Nat.one_le_iff_ne_zero.2 hm₀0)
  rw [← hmt] at hc
  have htpos : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero ht0
  have hm₀pos : (0 : ℝ) < m₀ := by exact_mod_cast Nat.pos_of_ne_zero hm₀0
  set τ : ℝ := (divCount m₀ : ℝ)
  have hτ : 0 < τ := Nat.cast_pos.2 (divCount_pos hm₀0)
  set β : ℝ := ((n : ℝ) - 1) / 4 - η + ε'
  set γ : ℝ := ((n : ℝ) - 3) / 4 + η - ε'
  have hβγ : β + γ = a := by simp only [β, γ, ha]; ring
  clear_value β γ
  have key := mul_lt_mul_of_pos_left hbound
    (by positivity : 0 < Λ * (t : ℝ) ^ β * τ ^ 2 * (m₀ : ℝ) ^ a)
  have e1 : Λ * (t : ℝ) ^ β * τ ^ 2 * (m₀ : ℝ) ^ a * (B / Λ) =
      B * (t : ℝ) ^ β * τ ^ 2 * (m₀ : ℝ) ^ a := by field_simp
  have e2 : Λ * (t : ℝ) ^ β * τ ^ 2 * (m₀ : ℝ) ^ a * ((t : ℝ) ^ γ * (m₀ : ℝ) ^ a / τ ^ 2) =
      Λ * ((t : ℝ) ^ (β + γ) * (m₀ : ℝ) ^ (a + a)) := by
    rw [Real.rpow_add htpos, Real.rpow_add hm₀pos]; field_simp
  rw [e1, e2, hβγ, show a + a = 2 * a by ring] at key
  exact represents_of_abs_lt_aE hTS (by omega) (Nat.one_le_iff_ne_zero.2 hm0) (by linarith)

/-! ### Theorems 6.1 and 6.2 ($n = 3$) -/

open Classical in
/-- The ternary main term along a square class (Thm 5.7(a), first part, for $a_E$; `thm_5_7_a_genus`), with $m$ in
$\mathbb{N}$: $a_E(T')\prod_{p \in S \cap \mathrm{Iso},\ p\ \mathrm{bad}}C'_p(T')\cdot(m')_{\mathrm{Iso}} \le a_E(m)$. -/
theorem thm_5_7_a_genus_nat (Q : IntQF 3) (hQ : IntQF.PosDef Q) {P : ℤ → ℝ}
    (hSF : SiegelFormula3 Q P) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin 3))
    {T : ℕ} (hT : 0 < T) (hst : ∀ p ∈ S, IsPStable Q S₀ p T)
    (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ → ℕ) {m : ℕ}
    (hm : m = T * (∏ p ∈ S, p ^ ν p) ^ 2)
    (hP : IsEulerProductValue Q T (P T)) (hPm : IsEulerProductValue Q m (P m)) :
    genusRepAvg Q T *
        (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T) *
        ∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p ≤ genusRepAvg Q m := by
  have hmZ : ((m : ℕ) : ℤ) = (T : ℤ) * sqPart S ν ^ 2 := by rw [hm, natCast_mul_sqPart]
  have h := thm_5_7_a_genus Q hSF hQ hS S₀ (T := (T : ℤ)) (by exact_mod_cast hT) hst hT2 ν hP
    (by rw [← hmZ]; exact hPm)
  rwa [← hmZ] at h

open Classical in
/-- **Theorem 6.1, first case** (Hanke 2004, p. 380; proof Case 1, p. 380), conditional form. Let $Q$ be a positive definite
ternary form, $t$ squarefree, $T' = ts^2$, $m = T'(m')^2 = tm_0^2$ with $m' = \prod_{p \in S}p^{\nu_p}$, $m_0 = sm'$, under the
hypotheses of Thm 5.7(a) (`thm_5_7_a_genus`; $n = 3$ uses Siegel's formula relative to the natural-order values $P$ of the
Euler products at $T'$ and $m$). Let $\Lambda_3(T') = a_E(T')\prod_{p \in S \cap \mathrm{Iso},\ p\ \mathrm{bad}}C'_p(T')$ and
$K > 0$, and assume
- the theta decomposition and (4.9) in the square class $t\mathbb{Z}^2$: $|c(tm_0^2)| \le C\tau(m_0)^2m_0^{1/2}$, $C = \sum_i|\gamma_i|$;
- `hH`: $a_H(m) \ge 0$, or $a_E(m) + a_H(m) \ge K\,(m')_{\mathrm{Iso}}$ (this is Thm 5.9(a)(ii) with $K = K'(\tilde T)$, not
  formalized, an input here; Thm 5.9(a)(i) and (b)(i) are the case $a_H(m) \ge 0$).

Then $Q$ represents $m$ whenever
$$\frac{\sqrt{(m_0)_{\mathrm{Iso}}}}{\tau((m_0)_{\mathrm{Iso}})^2} > M_3\,\tau((m_0)_{\mathrm{Aniso}})^2\sqrt{(m_0)_{\mathrm{Aniso}}},
  \qquad M_3 = \frac{C\,(s)_{\mathrm{Iso}}}{\min\{\Lambda_3(T'), K\}},\quad s = (T'/t)^{1/2}.$$
*Erratum (candidate):* the paper prints $M_3 = \sum_i|\gamma_i|/[(\tilde T/t)^{1/2}_{\mathrm{Iso}}\min\{\Lambda_3(\tilde T), K'(\tilde T)\}]$,
with $(\tilde T/t)^{1/2}_{\mathrm{Iso}}$ in the denominator. Since $(m_0)_{\mathrm{Iso}} = (s)_{\mathrm{Iso}}(m')_{\mathrm{Iso}}$, the lower bound
$a_E(m) + a_H(m) \ge \min\{\Lambda_3, K'\}(m')_{\mathrm{Iso}}$ equals $\min\{\Lambda_3, K'\}(m_0)_{\mathrm{Iso}}/(s)_{\mathrm{Iso}}$, so the factor
belongs in the numerator (they agree when $(s)_{\mathrm{Iso}} = 1$).
*Not formalized:* the second case ($\tilde T$ of exceptional type, $a_H(m) < 0$; needs Thm 5.6 and 5.9(b)(ii)), "sufficiently
large" and the exceptional sequences $\tilde Tp^2$, and the reduction to $\tilde m$ supported on $\mathrm{VStable}(\tilde T)$
(here: the stability hypotheses of Thm 5.7(a) at $p \in S$). -/
@[kb "hanke2004" "Thm 6.1, p. 380 (first case)"]
theorem thm_6_1 (Q : IntQF 3) (hQ : IntQF.PosDef Q) {P : ℤ → ℝ} (hSF : SiegelFormula3 Q P)
    {aH c : ℕ → ℝ} (hTS : ThetaSplit Q aH c) {t : ℕ} {C : ℝ}
    (hCB : CuspBoundSqClass c t (1 / 2) C)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin 3)) {T : ℕ} (hT : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T) (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T)
    (ν : ℕ → ℕ) {s : ℕ} (hTts : T = t * s ^ 2)
    {m m₀ : ℕ} (hm : m = T * (∏ p ∈ S, p ^ ν p) ^ 2) (hm₀ : m₀ = s * ∏ p ∈ S, p ^ ν p)
    (hP : IsEulerProductValue Q T (P T)) (hPm : IsEulerProductValue Q m (P m)) {K : ℝ}
    (hpos : 0 < min (genusRepAvg Q T *
        ∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T) K)
    (hH : 0 ≤ aH m ∨
      K * ∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p ≤ genusRepAvg Q m + aH m)
    (hbound : C * isoPart Q s / min (genusRepAvg Q T *
          ∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
            localConstC' Q p T) K *
        (divCount (anisoPart Q m₀) : ℝ) ^ 2 * √(anisoPart Q m₀ : ℝ) <
      √(isoPart Q m₀ : ℝ) / (divCount (isoPart Q m₀) : ℝ) ^ 2) :
    IntQF.Represents Q m := by
  have hm'pos : 0 < ∏ p ∈ S, p ^ ν p := Finset.prod_pos fun p hp => pow_pos (hS p hp).pos _
  have hs0 : s ≠ 0 := by rintro rfl; simp at hTts; omega
  have hmt : m = t * m₀ ^ 2 := by rw [hm, hm₀, hTts]; ring
  have hm0 : m ≠ 0 := by rw [hm]; positivity
  have hm₀0 : m₀ ≠ 0 := by rw [hm₀]; exact mul_ne_zero hs0 hm'pos.ne'
  have h57 := thm_5_7_a_genus_nat Q hQ hSF hS S₀ hT hst hT2 ν hm hP hPm
  set Cb : ℝ := ∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
    localConstC' Q p T
  set I' : ℝ := ∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p with hI'
  set L : ℝ := min (genusRepAvg Q T * Cb) K
  have hI'0 : 0 ≤ I' := by positivity
  -- the lower bound `a_E(m) + a_H(m) ≥ min{Λ₃, K} (m')_Iso`
  have hLB : L * I' ≤ genusRepAvg Q m + aH m := by
    rcases hH with h | h
    · calc L * I' ≤ genusRepAvg Q T * Cb * I' :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hI'0
        _ ≤ genusRepAvg Q m := h57
        _ ≤ genusRepAvg Q m + aH m := le_add_of_nonneg_right h
    · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hI'0).trans h
  -- `(m₀)_Iso = (s)_Iso (m')_Iso`
  have hiso0 : (isoPart Q m₀ : ℝ) = isoPart Q s * I' := by
    rw [hm₀, isoPart_mul Q hs0 hm'pos.ne', isoPart_prod_pow Q hS ν, hI']; push_cast; ring
  -- the cusp-form bound (4.9)
  have hc := hCB.abs_le m₀ (Nat.one_le_iff_ne_zero.2 hm₀0)
  rw [← hmt, mul_assoc, divCount_sq_mul_sqrt_split Q hm₀0] at hc
  set τI : ℝ := (divCount (isoPart Q m₀) : ℝ)
  set τA : ℝ := (divCount (anisoPart Q m₀) : ℝ)
  set sI : ℝ := √(isoPart Q m₀ : ℝ)
  set sA : ℝ := √(anisoPart Q m₀ : ℝ)
  set σ : ℝ := (isoPart Q s : ℝ)
  have hσ : 0 < σ := Nat.cast_pos.2 (isoPart_pos Q s)
  have hτI : 0 < τI := Nat.cast_pos.2 (divCount_pos (isoPart_pos Q m₀).ne')
  have hsI0 : 0 < sI := Real.sqrt_pos.2 (by exact_mod_cast isoPart_pos Q m₀)
  have hss : sI * sI = σ * I' := by rw [Real.mul_self_sqrt (by positivity), hiso0]
  have key := mul_lt_mul_of_pos_left hbound (by positivity : 0 < L * τI ^ 2 * sI / σ)
  have e1 : L * τI ^ 2 * sI / σ * (C * σ / L * τA ^ 2 * sA) = C * (τI ^ 2 * τA ^ 2 * (sI * sA)) := by
    field_simp
  have e2 : L * τI ^ 2 * sI / σ * (sI / τI ^ 2) = L * (sI * sI) / σ := by
    field_simp
  rw [e1, e2, hss, show L * (σ * I') / σ = L * I' by field_simp] at key
  exact represents_of_abs_lt hTS (Nat.one_le_iff_ne_zero.2 hm0) (by linarith)

open Classical in
/-- **Theorem 6.2** (Hanke 2004, p. 381), conditional form. Let $Q$ be a positive definite ternary form and
$m = T'(m')^2 = tm_0^2$ as in `thm_6_1` ($t$ squarefree, $T' = ts^2$, $m_0 = sm'$), with $t\mathbb{Z}^2$ **not a spinor square
class** (so $a_H(m) = 0$, Def. 4.3). Assume the theta decomposition, Siegel's formula relative to natural-order values, the
uniform bound (4.10) for $n = 3$ (Assumption 4.4): $|c(tm_0^2)| \le B\,t^{1/2-\eta+\varepsilon'}\tau(m_0)^2m_0^{1/2}$,
$B = B_{\varepsilon'}\sum_k|\delta_k|$, and (**global input**, `hglob`, the second part of Thm 5.7(a), p. 372, which uses
$L(1, \psi_t) \ge C_\varepsilon t^{-\varepsilon}$ and $\zeta(2)$; stated at $T'$):
$$\hat\Lambda_3\,t^{1/2-\varepsilon}(s)_{\mathrm{Iso}} \le \Lambda_3(T') = a_E(T')\prod_{p \in S \cap \mathrm{Iso},\ p\ \mathrm{bad}}C'_p(T'),$$
which with Thm 5.7(a) gives the paper's $a_E(m) \ge \hat\Lambda_3t^{1/2-\varepsilon}(m_0)_{\mathrm{Iso}}$. Then $Q$ represents $m$ whenever
$$\frac{t^{\eta-(\varepsilon+\varepsilon')}\sqrt{(m_0)_{\mathrm{Iso}}}}{\tau((m_0)_{\mathrm{Iso}})^2}
  > \frac{B}{\hat\Lambda_3}\,\tau((m_0)_{\mathrm{Aniso}})^2\sqrt{(m_0)_{\mathrm{Aniso}}}.$$
*Erratum (candidate):* the paper prints "$\ge$"; "$>$" is needed. *Not formalized:* "sufficiently large" (the threshold
holds eventually when $\eta > \varepsilon + \varepsilon'$ and the anisotropic part is bounded). -/
@[kb "hanke2004" "Thm 6.2, p. 381"]
theorem thm_6_2 (Q : IntQF 3) (hQ : IntQF.PosDef Q) {P : ℤ → ℝ} (hSF : SiegelFormula3 Q P)
    {aH c : ℕ → ℝ} (hTS : ThetaSplit Q aH c) {B η ε ε' : ℝ}
    (hCB : CuspBoundUniform c (1 / 2) (1 / 2 - η + ε') B)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin 3)) {T : ℕ} (hT : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T) (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T)
    (ν : ℕ → ℕ) {t s : ℕ} (ht : Squarefree t) (hTts : T = t * s ^ 2)
    (hspin : ¬ IsSpinorSquareClass aH t) {Λ : ℝ} (hΛ : 0 < Λ)
    (hglob : Λ * (t : ℝ) ^ (1 / 2 - ε) * isoPart Q s ≤ genusRepAvg Q T *
        ∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T)
    {m m₀ : ℕ} (hm : m = T * (∏ p ∈ S, p ^ ν p) ^ 2) (hm₀ : m₀ = s * ∏ p ∈ S, p ^ ν p)
    (hP : IsEulerProductValue Q T (P T)) (hPm : IsEulerProductValue Q m (P m))
    (hbound : B / Λ * (divCount (anisoPart Q m₀) : ℝ) ^ 2 * √(anisoPart Q m₀ : ℝ) <
      (t : ℝ) ^ (η - (ε + ε')) * √(isoPart Q m₀ : ℝ) / (divCount (isoPart Q m₀) : ℝ) ^ 2) :
    IntQF.Represents Q m := by
  have hm'pos : 0 < ∏ p ∈ S, p ^ ν p := Finset.prod_pos fun p hp => pow_pos (hS p hp).pos _
  have hs0 : s ≠ 0 := by rintro rfl; simp at hTts; omega
  have ht0 : t ≠ 0 := by rintro rfl; simp at hTts; omega
  have hmt : m = t * m₀ ^ 2 := by rw [hm, hm₀, hTts]; ring
  have hm0 : m ≠ 0 := by rw [hm]; positivity
  have hm₀0 : m₀ ≠ 0 := by rw [hm₀]; exact mul_ne_zero hs0 hm'pos.ne'
  have haH : aH m = 0 := by
    by_contra h
    exact hspin ⟨m₀, by rwa [← hmt]⟩
  have h57 := thm_5_7_a_genus_nat Q hQ hSF hS S₀ hT hst hT2 ν hm hP hPm
  set Cb : ℝ := ∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
    localConstC' Q p T
  set I' : ℝ := ∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p with hI'
  have hI'0 : 0 ≤ I' := by positivity
  have hiso0 : (isoPart Q m₀ : ℝ) = isoPart Q s * I' := by
    rw [hm₀, isoPart_mul Q hs0 hm'pos.ne', isoPart_prod_pow Q hS ν, hI']; push_cast; ring
  set u : ℝ := (t : ℝ) ^ (1 / 2 - ε)
  -- the main term: `a_E(m) ≥ Λ̂₃ t^{1/2-ε} (m₀)_Iso`
  have hLB : Λ * u * isoPart Q m₀ ≤ genusRepAvg Q m := by
    calc Λ * u * isoPart Q m₀ = (Λ * u * isoPart Q s) * I' := by rw [hiso0]; ring
      _ ≤ genusRepAvg Q T * Cb * I' := mul_le_mul_of_nonneg_right hglob hI'0
      _ ≤ genusRepAvg Q m := h57
  -- the cusp-form bound (4.10)
  have hc := hCB.abs_le t m₀ ht (Nat.one_le_iff_ne_zero.2 ht0) (Nat.one_le_iff_ne_zero.2 hm₀0)
  rw [← hmt, mul_assoc, divCount_sq_mul_sqrt_split Q hm₀0] at hc
  have htpos : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero ht0
  set τI : ℝ := (divCount (isoPart Q m₀) : ℝ)
  set τA : ℝ := (divCount (anisoPart Q m₀) : ℝ)
  set sI : ℝ := √(isoPart Q m₀ : ℝ)
  set sA : ℝ := √(anisoPart Q m₀ : ℝ)
  have hτI : 0 < τI := Nat.cast_pos.2 (divCount_pos (isoPart_pos Q m₀).ne')
  have hsI0 : 0 < sI := Real.sqrt_pos.2 (by exact_mod_cast isoPart_pos Q m₀)
  have hss : sI * sI = isoPart Q m₀ := Real.mul_self_sqrt (by positivity)
  set β : ℝ := 1 / 2 - η + ε'
  set γ : ℝ := η - (ε + ε')
  have hβγ : (t : ℝ) ^ β * (t : ℝ) ^ γ = u := by
    rw [← Real.rpow_add htpos]; congr 1; simp only [β, γ]; ring
  clear_value β γ u
  have key := mul_lt_mul_of_pos_left hbound (by positivity : 0 < Λ * (t : ℝ) ^ β * τI ^ 2 * sI)
  have e1 : Λ * (t : ℝ) ^ β * τI ^ 2 * sI * (B / Λ * τA ^ 2 * sA) =
      B * (t : ℝ) ^ β * (τI ^ 2 * τA ^ 2 * (sI * sA)) := by field_simp
  have e2 : Λ * (t : ℝ) ^ β * τI ^ 2 * sI * ((t : ℝ) ^ γ * sI / τI ^ 2) =
      Λ * ((t : ℝ) ^ β * (t : ℝ) ^ γ) * (sI * sI) := by field_simp
  rw [e1, e2, hβγ, hss] at key
  exact represents_of_abs_lt hTS (Nat.one_le_iff_ne_zero.2 hm0)
    (by rw [haH, add_zero]; linarith)

end QuadFormsKB.Siegel
