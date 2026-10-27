/-
# Local densities of the sum of four squares at every prime, for every $m \ge 1$

$I_4 = x_0^2 + x_1^2 + x_2^2 + x_3^2$ (`AWS.Q4`), $\beta_p(m)$ = `LocalDensity.localDensity` (Hanke 2004, (5.1)–(5.2)),
$\nu = \mathrm{ord}_p(m)$.

* **Odd $p$** (`localDensity_Q4_odd`): $\beta_p(m) = (1 - p^{-2})(1 + p^{-1} + \dots + p^{-\nu})$.
  *Proof:* $\nu = 0, 1$ are the AWS notes' Lemma 2.7.4 (`AWS.beta_odd_unit`, `AWS.beta_odd_ord_one`). For $\nu \ge 2$
  split the solutions mod $p^k$ into Zero type and the rest: the map $\pi_Z$ gives the Zero part $p^{-2}\beta_p(m/p^2)$,
  and the non-Zero part at $p^2T$ is $K = (r_p(0) - 1)/p^3 = \beta_p(p) = (1 - p^{-2})(1 + p^{-1})$ for every $T$
  (`localDensityOf_nonZero_eq`, `localDensityOf_nonZero_diag_sq`), so $\beta_p(p^2T) = p^{-2}\beta_p(T) + K$
  (`localDensity_Q4_odd_sq_mul`); this is (5.7) with $T' = $ the $p$-free part or $p$ times it.
* **$p = 2$** (`localDensity_Q4_two_nat`): $\beta_2(m) = 1$ for $m$ odd and $\beta_2(m) = 3/2^{\nu}$ for $m$ even.
  *Proof:* the non-Zero-type count stabilizes from level $3$ (Lemma 3.2 at $p = 2$, `repCountGood_add_diag`), so the
  non-Zero part of $\beta_2(m)$ is $r^{\ne 0}_8(m)/2^9$ (`localDensityOf_nonZero_Q4_two`), and by enumerating
  $(\mathbb{Z}/8)^4$ (`decide +kernel`) $r^{\ne 0}_8(m) = 512, 768, 256, 0$ for $m \equiv$ odd, $2 \bmod 4$, $4 \bmod 8$,
  $0 \bmod 8$ (`repCountOf_nonZero_Q4_eight`). With the Zero part $\beta_2(m/4)/4$:
  $\beta_2(2u) = 3/2$, $\beta_2(4u) = \tfrac14 + \tfrac12 = \tfrac34$, $\beta_2(4T) = \beta_2(T)/4$ for $T$ even.

Both agree with Jacobi's $r_4(m) = 8\sum_{d \mid m,\, 4 \nmid d} d$ through Siegel's formula (`Siegel/FourSquaresSiegel.lean`).
-/
import QuadFormsKB.Siegel.FourSquaresJacobi

namespace QuadFormsKB.Siegel

open LocalDensity

/-! ### $p = 2$ -/

section Dyadic

set_option maxRecDepth 100000 in
/-- Enumeration of $(\mathbb{Z}/8)^4$: the number of $\vec{x}$, not all coordinates even, with
$x_0^2 + x_1^2 + x_2^2 + x_3^2 = c$ is $512$ ($c$ odd), $768$ ($c \equiv 2 \bmod 4$), $256$ ($c = 4$), $0$ ($c = 0$). -/
lemma card_sumFourSq_nonZero_zmod8 : ∀ c : ZMod 8,
    (Finset.univ.filter (fun x : ZMod 8 × ZMod 8 × ZMod 8 × ZMod 8 =>
      x.1 ^ 2 + x.2.1 ^ 2 + x.2.2.1 ^ 2 + x.2.2.2 ^ 2 = c ∧
        ¬ (x.1.val % 2 = 0 ∧ x.2.1.val % 2 = 0 ∧ x.2.2.1.val % 2 = 0 ∧ x.2.2.2.val % 2 = 0))).card =
      if c.val % 2 = 1 then 512 else if c.val % 4 = 2 then 768 else if c.val = 4 then 256 else 0 := by
  decide +kernel

lemma zmod8_two_dvd_iff (y : ZMod (2 ^ 3)) : ((2 : ℕ) : ZMod (2 ^ 3)) ∣ y ↔ y.val % 2 = 0 := by
  have h : ∀ y : ZMod 8, (∃ c : ZMod 8, y = 2 * c) ↔ y.val % 2 = 0 := by decide
  exact h y

/-- **Non-Zero-type solutions mod $8$:** $r^{\ne 0}_8(m) = 512, 768, 256, 0$ for $m$ odd, $m \equiv 2 \bmod 4$,
$m \equiv 4 \bmod 8$, $m \equiv 0 \bmod 8$ ($I_4$; "non-Zero type" = not all $x_i$ even). -/
theorem repCountOf_nonZero_Q4_eight (m : ℤ) :
    repCountOf AWS.Q4 2 3 m (fun x => ¬ IsZeroType 2 3 x) =
      if m % 2 = 1 then 512 else if m % 4 = 2 then 768 else if m % 8 = 4 then 256 else 0 := by
  classical
  unfold repCountOf
  have : ∀ x : Fin 4 → ZMod (2 ^ 3),
      (AWS.Q4.evalIn (ZMod (2 ^ 3)) x = ((m : ℤ) : ZMod (2 ^ 3)) ∧ ¬ IsZeroType 2 3 x) ↔
      ((fin4Equiv _ x).1 ^ 2 + (fin4Equiv _ x).2.1 ^ 2 + (fin4Equiv _ x).2.2.1 ^ 2 +
          (fin4Equiv _ x).2.2.2 ^ 2 = ((m : ℤ) : ZMod (2 ^ 3)) ∧
        ¬ ((fin4Equiv _ x).1.val % 2 = 0 ∧ (fin4Equiv _ x).2.1.val % 2 = 0 ∧
          (fin4Equiv _ x).2.2.1.val % 2 = 0 ∧ (fin4Equiv _ x).2.2.2.val % 2 = 0)) := by
    intro x
    refine and_congr ?_ (not_congr ?_)
    · simp [AWS.Q4, QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_four, sq, fin4Equiv]
    · simp only [IsZeroType, fin4Equiv, ← zmod8_two_dvd_iff]
      constructor
      · intro h; exact ⟨h 0, h 1, h 2, h 3⟩
      · rintro ⟨h0, h1, h2, h3⟩ i; fin_cases i <;> assumption
  rw [Nat.card_congr ((Equiv.subtypeEquivRight this).trans ((fin4Equiv _).subtypeEquiv
      (q := fun y : ZMod (2 ^ 3) × ZMod (2 ^ 3) × ZMod (2 ^ 3) × ZMod (2 ^ 3) =>
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2.1 ^ 2 + y.2.2.2 ^ 2 = ((m : ℤ) : ZMod (2 ^ 3)) ∧
          ¬ (y.1.val % 2 = 0 ∧ y.2.1.val % 2 = 0 ∧ y.2.2.1.val % 2 = 0 ∧ y.2.2.2.val % 2 = 0))
      (fun _ => Iff.rfl))),
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine (card_sumFourSq_nonZero_zmod8 ((m : ℤ) : ZMod 8)).trans ?_
  have h8 : ((((m : ℤ) : ZMod 8)).val : ℤ) = m % 8 := ZMod.val_intCast m
  generalize (((m : ℤ) : ZMod 8)).val = v at h8 ⊢
  split_ifs <;> omega

/-- $I_4$ is the diagonal form $\langle 1, 1, 1, 1\rangle$ with all coefficients prime to $p$. -/
lemma Q4_eq_diag : AWS.Q4 = QuadForm.diag fun _ : Fin 4 => (1 : ℤ) := rfl

lemma not_dvd_one_Q4 (p : ℕ) [Fact p.Prime] : ∀ _ : Fin 4, ¬ (p : ℤ) ∣ (1 : ℤ) := fun _ h =>
  (Fact.out : p.Prime).one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h)

/-- **The non-Zero-type density at $p = 2$ is attained at level $3$** (Lemma 3.2 at $p = 2$, $k \ge 2\,\mathrm{ord}_2(2)+1$):
$\beta^{\ne 0}_2(m) = r^{\ne 0}_8(m)/2^9$ for every $m$. -/
theorem localDensityOf_nonZero_Q4_two (m : ℤ) :
    localDensityOf AWS.Q4 2 m (fun k x => ¬ IsZeroType 2 k x) =
      (repCountOf AWS.Q4 2 3 m (fun x => ¬ IsZeroType 2 3 x) : ℝ) / 2 ^ 9 := by
  apply limUnder_eq_of_eventually
  filter_upwards [Filter.eventually_ge_atTop 3] with k hk
  obtain ⟨l, rfl⟩ : ∃ l, k = 3 + l := ⟨k - 3, by omega⟩
  have h := repCountGood_add_diag (fun _ : Fin 4 => (1 : ℤ)) 2 m 3 l (by norm_num)
  rw [isGoodType_diag_unimodular _ 2 (not_dvd_one_Q4 2),
    isGoodType_diag_unimodular _ 2 (not_dvd_one_Q4 2)] at h
  rw [Q4_eq_diag, h]
  push_cast
  rw [show (3 + l) * (4 - 1) = 3 * l + 9 by omega, pow_add]
  field_simp

/-- If $4 \nmid m$ there are no Zero-type solutions, so $\beta_2(m) = r^{\ne 0}_8(m)/2^9$. -/
theorem localDensity_Q4_two_of_not_four_dvd (m : ℤ) (hm : ¬ (4 : ℤ) ∣ m) :
    localDensity AWS.Q4 2 m =
      (repCountOf AWS.Q4 2 3 m (fun x => ¬ IsZeroType 2 3 x) : ℝ) / 2 ^ 9 := by
  rw [← localDensityOf_nonZero_Q4_two]
  unfold localDensity localDensityOf Filter.limUnder
  refine congrArg Filter.lim (Filter.map_congr ?_)
  filter_upwards [Filter.eventually_ge_atTop 2] with k hk
  have hm' : ¬ ((2 : ℕ) : ℤ) ^ 2 ∣ m := by norm_num; exact hm
  rw [repCount_eq_zero_add_nonZero, repCountZero_eq _ 2 m k hk]
  simp only [hm', ↓reduceIte, zero_add]

/-- **The recursion at $p = 2$:** $\beta_2(4T) = \beta_2(T)/4 + r^{\ne 0}_8(4T)/2^9$ for $T \ne 0$ (Zero part by the map
$\pi_Z$). *Update:* so, contrary to the AWS notes, p. 38, the solutions mod 8 do not
determine $\beta_2(m)$ when $4 \mid m$ (e.g. $\beta_2(8) = 3/8$, while $r^{\ne 0}_8(8) = 0$). -/
theorem localDensity_Q4_two_four_mul (T : ℤ) (hT : T ≠ 0) :
    localDensity AWS.Q4 2 (4 * T) = localDensity AWS.Q4 2 T / 4 +
      (repCountOf AWS.Q4 2 3 (4 * T) (fun x => ¬ IsZeroType 2 3 x) : ℝ) / 2 ^ 9 := by
  have h := localDensityOf_nonZero_eq AWS.Q4 nondegenerate_Q4 2 (by norm_num) T hT
  have e : ((2 : ℕ) : ℤ) ^ 2 * T = 4 * T := by norm_num
  rw [e, localDensityOf_nonZero_Q4_two] at h
  norm_num at h
  linarith

/-- **$\beta_2$ of $I_4$ on $2^a u$, $u$ odd:** $\beta_2(2^a u) = 1$ if $a = 0$ and $3/2^a$ if $a \ge 1$. -/
theorem localDensity_Q4_two_pow_mul (a : ℕ) (u : ℤ) (hu : Odd u) :
    localDensity AWS.Q4 2 (2 ^ a * u) = if a = 0 then 1 else 3 / 2 ^ a := by
  obtain ⟨w, rfl⟩ := hu
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    match a with
    | 0 => simpa using localDensity_Q4_two (m := 2 * w + 1) ⟨w, rfl⟩
    | 1 =>
      have hN : (repCountOf AWS.Q4 2 3 (2 ^ 1 * (2 * w + 1)) (fun x => ¬ IsZeroType 2 3 x) : ℝ) = 768 := by
        rw [repCountOf_nonZero_Q4_eight]; norm_cast; split_ifs <;> omega
      rw [localDensity_Q4_two_of_not_four_dvd _ (by omega), hN]
      norm_num
    | a + 2 =>
      have hT : (2 : ℤ) ^ a * (2 * w + 1) ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ two_ne_zero) (by omega)
      rw [show (2 : ℤ) ^ (a + 2) * (2 * w + 1) = 4 * (2 ^ a * (2 * w + 1)) by ring,
        localDensity_Q4_two_four_mul _ hT, ih a (by omega)]
      rcases a with _ | a
      · have hN : (repCountOf AWS.Q4 2 3 (4 * (2 ^ 0 * (2 * w + 1))) (fun x => ¬ IsZeroType 2 3 x) : ℝ)
            = 256 := by
          rw [repCountOf_nonZero_Q4_eight]; norm_cast; split_ifs <;> omega
        rw [hN]
        norm_num
      · have hN : (repCountOf AWS.Q4 2 3 (4 * (2 ^ (a + 1) * (2 * w + 1)))
            (fun x => ¬ IsZeroType 2 3 x) : ℝ) = 0 := by
          rw [show (4 : ℤ) * (2 ^ (a + 1) * (2 * w + 1)) = 8 * (2 ^ a * (2 * w + 1)) by ring,
            repCountOf_nonZero_Q4_eight]
          generalize (2 : ℤ) ^ a * (2 * w + 1) = c
          norm_cast; split_ifs <;> omega
        rw [hN]
        simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, OfNat.ofNat_ne_zero]
        rw [pow_succ, pow_succ, pow_succ]
        ring

/-- **Local density of $x_0^2 + \dots + x_3^2$ at $p = 2$** (all $m \ge 1$): with $\nu = \mathrm{ord}_2(m)$,
$$\beta_2(m) = \begin{cases} 1 & m \text{ odd},\\ 3/2^{\nu} & m \text{ even}.\end{cases}$$
*Update:* the AWS notes' Lemma 2.7.6 gives only $\nu \le 1$. -/
@[kb "hanke2011aws" "§2.7.5, Lemma 2.7.6, p. 39 (extended to even m)"]
theorem localDensity_Q4_two_nat (m : ℕ) (hm : m ≠ 0) :
    localDensity AWS.Q4 2 m =
      if m.factorization 2 = 0 then 1 else 3 / 2 ^ m.factorization 2 := by
  have hodd : Odd (m / 2 ^ m.factorization 2) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Nat.not_dvd_ordCompl Nat.prime_two hm))
  have e : (m : ℤ) = 2 ^ m.factorization 2 * ((m / 2 ^ m.factorization 2 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.ordProj_mul_ordCompl_eq_self m 2).symm
  rw [e, localDensity_Q4_two_pow_mul _ _ (by exact_mod_cast hodd)]

end Dyadic

/-! ### Odd $p$ -/

section Odd

variable (p : ℕ) [Fact p.Prime]

/-- **The non-Zero-type density at $p^2T$, odd $p$:** $K = (1 - p^{-2})(1 + p^{-1})$ for every $T$. -/
theorem localDensityOf_nonZero_Q4_odd_sq (hp : p ≠ 2) (T : ℤ) :
    localDensityOf AWS.Q4 p ((p : ℤ) ^ 2 * T) (fun k x => ¬ IsZeroType p k x) =
      (1 - 1 / (p : ℝ) ^ 2) * (1 + 1 / (p : ℝ)) := by
  have hpp := (Fact.out : p.Prime)
  have h1 : padicValInt p (p : ℤ) = 1 := by simp [padicValInt, padicValNat_self]
  rw [Q4_eq_diag, localDensityOf_nonZero_diag_sq _ p hp (not_dvd_one_Q4 p),
    ← localDensity_diag_ord_one _ p hp (not_dvd_one_Q4 p) _ h1, ← Q4_eq_diag,
    AWS.beta_odd_ord_one p hp p dvd_rfl]
  intro h
  have h' : p ^ 2 ∣ p := by exact_mod_cast h
  have := Nat.le_of_dvd hpp.pos h'
  nlinarith [hpp.two_le]

/-- **The recursion at odd $p$:** $\beta_p(p^2T) = p^{-2}\beta_p(T) + (1 - p^{-2})(1 + p^{-1})$ for $T \ne 0$. -/
theorem localDensity_Q4_odd_sq_mul (hp : p ≠ 2) (T : ℤ) (hT : T ≠ 0) :
    localDensity AWS.Q4 p ((p : ℤ) ^ 2 * T) =
      localDensity AWS.Q4 p T / (p : ℝ) ^ 2 + (1 - 1 / (p : ℝ) ^ 2) * (1 + 1 / (p : ℝ)) := by
  have h := localDensityOf_nonZero_eq AWS.Q4 nondegenerate_Q4 p (by norm_num) T hT
  rw [localDensityOf_nonZero_Q4_odd_sq p hp] at h
  rw [show (4 : ℕ) - 2 = 2 from rfl] at h
  rw [div_eq_mul_inv, mul_comm (localDensity _ _ T)]
  linarith

/-- $\sum_{i \le a+2} x^i = x^2\sum_{i \le a} x^i + 1 + x$. -/
lemma sum_range_add_two (x : ℝ) (a : ℕ) :
    ∑ i ∈ Finset.range (a + 3), x ^ i = x ^ 2 * ∑ i ∈ Finset.range (a + 1), x ^ i + 1 + x := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_succ, pow_zero]
  ring_nf

/-- **$\beta_p$ of $I_4$ on $p^a u$, $p \nmid u$, odd $p$:** $(1 - p^{-2})\sum_{i=0}^{a} p^{-i}$. -/
theorem localDensity_Q4_odd_pow_mul (hp : p ≠ 2) (a : ℕ) (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) :
    localDensity AWS.Q4 p ((p : ℤ) ^ a * u) =
      (1 - 1 / (p : ℝ) ^ 2) * ∑ i ∈ Finset.range (a + 1), (1 / (p : ℝ)) ^ i := by
  have hpp := (Fact.out : p.Prime)
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (dvd_zero _)
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    match a with
    | 0 => simpa using AWS.beta_odd_unit p hp u hu
    | 1 =>
      rw [pow_one, AWS.beta_odd_ord_one p hp _ (dvd_mul_right _ _)]
      · simp [Finset.sum_range_succ]
      · rintro ⟨c, hc⟩
        apply hu
        refine ⟨c, mul_left_cancel₀ (by exact_mod_cast hpp.ne_zero : (p : ℤ) ≠ 0) ?_⟩
        rw [hc]; ring
    | a + 2 =>
      have hT : (p : ℤ) ^ a * u ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hpp.ne_zero)) hu0
      rw [show (p : ℤ) ^ (a + 2) * u = (p : ℤ) ^ 2 * ((p : ℤ) ^ a * u) by ring,
        localDensity_Q4_odd_sq_mul p hp _ hT, ih a (by omega), sum_range_add_two]
      field_simp
      ring

/-- **Local density of $x_0^2 + \dots + x_3^2$ at an odd prime $p$** (all $m \ge 1$): with $\nu = \mathrm{ord}_p(m)$,
$$\beta_p(m) = \Bigl(1 - \frac1{p^2}\Bigr)\Bigl(1 + \frac1p + \dots + \frac1{p^{\nu}}\Bigr).$$
For $\nu \le 1$ this is the AWS notes' Lemma 2.7.4. *Update:* the notes give only
$\nu \le 1$. -/
@[kb "hanke2011aws" "§2.7.4, Lemma 2.7.4, p. 38 (extended to all m)"]
theorem localDensity_Q4_odd (hp : p ≠ 2) (m : ℕ) (hm : m ≠ 0) :
    localDensity AWS.Q4 p m =
      (1 - 1 / (p : ℝ) ^ 2) * ∑ i ∈ Finset.range (m.factorization p + 1), (1 / (p : ℝ)) ^ i := by
  have hpp := (Fact.out : p.Prime)
  have hu : ¬ (p : ℤ) ∣ ((m / p ^ m.factorization p : ℕ) : ℤ) := by
    exact_mod_cast Nat.not_dvd_ordCompl hpp hm
  have e : (m : ℤ) = (p : ℤ) ^ m.factorization p * ((m / p ^ m.factorization p : ℕ) : ℤ) := by
    exact_mod_cast (Nat.ordProj_mul_ordCompl_eq_self m p).symm
  rw [e, localDensity_Q4_odd_pow_mul p hp _ _ hu]

end Odd

end QuadFormsKB.Siegel
