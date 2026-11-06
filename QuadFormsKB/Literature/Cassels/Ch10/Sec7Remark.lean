/-
# Cassels, Chapter 10, §7: strong approximation fails for $O^+(V)$

**Item.** Cassels (Ch. 10, §7, p. 187) explains why the Corollary to Theorem 7.1 (strong approximation for $\Theta$)
has no analogue for $O^+(V)$: there is a finite set $P$ of primes with $\theta(\sigma_p) \in U_p(\mathbb Q_p^\times)^2$
for $p \notin P$ and $\sigma_p \in O^+(\Lambda_p)$, so a global $\sigma \in O^+(V)$ approximating given $\sigma_p \in O^+(V_p)$
($p \in P$) would need a spinor norm $v = \theta(\sigma) \in \mathbb Q^\times$ with $v \in \theta(\sigma_p)(\mathbb Q_p^\times)^2$ for
$p \in P$ and $v \in U_p(\mathbb Q_p^\times)^2$ for $p \notin P$, which need not exist.

**Cassels' example** (read from the page image of p. 187; the machine-read text had lost the formula):
$f(\vec x) = x_1^2 + x_2^2 - x_3^2$, $P = \{2\}$, $\sigma_2 = \tau_{\vec a}\tau_{\vec b}$ with $\vec a = (1, 0, 0)$,
$\vec b = (2, 1, 0)$; then $\theta(\sigma_2) = f(\vec a)f(\vec b)(\mathbb Q_2^\times)^2 = 5(\mathbb Q_2^\times)^2$, and there is no
$v \in \mathbb Q^\times$ with $v \in 5(\mathbb Q_2^\times)^2$ and $v \in U_p(\mathbb Q_p^\times)^2$ for all $p \ne 2$.
Formalized: `spinorNorm_sec7_example` (the spinor norm, O'Meara's `HasSpinorNorm`/`spinorNormHom`, with Cassels'
$x_1, x_2, x_3$ as coordinates $0, 1, 2$) and `no_rational_spinor_value_two` (the obstruction).

*Correction (2026-10-30).* An earlier version of this file (ca-gaps) could not read the page and "reconstructed" the
example as $\theta(\sigma_5) = 3(\mathbb Q_5^\times)^2$ (`no_rational_spinor_value`, kept as a variant); the page shows that the
printed example is correct as it stands, so the erratum recorded for it is withdrawn.

**Proof.** If all odd valuations of $v$ are even and $v \in 5(\mathbb Q_2^\times)^2$, the $2$-adic valuation is even too, so
$v = \pm w^2$ with $w \in \mathbb Q$; then $\pm 5$ is a square in $\mathbb Q_2$, impossible because a $2$-adic unit square is
$\equiv 1 \pmod 8$.
-/
import QuadFormsKB.Literature.OMeara.Sec55
import QuadFormsKB.Citation

namespace QuadFormsKB.Cassels

section Remark

local instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- No $5$-adic number squares to $\pm 3$. -/
theorem r8_pi (t : ℚ_[5]) (e : ℤ) (he : e = 3 ∨ e = -3) (ht : t ^ 2 = (e : ℚ_[5])) : False := by
  have hn : ‖t‖ ^ 2 ≤ 1 := by
    rw [← norm_pow, ht]; exact Padic.norm_int_le_one e
  have h1 : ‖t‖ ≤ 1 := by
    by_contra h
    push Not at h
    nlinarith [norm_nonneg t]
  let ti : ℤ_[5] := ⟨t, h1⟩
  have h2 : ti ^ 2 = (e : ℤ_[5]) := by
    apply Subtype.ext
    simpa using ht
  have h3 := congrArg (PadicInt.toZMod (p := 5)) h2
  simp only [map_pow, map_intCast] at h3
  generalize PadicInt.toZMod (p := 5) ti = r at h3
  rcases he with rfl | rfl
  · revert r; decide
  · revert r; decide

/-- **The obstruction in Cassels' remark after Theorem 7.1, a variant** (Ch. 10, §7, p. 187): there is no
$v \in \mathbb Q^\times$ with $v \in 3(\mathbb Q_5^\times)^2$ and $v \in U_p(\mathbb Q_p^\times)^2$ (even $p$-adic valuation)
for every prime $p \ne 5$. This is the same obstruction with $P = \{5\}$ and spinor norm $3$; Cassels' own example
($P = \{2\}$, spinor norm $5$) is `no_rational_spinor_value_two`. -/
@[kb "cassels1978" "Ch. 10, §7, p. 187 (the analogue for O⁺(V) is false; variant: P = {5}, spinor norm 3)"]
theorem no_rational_spinor_value :
    ¬ ∃ v : ℚ, v ≠ 0 ∧ (∃ s : ℚ_[5], s ≠ 0 ∧ (v : ℚ_[5]) = 3 * s ^ 2) ∧
      ∀ p : ℕ, p.Prime → p ≠ 5 → Even (padicValRat p v) := by
  rintro ⟨v, hv, ⟨s, hs, hvs⟩, hp⟩
  have hv5 : Even (padicValRat 5 v) := by
    have h := Padic.valuation_ratCast (p := 5) v
    rw [hvs] at h
    have h3 : (3 : ℚ_[5]) ≠ 0 := by norm_num
    rw [Padic.valuation_mul h3 (pow_ne_zero 2 hs), Padic.valuation_pow] at h
    have h3v : Padic.valuation (3 : ℚ_[5]) = 0 := by
      have : (3 : ℚ_[5]) = ((3 : ℕ) : ℚ_[5]) := by norm_num
      rw [this, Padic.valuation_natCast]
      have : padicValNat 5 3 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
      simp [this]
    rw [h3v] at h
    rw [← h]
    exact ⟨Padic.valuation s, by push_cast; ring⟩
  have hall : ∀ p : ℕ, p.Prime → Even (padicValRat p v) := by
    intro p pp
    by_cases h5 : p = 5
    · subst h5; exact hv5
    · exact hp p pp h5
  have key : ∃ w : ℚ, ∃ e : ℤ, (e = 1 ∨ e = -1) ∧ v = e * w ^ 2 := by
    rcases lt_or_gt_of_ne hv with h | h
    · have hsq : IsSquare (-v) := by
        rw [Rat.isSquare_iff_even_factorization]
        refine ⟨by linarith, fun p pp => ?_⟩
        have : Fact p.Prime := ⟨pp⟩
        rw [padicValRat.neg]; exact hall p pp
      obtain ⟨w, hw⟩ := hsq
      exact ⟨w, -1, Or.inr rfl, by push_cast; linarith [hw, sq w]⟩
    · have hsq : IsSquare v := by
        rw [Rat.isSquare_iff_even_factorization]
        exact ⟨h.le, hall⟩
      obtain ⟨w, hw⟩ := hsq
      exact ⟨w, 1, Or.inl rfl, by push_cast; linarith [hw, sq w]⟩
  obtain ⟨w, e, he, hvw⟩ := key
  have hw : (w : ℚ_[5]) ≠ 0 := by
    intro h0
    have : w = 0 := by exact_mod_cast h0
    apply hv; rw [hvw, this]; simp
  have heq : (e : ℚ_[5]) * (w : ℚ_[5]) ^ 2 = 3 * s ^ 2 := by
    rw [← hvs, hvw]; push_cast; ring
  rcases he with rfl | rfl
  · refine r8_pi ((w : ℚ_[5]) / s) 3 (Or.inl rfl) ?_
    rw [div_pow]; field_simp
    push_cast at heq ⊢
    linear_combination heq
  · refine r8_pi ((w : ℚ_[5]) / s) (-3) (Or.inr rfl) ?_
    rw [div_pow]; field_simp
    push_cast at heq ⊢
    linear_combination (-1 : ℚ_[5]) * heq

end Remark

section RemarkTwo

local instance fact_prime_two' : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Helper: no $2$-adic number squares to $\pm 5$ (a $2$-adic unit square is $\equiv 1 \pmod 8$). -/
theorem sq_ne_pm_five_two (t : ℚ_[2]) (e : ℤ) (he : e = 5 ∨ e = -5) (ht : t ^ 2 = (e : ℚ_[2])) : False := by
  have hn : ‖t‖ ^ 2 ≤ 1 := by
    rw [← norm_pow, ht]; exact Padic.norm_int_le_one e
  have h1 : ‖t‖ ≤ 1 := by
    by_contra h
    push Not at h
    nlinarith [norm_nonneg t]
  let ti : ℤ_[2] := ⟨t, h1⟩
  have h2 : ti ^ 2 = (e : ℤ_[2]) := by
    apply Subtype.ext
    simpa using ht
  have h3 := congrArg (PadicInt.toZModPow (p := 2) 3) h2
  simp only [map_pow, map_intCast] at h3
  generalize PadicInt.toZModPow (p := 2) 3 ti = r at h3
  rcases he with rfl | rfl
  · revert r; decide
  · revert r; decide

/-- **The obstruction in Cassels' example after Theorem 7.1** (Ch. 10, §7, p. 187): there is no $v \in \mathbb Q^\times$
with $v \in 5(\mathbb Q_2^\times)^2$ (`s` a nonzero $2$-adic number with $v = 5s^2$) and $v \in U_p(\mathbb Q_p^\times)^2$, i.e. of even
$p$-adic valuation, for every prime $p \ne 2$. With `spinorNorm_sec7_example` ($\theta(\sigma_2) = 5(\mathbb Q_2^\times)^2$) this shows
that no $\sigma \in O^+(V)$, $V = (\mathbb Q^3, x_1^2 + x_2^2 - x_3^2)$, has spinor norm in $\theta(\sigma_2)(\mathbb Q_2^\times)^2$ and in
$U_p(\mathbb Q_p^\times)^2$ for all $p \ne 2$, so the analogue of the Corollary to Theorem 7.1 for $O^+(V)$ fails. -/
@[kb "cassels1978" "Ch. 10, §7, p. 187 (the analogue for O⁺(V) is false: no v ∈ ℚ* with v ∈ 5(ℚ₂*)², v ∈ U_p(ℚ_p*)² for p ≠ 2)"]
theorem no_rational_spinor_value_two :
    ¬ ∃ v : ℚ, v ≠ 0 ∧ (∃ s : ℚ_[2], s ≠ 0 ∧ (v : ℚ_[2]) = 5 * s ^ 2) ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → Even (padicValRat p v) := by
  rintro ⟨v, hv, ⟨s, hs, hvs⟩, hp⟩
  have hv2 : Even (padicValRat 2 v) := by
    have h := Padic.valuation_ratCast (p := 2) v
    rw [hvs] at h
    have h5 : (5 : ℚ_[2]) ≠ 0 := by norm_num
    rw [Padic.valuation_mul h5 (pow_ne_zero 2 hs), Padic.valuation_pow] at h
    have h5v : Padic.valuation (5 : ℚ_[2]) = 0 := by
      have : (5 : ℚ_[2]) = ((5 : ℕ) : ℚ_[2]) := by norm_num
      rw [this, Padic.valuation_natCast]
      have : padicValNat 2 5 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
      simp [this]
    rw [h5v] at h
    rw [← h]
    exact ⟨Padic.valuation s, by push_cast; ring⟩
  have hall : ∀ p : ℕ, p.Prime → Even (padicValRat p v) := by
    intro p pp
    by_cases h2 : p = 2
    · subst h2; exact hv2
    · exact hp p pp h2
  have key : ∃ w : ℚ, ∃ e : ℤ, (e = 1 ∨ e = -1) ∧ v = e * w ^ 2 := by
    rcases lt_or_gt_of_ne hv with h | h
    · have hsq : IsSquare (-v) := by
        rw [Rat.isSquare_iff_even_factorization]
        refine ⟨by linarith, fun p pp => ?_⟩
        have : Fact p.Prime := ⟨pp⟩
        rw [padicValRat.neg]; exact hall p pp
      obtain ⟨w, hw⟩ := hsq
      exact ⟨w, -1, Or.inr rfl, by push_cast; linarith [hw, sq w]⟩
    · have hsq : IsSquare v := by
        rw [Rat.isSquare_iff_even_factorization]
        exact ⟨h.le, hall⟩
      obtain ⟨w, hw⟩ := hsq
      exact ⟨w, 1, Or.inl rfl, by push_cast; linarith [hw, sq w]⟩
  obtain ⟨w, e, he, hvw⟩ := key
  have heq : (e : ℚ_[2]) * (w : ℚ_[2]) ^ 2 = 5 * s ^ 2 := by
    rw [← hvs, hvw]; push_cast; ring
  rcases he with rfl | rfl
  · refine sq_ne_pm_five_two ((w : ℚ_[2]) / s) 5 (Or.inl rfl) ?_
    rw [div_pow]; field_simp
    push_cast at heq ⊢
    linear_combination heq
  · refine sq_ne_pm_five_two ((w : ℚ_[2]) / s) (-5) (Or.inr rfl) ?_
    rw [div_pow]; field_simp
    push_cast at heq ⊢
    linear_combination (-1 : ℚ_[2]) * heq

noncomputable local instance invertibleTwoQ2 : Invertible (2 : ℚ_[2]) := invertibleOfNonzero two_ne_zero

/-- Cassels' form $f(\vec x) = x_1^2 + x_2^2 - x_3^2$ of the example on p. 187, over $\mathbb Q_2$ (coordinates
$0, 1, 2$ for Cassels' $x_1, x_2, x_3$). -/
noncomputable def sec7Form : QuadraticForm ℚ_[2] (Fin 3 → ℚ_[2]) :=
  QuadraticMap.weightedSumSquares ℚ_[2] ![(1 : ℚ_[2]), 1, -1]

/-- Helper: the value of `sec7Form`. -/
theorem sec7Form_apply (x : Fin 3 → ℚ_[2]) : sec7Form x = x 0 ^ 2 + x 1 ^ 2 - x 2 ^ 2 := by
  simp [sec7Form, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_three]; ring

/-- **Cassels' example after Theorem 7.1** (Ch. 10, §7, p. 187): for $f = x_1^2 + x_2^2 - x_3^2$ (`sec7Form`),
$\vec a = (1, 0, 0)$, $\vec b = (2, 1, 0)$ we have $f(\vec a) = 1$, $f(\vec b) = 5$, and the rotation
$\sigma_2 = \tau_{\vec a}\tau_{\vec b}$ of $\mathbb Q_2^3$ (`OMeara.symmetry`) has spinor norm $5(\mathbb Q_2^\times)^2$
(`OMeara.HasSpinorNorm`, which determines O'Meara's spinor norm `OMeara.spinorNormHom`). -/
@[kb "cassels1978" "Ch. 10, §7, p. 187 (the example: f = x₁² + x₂² − x₃², σ₂ = τ_a τ_b, θ(σ₂) = 5(ℚ₂*)²)"]
theorem spinorNorm_sec7_example :
    ∃ (ha : sec7Form ![1, 0, 0] ≠ 0) (hb : sec7Form ![2, 1, 0] ≠ 0),
      sec7Form ![1, 0, 0] = 1 ∧ sec7Form ![2, 1, 0] = 5 ∧
      OMeara.HasSpinorNorm sec7Form
        (OMeara.symmetry sec7Form ![1, 0, 0] ha * OMeara.symmetry sec7Form ![2, 1, 0] hb) 5 := by
  have ha1 : sec7Form ![1, 0, 0] = 1 := by rw [sec7Form_apply]; simp
  have hb5 : sec7Form ![2, 1, 0] = 5 := by rw [sec7Form_apply]; simp; norm_num
  have ha : sec7Form ![1, 0, 0] ≠ 0 := by rw [ha1]; exact one_ne_zero
  have hb : sec7Form ![2, 1, 0] ≠ 0 := by rw [hb5]; norm_num
  refine ⟨ha, hb, ha1, hb5, ?_⟩
  have h := OMeara.HasSpinorNorm.mul sec7Form (OMeara.hasSpinorNorm_symmetry sec7Form ha)
    (OMeara.hasSpinorNorm_symmetry sec7Form hb)
  rwa [ha1, hb5, one_mul] at h

end RemarkTwo

end QuadFormsKB.Cassels
