/-
# Cassels, Chapter 6, §1: Meyer's theorem

**Setting.** A rational quadratic form is `Q : RatQF n` (the polynomial $\sum_{i \le j} c_{ij}x_ix_j$), regular means
`Q.Nondegenerate`, and isotropy over a field $K \supseteq \mathbb Q$ is `Q.IsotropicIn K`. Cassels calls a real form
*indefinite* when it takes both signs; for a regular form this is isotropy over $\mathbb R$ (`isotropic_real_of_indefinite`).

**Proves** (Cassels, *Rational Quadratic Forms*, Chapter 6)
* Corollary 1 to Theorem 1.1 (Meyer's theorem): `meyer` (indefinite in the sense of taking both signs) and
  `meyer_of_isotropic_real` (isotropic over $\mathbb R$, the form of the hypothesis Cassels' proof uses).

**Proof notes.** As Cassels': the form is isotropic over $\mathbb R$ by hypothesis and over every $\mathbb Q_p$ by
Ch. 4, Lemma 2.7 (`isotropic_padic_of_five_le`), so over $\mathbb Q$ by the Strong Hasse Principle (`hasseMinkowski`).
-/
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowski

namespace QuadFormsKB.Cassels.Ch6

variable {n : ℕ}

/-- A real form taking both signs is isotropic over $\mathbb R$ (intermediate values on the segment between a point
where it is positive and one where it is negative; the segment avoids $\vec 0$ since $Q(-c\vec x) = c^2Q(\vec x)$). -/
theorem isotropic_real_of_indefinite (Q : RatQF n) (hpos : ∃ x : Fin n → ℝ, 0 < Q.evalIn ℝ x)
    (hneg : ∃ y : Fin n → ℝ, Q.evalIn ℝ y < 0) : Q.IsotropicIn ℝ := by
  obtain ⟨x, hx⟩ := hpos
  obtain ⟨y, hy⟩ := hneg
  have hsmul : ∀ (c : ℝ) (z : Fin n → ℝ), Q.evalIn ℝ (c • z) = c ^ 2 * Q.evalIn ℝ z := by
    intro c z
    simp only [QuadForm.evalIn, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  set f : ℝ → ℝ := fun t => Q.evalIn ℝ (t • x + (1 - t) • y) with hf
  have hcont : Continuous f := by
    simp only [hf, QuadForm.evalIn]
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    split_ifs
    · fun_prop
    · exact continuous_const
  have h0 : f 0 < 0 := by simpa [hf] using hy
  have h1 : 0 < f 1 := by simpa [hf] using hx
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc (zero_le_one' ℝ) hcont.continuousOn ⟨h0.le, h1.le⟩
  refine ⟨t • x + (1 - t) • y, fun hz => ?_, hft⟩
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp only [zero_smul, sub_zero, one_smul, zero_add] at hz
    rw [hz] at hy; simp [QuadForm.evalIn] at hy
  have hxe : x = (-(1 - t) / t) • y := by
    have : t • x = -((1 - t) • y) := eq_neg_of_add_eq_zero_left hz
    rw [div_eq_inv_mul, mul_smul, neg_smul, ← this, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  rw [hxe, hsmul] at hx
  nlinarith [sq_nonneg (-(1 - t) / t)]

/-- **Cassels, Ch. 6, Corollary 1 to Theorem 1.1** (Meyer's theorem), with the hypothesis as used in the proof:
*a regular rational form in $n \ge 5$ variables which is isotropic over $\mathbb Q_\infty = \mathbb R$ is isotropic
over $\mathbb Q$.* -/
@[kb "cassels1978" "Ch. 6, Cor. 1 to Thm. 1.1, p. 75 (indefinite as isotropic over ℝ)"]
theorem meyer_of_isotropic_real (Q : RatQF n) (hn : 5 ≤ n) (hQ : Q.Nondegenerate) (hR : Q.IsotropicIn ℝ) :
    Q.IsotropicIn ℚ := by
  refine (hasseMinkowski Q hQ).2 fun v => ?_
  cases v with
  | infinite => exact hR
  | finite p =>
    have : Fact p.1.Prime := ⟨p.2⟩
    exact isotropic_padic_of_five_le p.1 Q hn hQ

/-- **Cassels, Ch. 6, Corollary 1 to Theorem 1.1** (Meyer's theorem): *an indefinite regular form $f$ in $n \ge 5$
variables is isotropic* (over $\mathbb Q$). Indefinite: $f$ takes a positive and a negative value at real points. -/
@[kb "cassels1978" "Ch. 6, Cor. 1 to Thm. 1.1, p. 75"]
theorem meyer (Q : RatQF n) (hn : 5 ≤ n) (hQ : Q.Nondegenerate) (hpos : ∃ x : Fin n → ℝ, 0 < Q.evalIn ℝ x)
    (hneg : ∃ y : Fin n → ℝ, Q.evalIn ℝ y < 0) : Q.IsotropicIn ℚ :=
  meyer_of_isotropic_real Q hn hQ (isotropic_real_of_indefinite Q hpos hneg)

end QuadFormsKB.Cassels.Ch6
