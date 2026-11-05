/-
# The typographical error in Cassels's (4.19), quoted in the proof of Hanke's Theorem 2.1

**Layer:** real arithmetic (the step of Cassels's argument, not the measure theory behind it, which is
`theorem21` / `Indefinite.covolume_eq_muFin_mul_tsum_unitVolume`).

Hanke's proof of Theorem 2.1 (thesis, p. 6) cites Cassels 1978, Ch. 9 (4.11)–(4.19), pp. 380–382, and notes that "due to
a typographical error" the right side of (4.19) on p. 382 should read $2\lambda_\infty^{-1}\prod_{p\ne\infty}\lambda_p^{-1}$.
Checked against Cassels's page: Cassels has, for the classes $\Lambda_j$ of a genus,
$$\textstyle\sum_j\sigma_j = 2\prod_{p\ne\infty}\lambda_p^{-1}\ \ (4.17),\qquad \sigma_j = \lambda_\infty/o^+(\Lambda_j)\ \ (4.18),$$
and prints $W = \sum_j 1/o^+(\Lambda_j) = 2\lambda_\infty\prod_{p\ne\infty}\lambda_p$ as (4.19). From (4.17)–(4.18) the
right side is $2\lambda_\infty^{-1}\prod_p\lambda_p^{-1}$: Hanke's correction is right.

**Proves**
* `cassels_4_19_corrected`: (4.17) and (4.18) imply $\sum_j1/o_j = 2\lambda_\infty^{-1}P^{-1}$, $P = \prod_p\lambda_p$.
* `cassels_4_19_printed_false`: (4.17) and (4.18) do not imply the printed $\sum_j1/o_j = 2\lambda_\infty P$ (one class,
  $o = 1$, $\lambda_\infty = 2$, $P = 1$).
-/
import Mathlib
import QuadFormsKB.Citation

namespace QuadFormsKB.Hanke2005

/-- **Cassels's (4.19), corrected** (Hanke thesis, proof of Theorem 2.1, p. 6; Cassels 1978, Ch. 9, (4.17)–(4.19),
p. 382). For finitely many classes $j\in\iota$ with $o_j = o^+(\Lambda_j) > 0$ (`ho`), $\lambda_\infty > 0$ (`hl`), the
fundamental-domain volumes $\sigma_j = \lambda_\infty/o_j$ ((4.18), `h418`) and $\sum_j\sigma_j = 2P^{-1}$ ((4.17), `h417`,
$P = \prod_{p\ne\infty}\lambda_p$):
$$\sum_j\frac1{o_j} = 2\lambda_\infty^{-1}P^{-1}.$$ -/
@[kb "hanke2005crelle" "proof of Theorem 2.1, p. 6 (correction of Cassels (4.19), p. 382)"]
theorem cassels_4_19_corrected {ι : Type*} [Fintype ι] (o σ : ι → ℝ) (lamInf P : ℝ) (hl : 0 < lamInf)
    (h418 : ∀ j, σ j = lamInf / o j) (h417 : ∑ j, σ j = 2 * P⁻¹) :
    ∑ j, 1 / o j = 2 * lamInf⁻¹ * P⁻¹ := by
  have h : ∑ j, σ j = lamInf * ∑ j, 1 / o j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by rw [h418]; ring
  rw [h] at h417
  rw [show 2 * lamInf⁻¹ * P⁻¹ = lamInf⁻¹ * (2 * P⁻¹) by ring, ← h417, inv_mul_cancel_left₀ hl.ne']

/-- **Cassels's (4.19) as printed does not follow from (4.17)–(4.18)**: with one class, $o = 1$, $\lambda_\infty = 2$,
$P = 1$, $\sigma = 2$, (4.17) and (4.18) hold but $\sum_j1/o_j = 1\ne4 = 2\lambda_\infty P$. -/
@[kb "cassels1978" "Ch. 9, (4.19), p. 382 (typographical error, noted in hanke2005crelle, p. 6)"]
theorem cassels_4_19_printed_false :
    ∃ (o σ : Unit → ℝ) (lamInf P : ℝ), 0 < lamInf ∧ (∀ j, 0 < o j) ∧ (∀ j, σ j = lamInf / o j) ∧
      ∑ j, σ j = 2 * P⁻¹ ∧ ∑ j, 1 / o j ≠ 2 * lamInf * P := by
  refine ⟨fun _ => 1, fun _ => 2, 2, 1, by norm_num, fun _ => by norm_num, fun _ => by norm_num, by simp, ?_⟩
  simp; norm_num

end QuadFormsKB.Hanke2005
