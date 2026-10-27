/-
# The $T(p^2)$-type relation for $a_E$ at good primes

For $Q$ positive definite quaternary, $p$ an odd prime with $p \nmid \det H$, $\varepsilon = \left(\frac{\det H}{p}\right)$ and
$m \ge 1$ with $p \nmid m$:
$$a_E(p^2m) = (p^2 + 1 + \varepsilon p)\,a_E(m)$$
(`aE_prime_sq_mul`). This is the same eigenvalue as in the neighbour relation for $r_{\mathrm{Gen}}$
(`genusRepAvg_neighbor_four` with $p \nmid m$), so $c = r_{\mathrm{Gen}} - a_E$ satisfies $c(p^2m) = (p^2+1+\varepsilon p)c(m)$.

*Proof.* `aE_mul_sq` with $S = \{p\}$, $\nu_p = 1$: $a_E(p^2m) = a_E(m)\,p^2\beta_p(p^2m)/\beta_p(m)$. At a good prime,
$\beta_p(m) = 1 - \varepsilon p^{-2}$ ($p \nmid m$, Table 1) and $\beta_p(p^2m) = p^{-2}\beta_p(m) + (1 - \varepsilon p^{-2})(1 + \varepsilon p^{-1})$
(the Zero/non-Zero type recursion, `localDensityOf_nonZero_eq`, with the non-Zero part computed on a diagonal model
as in `localDensity_good_four_ge`), so $p^2\beta_p(p^2m)/\beta_p(m) = 1 + p^2 + \varepsilon p$.
-/
import QuadFormsKB.Siegel.GlobalLowerBound

namespace QuadFormsKB.Siegel

open LocalDensity

/-- **Local densities at a good prime, $n = 4$, $p \nmid T$:** $\beta_p(T) = 1 - \varepsilon/p^2$ and
$\beta_p(p^2T) = p^{-2}\beta_p(T) + (1 - \varepsilon/p^2)(1 + \varepsilon/p)$, $\varepsilon = \left(\frac{\det H}{p}\right)$. -/
theorem localDensity_good_four_sq (Q : QuadForm ℤ 4) (hQ : Q.Nondegenerate) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) (T : ℤ) (hpT : ¬ (p : ℤ) ∣ T) :
    localDensity Q p T = 1 - (legendreSym p Q.hessian.det : ℝ) / (p : ℝ) ^ 2 ∧
      localDensity Q p ((p : ℤ) ^ 2 * T) = ((p : ℝ) ^ 2)⁻¹ * localDensity Q p T +
        (1 - (legendreSym p Q.hessian.det : ℝ) / (p : ℝ) ^ 2) *
          (1 + (legendreSym p Q.hessian.det : ℝ) / p) := by
  have hpp : p.Prime := Fact.out
  obtain ⟨a, ha, hcnt, u, hu, hprod⟩ := exists_diag_unimodular_same_counts_det Q p hp hdet
  have hχ : legendreSym p Q.hessian.det = legendreSym p (∏ i, a i) := by
    have := legendreSym_prod_eq_even Q (by decide) p hp a hu hprod 0
    rw [pow_zero, one_mul, one_mul] at this
    exact this.symm
  have hpp2 : ¬ (p : ℤ) ^ 2 ∣ (p : ℤ) := by
    intro h
    have h' : p ^ 2 ∣ p := by exact_mod_cast h
    have := Nat.le_of_dvd hpp.pos h'
    nlinarith [hpp.two_le]
  have hV : localDensity (QuadForm.diag a) p p =
      (1 - (legendreSym p (∏ i, a i) : ℝ) / (p : ℝ) ^ 2) * (1 + (legendreSym p (∏ i, a i) : ℝ) / p) := by
    have := localDensity_diag_even_ord_one a p hp ha (by norm_num) (by decide) (p : ℤ) dvd_rfl hpp2
    rw [this]; norm_num
  have hT0 : T ≠ 0 := by rintro rfl; exact hpT (dvd_zero _)
  have h1 : localDensity Q p T = 1 - (legendreSym p Q.hessian.det : ℝ) / (p : ℝ) ^ 2 := by
    rw [(localDensity_congr_of_repCount Q _ p hcnt T).1,
      localDensity_diag_even_unit a p hp ha (by norm_num) (by decide) T hpT, hχ]
    norm_num
  refine ⟨h1, ?_⟩
  have hK := localDensityOf_nonZero_eq Q hQ p (by norm_num) T hT0
  have hp1 : padicValInt p (p : ℤ) = 1 := by simp [padicValInt, padicValNat_self]
  rw [(localDensity_congr_of_repCount Q _ p hcnt T).2.1,
    localDensityOf_nonZero_diag_sq a p hp ha T,
    ← localDensity_diag_ord_one a p hp ha _ hp1, hV, ← hχ] at hK
  norm_num at hK
  linarith

/-- **$a_E(p^2m) = (p^2 + 1 + \varepsilon p)\,a_E(m)$** at a good prime $p \nmid m$, $\varepsilon = \left(\frac{\det H}{p}\right)$. -/
@[kb "hanke2004" "Table 1, p. 363; (5.8), p. 369 (T(p²) relation for a_E at good p)"]
theorem aE_prime_sq_mul {Q : QuadForm ℤ 4} (hQ : IntQF.PosDef Q) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) {m : ℤ} (hm : 0 < m) (hpm : ¬ (p : ℤ) ∣ m) :
    aE Q ((p : ℤ) ^ 2 * m) = ((p : ℝ) ^ 2 + 1 + (legendreSym p Q.hessian.det : ℝ) * p) * aE Q m := by
  have hpp : p.Prime := Fact.out
  have hnd := hQ.nondegenerate
  obtain ⟨hβ, hβ2⟩ := localDensity_good_four_sq Q hnd p hp2 hdet m hpm
  set ε : ℝ := (legendreSym p Q.hessian.det : ℝ) with hε
  have hε2 : ε ^ 2 = 1 := by
    rcases legendreSym.eq_one_or_neg_one p (a := Q.hessian.det)
      (by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]) with h | h <;> simp [hε, h]
  have hp0 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
  have hβne : localDensity Q p m ≠ 0 := by
    rw [hβ]
    intro h
    have : ε = (p : ℝ) ^ 2 := by
      field_simp at h; linarith
    have hε1 : |ε| = 1 := by
      have := sq_abs ε; rw [hε2] at this
      nlinarith [abs_nonneg ε, sq_nonneg (|ε| - 1)]
    rw [this, abs_of_nonneg (by positivity)] at hε1
    nlinarith
  have hS : ∀ q ∈ ({p} : Finset ℕ), q.Prime := by simp [hpp]
  have h := aE_mul_sq Q hnd (by norm_num) hS (fun _ => 1) hm (by simpa using hβne)
  have hsq : sqPart ({p} : Finset ℕ) (fun _ => 1) = (p : ℤ) := by simp [sqPart]
  rw [hsq, mul_comm m] at h
  rw [h, Finset.prod_singleton, sqShiftFactor, hβ2]
  simp only [show (4 - 2) * 1 = 2 by norm_num]
  rw [mul_comm (aE Q m)]
  congr 1
  have hpne : (p : ℝ) ≠ 0 := by positivity
  rw [hβ] at hβne ⊢
  have hne : (p : ℝ) ^ 2 - ε ≠ 0 := by
    intro h0; apply hβne; field_simp; linarith
  field_simp
  ring

end QuadFormsKB.Siegel
