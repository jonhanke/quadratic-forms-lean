/-
# Moreno–Wagstaff 2005, Theorem 6.1 (Hardy): $r_s(n) = \rho_s(n)$ for $5 \le s \le 8$, $r_s(n) = \rho_s(n) + O(n^{s/4})$

**Source.** C. J. Moreno and S. S. Wagstaff Jr., *Sums of Squares of Integers* (2005), Theorem 6.1, p. 189
(printed page). Notation: $r_s(n)$ = `Siegel.repNum (Siegel.sumSq s) n`, $\rho_s(n)$ = `singularSeriesSq s n`
(the book's (6.17)).

**Proved here (unconditional).**
* `betaInf_sumSq`: the archimedean density of $x_0^2 + \dots + x_{s-1}^2$ is
  $\beta_\infty(m) = \pi^{s/2} m^{s/2-1}/\Gamma(s/2)$, the factor in front of the series in (6.17).
* `singularSeriesSq_eq_aE`: for $s \ge 5$ and $n \ge 1$, $\rho_s(n) = a_E(n) = \beta_\infty(n)\prod_p\beta_p(n)$ (Siegel's
  local product), from the absolute convergence of $\sum_m A_m(n)$ (`summable_ssTerm_sumSq`, file
  `SingularSeriesBound.lean`) and the Euler product of the singular series (`SingularSeries.hasSum_ssTerm`).
* `theorem61_small`: **$r_s(n) = \rho_s(n)$ for $s = 5, 6, 7, 8$ and $n \ge 1$** (first half of Theorem 6.1). The proof is
  not Hardy's (modular forms on the theta group): Siegel's formula (`siegelFormula_of_posDef`, a theorem of this library)
  gives $\rho_s(n) = a_E(n)$, the genus average, and the genus of $x_0^2 + \dots + x_{s-1}^2$ has one class for $s \le 8$
  (`genusClasses_sumSq_of_le_eight`), so the genus average is $r_s(n)$.
* `theorem61_even`: for **even** $s > 8$, $|r_s(n) - \rho_s(n)| \le C n^{s/4}$ (second half of Theorem 6.1 for even $s$):
  $r_s(n) - a_E(n)$ is the coefficient of the cusp form $\Theta_Q - \Theta_{\mathrm{Gen}(Q)}$ of weight $s/2$, bounded by
  Hecke's estimate (`exists_abs_genusCuspCoeff_le`).

* `theorem61_large`: for **every** $s \ge 5$, $|r_s(n) - \rho_s(n)| \le C n^{s/4}$, from Hecke's bound in every rank
  (`exists_abs_genusCuspCoeff_le_rpow`, file `OddHecke.lean`: for odd $s$ the half-integral weight cusp form is bounded
  through its square, a combination of integral weight cusp forms of rank $2s$).
* `theorem61`: **Theorem 6.1 in full** (`Theorem61`), unconditional.

`theorem61_iff_odd` (the reduction to odd $s > 8$, written before `theorem61_large`) is kept for reference.
-/
import QuadFormsKB.Literature.MorenoWagstaff.Wave2.SingularSeriesBound
import QuadFormsKB.Literature.Cassels.AppB.SumSquaresGenus
import QuadFormsKB.Tamagawa.SiegelFormulaConsumers
import QuadFormsKB.Literature.MorenoWagstaff.Wave2.OddHecke

namespace QuadFormsKB.MorenoWagstaff

open QuadFormsKB.Siegel

/-- **The archimedean density of a sum of $s$ squares** ($s \ge 1$, $m \ge 0$):
$\beta_\infty(m) = \dfrac{\pi^{s/2}}{\Gamma(s/2)}\, m^{s/2 - 1}$ (Moreno–Wagstaff (6.17), the factor in front of the
singular series). -/
theorem betaInf_sumSq {s : ℕ} (hs : 1 ≤ s) (m : ℝ) :
    betaInf (sumSq s) m = m ^ ((s : ℝ) / 2 - 1) * Real.pi ^ ((s : ℝ) / 2) / Real.Gamma ((s : ℝ) / 2) := by
  rw [betaInf, gramDet_sumSq, unitBallVol_eq hs, Real.one_rpow, mul_one]
  have hG : Real.Gamma ((s : ℝ) / 2 + 1) = (s : ℝ) / 2 * Real.Gamma ((s : ℝ) / 2) :=
    Real.Gamma_add_one (by positivity)
  have hGpos : 0 < Real.Gamma ((s : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hsq : Real.sqrt Real.pi ^ s = Real.pi ^ ((s : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    ring_nf
  have he : ((s : ℝ) - 2) / 2 = (s : ℝ) / 2 - 1 := by ring
  rw [hG, hsq, he]
  have hs0 : (s : ℝ) ≠ 0 := by positivity
  field_simp

/-- **$\rho_s(n)$ is Siegel's local product** ($s \ge 5$, $n \ge 1$):
$\rho_s(n) = a_E(n) = \beta_\infty(n)\prod_p \beta_p(n)$ for $Q = x_0^2 + \dots + x_{s-1}^2$. -/
theorem singularSeriesSq_eq_aE {s : ℕ} (hs : 5 ≤ s) {n : ℕ} (hn : 1 ≤ n) :
    singularSeriesSq s n = ((aE (sumSq s) n : ℝ) : ℂ) := by
  have hQ : (sumSq s).Nondegenerate := posDef_sumSq.nondegenerate
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hsum := SingularSeries.hasSum_ssTerm hQ (by omega) hn0 (summable_ssTerm_sumSq hs n)
  rw [singularSeriesSq, hsum.tsum_eq, aE, aEWith, betaInf_sumSq (by omega)]
  push_cast
  ring

/-- **Moreno–Wagstaff, Theorem 6.1, first half** (Hardy; p. 189): $r_s(n) = \rho_s(n)$ for $s = 5, 6, 7, 8$ and every
$n \ge 1$. Unconditional (Siegel's formula and class number one for $s \le 8$; see the file header). -/
@[kb "morenowagstaff2005" "Theorem 6.1 (s = 5, 6, 7, 8), p. 189"]
theorem theorem61_small {s n : ℕ} (hs5 : 5 ≤ s) (hs8 : s ≤ 8) (hn : 0 < n) :
    (repNum (sumSq s) n : ℂ) = singularSeriesSq s n := by
  rw [singularSeriesSq_eq_aE hs5 hn]
  have hSF := siegelFormula_of_posDef (sumSq s) posDef_sumSq (by omega)
  rw [← hSF.genusRepAvg_eq n (by exact_mod_cast hn), genusRepAvg_sumSq_of_le_eight hs8]
  simp

/-- **Moreno–Wagstaff, Theorem 6.1, second half for even $s$** (p. 189): for even $s > 8$ there is $C$ with
$|r_s(n) - \rho_s(n)| \le C n^{s/4}$ for all $n \ge 1$. Unconditional (Siegel's formula and Hecke's bound). -/
@[kb "morenowagstaff2005" "Theorem 6.1 (s > 8 even), p. 189"]
theorem theorem61_even {s : ℕ} (hs : 8 < s) (he : Even s) : ∃ C : ℝ, ∀ n : ℕ, 0 < n →
    ‖(repNum (sumSq s) n : ℂ) - singularSeriesSq s n‖ ≤ C * (n : ℝ) ^ ((s : ℝ) / 4) := by
  obtain ⟨k, hk⟩ := he
  obtain ⟨C, -, hC⟩ := exists_abs_genusCuspCoeff_le (posDef_sumSq (n := s)) (k := k) (by omega)
  refine ⟨C, fun n hn => ?_⟩
  have hSF := siegelFormula_of_posDef (sumSq s) posDef_sumSq (by omega)
  rw [singularSeriesSq_eq_aE (by omega) hn, ← hSF.genusRepAvg_eq n (by exact_mod_cast hn)]
  have h := hC n hn
  rw [genusCuspCoeff] at h
  have hk' : (s : ℝ) / 4 = (k : ℝ) / 2 := by rw [hk]; push_cast; ring
  rw [hk']
  have : (repNum (sumSq s) (n : ℤ) : ℂ) - ((genusRepAvg (sumSq s) n : ℝ) : ℂ) =
      (((repNum (sumSq s) (n : ℤ) : ℝ) - genusRepAvg (sumSq s) n : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs]
  exact h

/-- **Moreno–Wagstaff, Theorem 6.1, second half for every $s \ge 5$** (p. 189): there is $C$ with
$|r_s(n) - \rho_s(n)| \le C n^{s/4}$ for all $n \ge 1$. Unconditional: Siegel's formula and Hecke's bound in every rank
(`exists_abs_genusCuspCoeff_le_rpow`, file `OddHecke.lean`; for odd $s$ through the square of the half-integral weight
cusp form). -/
@[kb "morenowagstaff2005" "Theorem 6.1 (s > 8), p. 189"]
theorem theorem61_large {s : ℕ} (hs : 5 ≤ s) : ∃ C : ℝ, ∀ n : ℕ, 0 < n →
    ‖(repNum (sumSq s) n : ℂ) - singularSeriesSq s n‖ ≤ C * (n : ℝ) ^ ((s : ℝ) / 4) := by
  obtain ⟨C, -, hC⟩ := exists_abs_genusCuspCoeff_le_rpow (posDef_sumSq (n := s)) (by omega)
  refine ⟨C, fun n hn => ?_⟩
  have hSF := siegelFormula_of_posDef (sumSq s) posDef_sumSq (by omega)
  rw [singularSeriesSq_eq_aE hs hn, ← hSF.genusRepAvg_eq n (by exact_mod_cast hn)]
  have h := hC n hn
  rw [genusCuspCoeff] at h
  have : (repNum (sumSq s) (n : ℤ) : ℂ) - ((genusRepAvg (sumSq s) n : ℝ) : ℂ) =
      (((repNum (sumSq s) (n : ℤ) : ℝ) - genusRepAvg (sumSq s) n : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs]
  exact h

/-- **Moreno–Wagstaff, Theorem 6.1** (Hardy; p. 189), both halves. Unconditional. -/
@[kb "morenowagstaff2005" "Theorem 6.1, p. 189"]
theorem theorem61 : Theorem61 :=
  ⟨fun _ _ h5 h8 hn => theorem61_small h5 h8 hn, fun _ hs => theorem61_large (by omega)⟩

/-- **What remains of Theorem 6.1:** `Theorem61` holds if and only if its second half holds for odd $s > 8$. -/
theorem theorem61_iff_odd : Theorem61 ↔ ∀ s : ℕ, 8 < s → Odd s → ∃ C : ℝ, ∀ n : ℕ, 0 < n →
    ‖(repNum (sumSq s) n : ℂ) - singularSeriesSq s n‖ ≤ C * (n : ℝ) ^ ((s : ℝ) / 4) := by
  constructor
  · exact fun h s hs _ => h.2 s hs
  · intro h
    refine ⟨fun s n h5 h8 hn => theorem61_small h5 h8 hn, fun s hs => ?_⟩
    rcases Nat.even_or_odd s with he | ho
    · exact theorem61_even hs he
    · exact h s hs ho

end QuadFormsKB.MorenoWagstaff
