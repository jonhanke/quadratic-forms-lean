/-
# `ThetaSplit` from the cuspidality of $\Theta_Q - \Theta_{\mathrm{Gen}(Q)}$

For a positive definite form $Q$ in $n = 2k$ variables with `GenusFinite`, put
$$c(m) = r_Q(m) - a_E(m), \qquad a_E(m) = \texttt{genusRepAvg}\ Q\ m$$
(`genusCuspCoeff`). Then:

* `thetaSplit_genusCuspCoeff`: `ThetaSplit Q 0 c` (with $a_H = 0$), i.e. $r_Q(m) = a_E(m) + c(m)$ for $m \ge 1$;
* `hasSum_genusCuspCoeff`: $c(m)$ are the Fourier coefficients of the cusp form
  $\Theta_Q - \Theta_{\mathrm{Gen}(Q)} \in S_k(\Gamma_1(N))$ (`thetaGenCusp`), $c(0) = 0$ (`genusCuspCoeff_zero`);
* `exists_thetaSplit_quaternary'` (unconditional) and `exists_thetaSplit_quaternary` ($n = 4$): a level $N$, a cusp form $f \in S_2(\Gamma_1(N))$ with
  $f \mid_2 \gamma = \chi_Q(d) f$ on $\Gamma_0(N)$ and $q$-expansion $\sum_m c(m)e(m\tau)$, and `ThetaSplit Q 0 c`. This is the
  input that (4.8) (`CuspBound`) is to be proved for, from (4.7) and Deligne.

*Siegel's formula:* `ThetaSplit` is stated with the genus average `genusRepAvg`, so Siegel's formula is not needed to
build it; `SiegelFormula` (Hanke (5.3)) then identifies $a_E(m)$ with the local product $\beta_\infty(m)\prod_p\beta_p(m)$
(`repNum_eq_aE_add_genusCuspCoeff`).
-/
import QuadFormsKB.Siegel.ThetaCuspidal
import QuadFormsKB.Siegel.Inputs
import QuadFormsKB.Siegel.GenusFinite

open Complex ModularForm
open scoped MatrixGroups

namespace QuadFormsKB.Siegel

noncomputable section

variable {n : ℕ}

/-- **The cusp-form coefficients** $c(m) = r_Q(m) - a_E(m)$, the Fourier coefficients of
$\Theta_Q - \Theta_{\mathrm{Gen}(Q)}$ (`hasSum_genusCuspCoeff`); Hanke's $a(m)$ in (4.3)/(4.8). -/
@[kb "hanke2004" "(4.3), p. 365; (4.8), p. 367 [unverified]"]
def genusCuspCoeff (Q : QuadForm ℤ n) (m : ℕ) : ℝ := (repNum Q m : ℝ) - genusRepAvg Q m

/-- **`ThetaSplit` with $a_H = 0$** for the coefficients $c(m) = r_Q(m) - a_E(m)$ (any $n$). -/
theorem thetaSplit_genusCuspCoeff (Q : QuadForm ℤ n) : ThetaSplit Q 0 (genusCuspCoeff Q) where
  repNum_eq m _ := by simp [genusCuspCoeff]
  aH_eq_zero _ _ := rfl
  aH_finite_squareClasses := ⟨∅, fun m h => absurd rfl h⟩

/-- $a_E(0) = 1$ (every form in the genus has $r_{Q'}(0) = 1$). -/
theorem genusRepAvg_zero {Q : IntQF n} (hQ : Q.PosDef) (hF : GenusFinite Q) : genusRepAvg Q 0 = 1 := by
  rw [genusRepAvg, genusRepSum, finsum_mem_eq_finite_toFinset_sum _ hF.finite_classes]
  have : ∀ c ∈ hF.finite_classes.toFinset, (c.repNum 0 : ℝ) / c.autCard = ((c.autCard : ℝ))⁻¹ := by
    intro c hc
    rw [QClass.repNum_eq_out,
      repNum_zero ((sameGenus_out_of_mem ((Set.Finite.mem_toFinset _).mp hc)).posDef hQ)]
    simp
  rw [Finset.sum_congr rfl this, ← mass_eq_sum hF, div_self (mass_pos hQ hF).ne']

/-- $c(0) = r_Q(0) - a_E(0) = 0$. -/
theorem genusCuspCoeff_zero {Q : IntQF n} (hQ : Q.PosDef) (hF : GenusFinite Q) : genusCuspCoeff Q 0 = 0 := by
  rw [genusCuspCoeff, Nat.cast_zero, genusRepAvg_zero hQ hF, repNum_zero hQ]; simp

/-- **The $q$-expansion of $\Theta_Q - \Theta_{\mathrm{Gen}(Q)}$:** $\sum_{m \ge 0}c(m)e(m\tau)$, $c$ = `genusCuspCoeff`. -/
@[kb "hanke2004" "(4.3), p. 365 [unverified]"]
theorem hasSum_genusCuspCoeff {Q : IntQF n} (hQ : Q.PosDef) (hF : GenusFinite Q) {k : ℕ} (hn : n = 2 * k)
    {N : ℕ} (hN0 : 0 < N) (hN : ∀ Q', SameGenus Q Q' → IsThetaLevel Q' N) (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ => (genusCuspCoeff Q m : ℂ) * cexp (2 * Real.pi * I * τ * m))
      (thetaGenCusp hQ hF hn hN0 hN τ) := by
  rw [thetaGenCusp_apply]
  refine ((hasSum_theta hQ τ.im_pos).sub (hasSum_thetaGen hQ hF τ.im_pos)).congr_fun fun m => ?_
  simp only [genusCuspCoeff]; push_cast; ring

/-- **Under Siegel's formula** (`SiegelFormula`, $n \ge 4$): $r_Q(m) = a_E(m) + c(m)$ with $a_E(m) = \beta_\infty(m)\prod_p\beta_p(m)$
the local product (`aE`) and $c(m)$ the coefficients of the cusp form $\Theta_Q - \Theta_{\mathrm{Gen}(Q)}$. -/
theorem repNum_eq_aE_add_genusCuspCoeff {Q : QuadForm ℤ n} (hS : SiegelFormula Q) {m : ℕ} (hm : 1 ≤ m) :
    (repNum Q m : ℝ) = aE Q m + genusCuspCoeff Q m := by
  rw [genusCuspCoeff, ← hS.genusRepAvg_eq m (by exact_mod_cast hm)]; ring

/-- **The theta decomposition for quaternary forms** (Hanke 2004, (4.3), $n = 4$, $k = 2$): for $Q$ positive definite with
`GenusFinite`, there is a level $N \ge 1$ of the whole genus and a cusp form $f \in S_2(\Gamma_1(N))$ such that
* $f \mid_2 \gamma = \chi_Q(d)\,f$ for $\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \Gamma_0(N)$ ($f \in S_2(\Gamma_0(N), \chi_Q)$);
* $f(\tau) = \sum_{m \ge 0}c(m)e(m\tau)$ with $c$ = `genusCuspCoeff` ($f = \Theta_Q - \Theta_{\mathrm{Gen}(Q)}$);
* `ThetaSplit Q 0 c`: $r_Q(m) = a_E(m) + c(m)$ for $m \ge 1$. -/
@[kb "hanke2004" "(4.3), (4.5), pp. 365–366 (n = 4) [unverified]"]
theorem exists_thetaSplit_quaternary {Q : IntQF 4} (hQ : Q.PosDef) (hF : GenusFinite Q) :
    ∃ N : ℕ, 0 < N ∧ ∃ f : CuspForm (CongruenceSubgroup.Gamma1 N) 2,
      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
        ⇑f ∣[(2 : ℤ)] γ = (thetaChi Q 2 N (γ 1 1) : ℂ) • ⇑f) ∧
      (∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => (genusCuspCoeff Q m : ℂ) * cexp (2 * Real.pi * I * τ * m))
        (f τ)) ∧
      ThetaSplit Q 0 (genusCuspCoeff Q) := by
  obtain ⟨N, hN0, hN⟩ := exists_isThetaLevel_genus hQ hF
  exact ⟨N, hN0, thetaGenCusp hQ hF (k := 2) rfl hN0 hN,
    fun γ hγ => thetaGenCusp_slash_gamma0 hQ hF rfl hN0 hN hγ,
    hasSum_genusCuspCoeff hQ hF rfl hN0 hN, thetaSplit_genusCuspCoeff Q⟩

/-- **The theta decomposition for quaternary forms, unconditionally** (Hanke 2004, (4.3), $n = 4$, $k = 2$): the same as
`exists_thetaSplit_quaternary`, with finiteness of the genus discharged by `genusFinite`, so the only
hypothesis is that $Q$ is positive definite. -/
@[kb "hanke2004" "(4.3), (4.5), pp. 365–366 (n = 4) [unverified]"]
theorem exists_thetaSplit_quaternary' {Q : IntQF 4} (hQ : Q.PosDef) :
    ∃ N : ℕ, 0 < N ∧ ∃ f : CuspForm (CongruenceSubgroup.Gamma1 N) 2,
      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
        ⇑f ∣[(2 : ℤ)] γ = (thetaChi Q 2 N (γ 1 1) : ℂ) • ⇑f) ∧
      (∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => (genusCuspCoeff Q m : ℂ) * cexp (2 * Real.pi * I * τ * m))
        (f τ)) ∧
      ThetaSplit Q 0 (genusCuspCoeff Q) :=
  exists_thetaSplit_quaternary hQ (genusFinite hQ)

end

end QuadFormsKB.Siegel
