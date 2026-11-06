/-
# Hanke 2011, Remark 4.14 at the dyadic primes: the generic density is constant for $n$ odd

Setting: $R$ a Henselian discrete valuation ring with finite residue field, $2 \ne 0$ a non-unit of $R$ (e.g. the integers
of the completion of a number field at a prime over $2$), $\pi$ a uniformizer. Forms are `QuadForm R n` in $n$ variables
$x_0, \dots, x_{n-1}$ (0-based); $\det_H$ is the determinant of the Hessian matrix, and a form is *normalized*
(`IsNormalizedHessian`) when $\operatorname{ord}\det_H$ is $0$ ($n$ even) or $\operatorname{ord} 2$ ($n$ odd).

**Proves** (Hanke 2011, Rem. 4.14, p. 20, the statement at the dyadic primes): for $n = 2r + 1$ odd, any two normalized forms
$Q, Q'$ have the same local self-density $\beta_\pi(Q, Q) = \beta_\pi(Q', Q')$; so the generic density
$\beta_{n,\mathfrak p}(\widetilde S_\mathfrak p)$, the density of the unique normalized local genus with $\det_H = \widetilde S_\mathfrak p$
(Thm. 2.6), does not depend on $\widetilde S_\mathfrak p$ (`remark_4_14_dyadic`). The paper quotes this from Gan–Hanke–Yu; here it
is proved from Sublemmas 2.8/2.9 (`uniqueNormalizedLocalGenus_odd`) and the invariance of the self-density under scaling by a
unit (`Tamagawa.localDensityForm_smul`): if $\det_H Q' = \varepsilon \det_H Q$ with $\varepsilon$ a unit, then
$\det_H(\varepsilon Q) = (\varepsilon^r)^2 \det_H Q'$, so $\varepsilon Q \cong Q'$, and
$\beta_\pi(\varepsilon Q, \varepsilon Q) = \beta_\pi(Q, Q)$. The value of the constant (Gan–Hanke–Yu) is not formalized.
-/
import QuadFormsKB.Literature.Hanke2011Structure.DyadicOdd
import QuadFormsKB.Literature.Hanke2011Structure.GenericDensity
import QuadFormsKB.Tamagawa.AlphaLawMoves

open IsLocalRing QuadFormsKB.LocalDensity

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Hanke2011Structure.Dyadic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)]

/-- A normalized form in an odd number of variables has $\det_H = 2w$ with $w$ a unit. -/
theorem exists_det_eq_two_mul_of_normalized {n : ℕ} (hn : Odd n) (Q : QuadForm R n)
    (hN : IsNormalizedHessian R Q) : ∃ w : R, IsUnit w ∧ Q.hessian.det = 2 * w := by
  have hnev : ¬ Even n := Nat.not_even_iff_odd.2 hn
  simp only [IsNormalizedHessian, hnev, ite_false] at hN
  obtain ⟨v, hv⟩ := (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).1 hN
  refine ⟨((v⁻¹ : Rˣ) : R), (v⁻¹).isUnit, ?_⟩
  calc Q.hessian.det = Q.hessian.det * (v * ((v⁻¹ : Rˣ) : R)) := by simp
    _ = (Q.hessian.det * v) * ((v⁻¹ : Rˣ) : R) := by ring
    _ = 2 * ((v⁻¹ : Rˣ) : R) := by rw [hv]

/-- $\det_H$ of a scaled form: the Hessian matrix of $cQ$ is $c$ times that of $Q$. -/
theorem hessian_smul' {n : ℕ} (c : R) (S : QuadForm R n) : (c • S).hessian = c • S.hessian := by
  ext a b; simp [QuadForm.hessian, mul_add]

/-- **Remark 4.14 at the dyadic primes** (Hanke 2011, p. 20; for $n$ odd): any two normalized forms $Q, Q'$ in $n = 2r+1$
variables over $R$ ($2$ a nonzero non-unit) have the same local self-density, $\beta_\pi(Q, Q) = \beta_\pi(Q', Q')$. Hence the
generic local density $\beta_{n,\mathfrak p}(\widetilde S_\mathfrak p)$ does not depend on the normalized squareclass
$\widetilde S_\mathfrak p$ (the paper: "constant in $\widetilde S$ for $n$ odd", quoting Gan–Hanke–Yu for the dyadic primes). -/
@[kb "hanke2011structure" "Rem. 4.14, p. 20 (p | 2, n odd: the generic density does not depend on the squareclass)"]
theorem remark_4_14_dyadic (h2 : ¬ IsUnit (2 : R)) (h20 : (2 : R) ≠ 0) {π : R} (hπ : Irreducible π) (r : ℕ)
    (Q Q' : QuadForm R (2 * r + 1)) (hN : IsNormalizedHessian R Q) (hN' : IsNormalizedHessian R Q') :
    DVR.localDensityForm Q Q π = DVR.localDensityForm Q' Q' π := by
  have hodd : Odd (2 * r + 1) := ⟨r, rfl⟩
  obtain ⟨w, hw, hd⟩ := exists_det_eq_two_mul_of_normalized hodd Q hN
  obtain ⟨w', hw', hd'⟩ := exists_det_eq_two_mul_of_normalized hodd Q' hN'
  obtain ⟨wi, hwi⟩ := hw.exists_right_inv
  set ε : R := w' * wi with hε
  have hεu : IsUnit ε := hw'.mul (isUnit_iff_exists_inv'.2 ⟨w, hwi⟩)
  -- `det_H (ε • Q) = (ε ^ r) ^ 2 * det_H Q'`
  have hdetε : (ε • Q).hessian.det = (ε ^ r) ^ 2 * Q'.hessian.det := by
    rw [hessian_smul', Matrix.det_smul, Fintype.card_fin, hd, hd', hε]
    linear_combination (2 * w' ^ (2 * r + 1) * wi ^ (2 * r)) * hwi
  have hiso : Siegel.IsometricGL Q' (ε • Q) :=
    uniqueNormalizedLocalGenus_odd h2 h20 hodd Q' (ε • Q) hN' (ε ^ r) (hεu.pow r) hdetε
  have hQnd : Q.Nondegenerate := by
    show Q.hessian.det ≠ 0
    rw [hd]; exact mul_ne_zero h20 hw.ne_zero
  have hsm := Tamagawa.localDensityForm_smul Q hQnd hπ (o := 0) (s := ε) (by simp)
    (by rw [zero_add, pow_one]; exact fun h => hπ.not_isUnit (isUnit_of_dvd_unit h hεu))
  rw [zero_mul, pow_zero, one_mul] at hsm
  rw [← hsm, DVR.localDensityForm_congr_left hiso, DVR.localDensityForm_congr_right _ hiso]

end QuadFormsKB.Hanke2011Structure.Dyadic
