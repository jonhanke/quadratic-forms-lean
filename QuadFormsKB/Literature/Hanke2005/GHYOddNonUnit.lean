/-
# Gan–Hanke–Yu 2001, Table 4: the odd-rank row $\delta\notin A^\times$, $w = 1$, at a dyadic place

W. T. Gan, J. Hanke, J.-K. Yu, *On an exact mass formula of Shimura*, Duke Math. J. 107 (2001), (6.6), (6.11), Table 4.

For odd rank $n = 2k+1$ and $\delta$ a uniformizer times a unit, GHY's maximal lattice of $V_{\delta,1} = \mathbb H^k\perp F_\delta$
is $\Delta^k\perp A$ with the form $\delta x^2$, i.e. `hypSum (unary (π u)) k` here. This row is excluded by Shimura's
hypothesis ($\det$ a unit times a square for odd $n$), and is one of the cases GHY add. We compute its local density at a
dyadic place, at every level $k$:
$$\beta(\mathbb H^k\perp\langle\pi u\rangle) = 2q^{e+1}\prod_{j<k}\rho_j(q),\qquad
\rho_j(Z) = \frac{(q^{j+1}-1)(q^{1+j}+Z)}{q^{2j+2}},$$
from $\beta(\langle\pi u\rangle) = q\cdot2q^e$ (scaling and the unary density) and the recursion
`localDensityForm_hypSum_succ` with residue zero count $Z = q$ (the residue form is $0$).
-/
import QuadFormsKB.Literature.Hanke2005.DensityDyadicKernelAniso

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.LocalDensity.HypFrame QuadFormsKB.Tamagawa
  QuadForm

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem unary_mul_eq_smul (p u : R) : DVR.unary (p * u) = p • DVR.unary u := by
  ext i j
  fin_cases i; fin_cases j
  simp [DVR.unary, QuadForm.diag]

/-- **The density of $\mathbb H^k\perp\langle\pi u\rangle$ at a dyadic prime** (GHY Table 4, $\delta\notin A^\times$, $w = 1$):
$2q^{e+1}\prod_{j<k}\rho_j(q)$, $\pi^e\,\|\,2$, $u$ a unit. -/
@[kb "ganhankeyu2001" "(6.6), (6.11), Table 4 (odd rank, δ ∉ A×, w = 1)"]
theorem localDensityForm_hypSum_piUnit [Finite (IsLocalRing.ResidueField R)]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {π : R} (hπ : Irreducible π) {e : ℕ}
    (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) {u : R} (hu : IsUnit u) (k : ℕ) :
    localDensityForm (hypSum (DVR.unary (π * u)) k) (hypSum (DVR.unary (π * u)) k) π =
      2 * (q R : ℝ) ^ (e + 1) * ∏ j ∈ Finset.range k, rho (q R) 1 (q R) j := by
  have h20 : (2 : R) ≠ 0 := fun h => he.2 (h ▸ dvd_zero _)
  have hπu : π * u ≠ 0 := mul_ne_zero hπ.ne_zero hu.ne_zero
  have hN : (DVR.unary (π * u)).Nondegenerate := by
    rw [QuadForm.Nondegenerate, hessian_unary_det]; exact mul_ne_zero h20 hπu
  have han : ∀ x, (DVR.unary (π * u)).eval x = 0 → x = 0 := by
    intro x hx
    have e1 : (DVR.unary (π * u)).eval x = π * u * x 0 * x 0 := by
      simp [DVR.unary, QuadForm.diag, QuadForm.eval, QuadForm.evalIn]
    rw [e1] at hx
    funext i; fin_cases i
    simpa [hπu] using hx
  have hZ : (resZero π (DVR.unary (π * u)) : ℝ) = q R := by
    rw [resZero_eq_zeroCount_res hπ]
    have h0 : ∀ x, ((DVR.unary (π * u)).map (IsLocalRing.residue R)).eval x = 0 := by
      intro x
      have hr : IsLocalRing.residue R (π * u) = 0 := (res_eq_zero_iff' hπ _).2 (dvd_mul_right _ _)
      simp [DVR.unary, QuadForm.diag, QuadForm.eval, QuadForm.evalIn, QuadForm.map, hr]
    unfold zeroCount
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv h0), Nat.card_fun, Nat.card_fin, pow_one]
    rfl
  induction k with
  | zero =>
    simp only [Finset.range_zero, Finset.prod_empty, mul_one]
    show localDensityForm (DVR.unary (π * u)) (DVR.unary (π * u)) π = _
    have hU : (DVR.unary u).Nondegenerate := by
      rw [QuadForm.Nondegenerate, hessian_unary_det]; exact mul_ne_zero h20 hu.ne_zero
    rw [unary_mul_eq_smul, localDensityForm_smul (DVR.unary u) hU hπ (o := 1) (by simp)
      (fun h => hπ.not_isUnit (isUnit_of_dvd_one (by
        rw [pow_two] at h; exact (mul_dvd_mul_iff_left hπ.ne_zero).mp (by simpa using h)))),
      localDensityForm_self_unary π hπ e he hu]
    ring
  | succ k ih =>
    rw [localDensityForm_hypSum_succ hπ _ hN han k, ih, hZ, Finset.prod_range_succ]
    ring

end QuadFormsKB.Hanke2005
