/-
# Siegel's formula for numbers by ternary forms with an isotropic complement, regularized

**Layer:** number fields. The case $r = 1$, $T_0 = \langle m\rangle$ of `siegelIndefiniteForms_rank2_isotropic_uncond`:
representations of $m\ne0$ by a ternary $Q_0$ (any signature, every number field) with $m^\perp$ **isotropic**, i.e.
$-2m\det H_{Q_0}$ a square in $F$ (Siegel's excluded case; e.g. $Q_0 = x_0^2 + x_1^2 - x_2^2$ over $\mathbb Q$ and $m$ a square).

* **`siegelIndefinite_ternary_isotropic_uncond`**:
  $$2\,c_\infty(m)\sum_i\rho^1(M_i, m) = |d_F|^{-1}\,\rho_F\prod_\mathfrak p\beta_\mathfrak p(L,m)\Bigl(1-\frac1{N\mathfrak p}\Bigr)\cdot\sum_iv(M_i),$$
  $c_\infty(m)$ = `cInfNF m` $= c_F(3)\prod_{w\mid\infty}|2m|_w^{-2}$, $\rho^1$ the norm-one measures of the representations
  $x\in M_i$, $Q_0(x) = m$ (as $1$-frames, `ratFrameEquivRatSphere`), $\beta_\mathfrak p(L,m)$ = `NF.localDensity v Q₀ m`,
  $\rho_F = \operatorname{Res}_{s=1}\zeta_F(s)$;
* `multipliable_localDensity_ternary_iso`: the product converges absolutely;
* `exists_ternary_iso_instance`: the hypotheses are satisfiable over every number field
  ($Q_0 = \langle1\rangle\perp W$ with $W$ isotropic binary, $m = 1$).
-/
import QuadFormsKB.Tamagawa.Indefinite.FormsIndefiniteIso
import QuadFormsKB.Tamagawa.Indefinite.SiegelTernary
import QuadFormsKB.Tamagawa.Indefinite.Rank2Examples

open MeasureTheory Set Matrix Filter
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames LocalDensity

variable {F : Type} [Field F] [NumberField F]

/-- **The regularized local side for the representations of $m$ by a ternary form, isotropic complement**:
$|d_F|^{-1}\rho_F\prod_\mathfrak p\beta_\mathfrak p(L,m)\,(1 - N\mathfrak p^{-1})$. -/
@[kb "siegel1944indef" "local side, ternary forms, m⊥ isotropic (excluded case), regularized by Res ζ_F [unverified]"]
def ternaryIsoDensityProductReg (Q₀ : QuadForm (𝓞 F) (1 + 2)) (m : 𝓞 F) : ℝ :=
  |(discr F : ℝ)| ^ (-1 : ℝ) * dedekindZeta_residue F * ∏' v, NF.localDensity v Q₀ m * lamV v

theorem isSquare_deltaForms_unary {N : ℕ} {Q₀ : QuadForm (𝓞 F) N} {m : 𝓞 F}
    (hiso : IsSquare (-(2 * (m : F) * algebraMap (𝓞 F) F Q₀.hessian.det))) :
    IsSquare (algebraMap (𝓞 F) F (deltaForms Q₀ (DVR.unary m))) := by
  rwa [algebraMap_deltaForms_unary]

theorem isoDensityProductReg_unary (Q₀ : QuadForm (𝓞 F) (1 + 2)) (m : 𝓞 F) :
    isoDensityProductReg Q₀ (DVR.unary m) = ternaryIsoDensityProductReg Q₀ m := by
  rw [isoDensityProductReg, ternaryIsoDensityProductReg]
  simp only [NF.localDensityForm_unary]
  norm_num

/-- **Siegel's formula for numbers by ternary forms with $m^\perp$ isotropic, regularized — unconditional, every number
field** (the case $r = 1$ of `siegelIndefiniteForms_rank2_isotropic_uncond`): for $Q_0$ nondegenerate ternary over
$\mathcal O_F$ (any signature), $m\in\mathcal O_F$, $m\ne0$, represented by $Q_0$ over $F$ (a rational point $\xi$), and
$-2m\det H_{Q_0}$ a square in $F$ ($m^\perp$ isotropic, the stabilizers split tori),
$$2\,c_\infty(m)\sum_i\rho^1(M_i, m) = |d_F|^{-1}\,\rho_F\prod_\mathfrak p\beta_\mathfrak p(L,m)\Bigl(1-\frac1{N\mathfrak p}\Bigr)
  \cdot\sum_iv(M_i),$$
with $\rho^1$ the measures of representations for the norm-one stabilizers (`repMeasureIso`). -/
@[kb "siegel1944indef" "On the theory of indefinite quadratic forms; ternary forms, m⊥ isotropic (excluded case), regularized [unverified]"]
theorem siegelIndefinite_ternary_isotropic_uncond (Q₀ : QuadForm (𝓞 F) (1 + 2)) (hQ : Q₀.Nondegenerate) {m : 𝓞 F}
    (hm : (m : F) ≠ 0) (hiso : IsSquare (-(2 * (m : F) * algebraMap (𝓞 F) F Q₀.hessian.det)))
    (ξ : RatSphere Q₀ (m : F)) :
    2 * (cInfNF (k := 2) (m : F) * ∑' i, repMeasureIso Q₀ hQ (DVR.unary m) (unary_nondegenerate hm)
        (isSquare_deltaForms_unary hiso) ((ratFrameEquivRatSphere Q₀ m).symm ξ) i) =
      ENNReal.ofReal (ternaryIsoDensityProductReg Q₀ m) * ∑' i, unitVolume Q₀ hQ i := by
  rw [← cInfTNF_unary Q₀ m, ← isoDensityProductReg_unary]
  exact siegelIndefiniteForms_rank2_isotropic_uncond Q₀ hQ (DVR.unary m) (unary_nondegenerate hm)
    (isSquare_deltaForms_unary hiso) _ le_rfl

/-- The ternary regularized product converges absolutely. -/
theorem multipliable_localDensity_ternary_iso (Q₀ : QuadForm (𝓞 F) (1 + 2)) (hQ : Q₀.Nondegenerate) {m : 𝓞 F}
    (hm : (m : F) ≠ 0) (hiso : IsSquare (-(2 * (m : F) * algebraMap (𝓞 F) F Q₀.hessian.det)))
    (ξ : RatSphere Q₀ (m : F)) :
    Multipliable fun v => NF.localDensity v Q₀ m * lamV v := by
  have := multipliable_localDensityForm_iso Q₀ hQ (DVR.unary m) (unary_nondegenerate hm)
    (isSquare_deltaForms_unary hiso) ((ratFrameEquivRatSphere Q₀ m).symm ξ) le_rfl
  simpa only [NF.localDensityForm_unary] using this

/-- **The hypotheses of the isotropic ternary headline are satisfiable over every number field**: there is a
nondegenerate ternary $Q_0$ over $\mathcal O_F$ representing $m = 1$ over $F$ with $-2m\det H_{Q_0}$ a square in $F$
($Q_0 = \langle1\rangle\perp W$, $W$ isotropic binary). -/
theorem exists_ternary_iso_instance (F : Type) [Field F] [NumberField F] :
    ∃ Q₀ : QuadForm (𝓞 F) (1 + 2), Q₀.Nondegenerate ∧
      IsSquare (-(2 * ((1 : 𝓞 F) : F) * algebraMap (𝓞 F) F Q₀.hessian.det)) ∧
      Nonempty (RatSphere Q₀ ((1 : 𝓞 F) : F)) := by
  obtain ⟨W, hWnd, hW⟩ := exists_isotropic_binary F
  have hdet : (blockForm (DVR.unary (1 : 𝓞 F)) W).hessian.det = 2 * W.hessian.det := by
    rw [det_hessian_blockForm]
    congr 1
    rw [Matrix.det_unique]
    simp [DVR.unary, QuadForm.hessian, QuadForm.diag]
    norm_num
  refine ⟨blockForm (DVR.unary (1 : 𝓞 F)) W, ?_, ?_, ?_⟩
  · unfold QuadForm.Nondegenerate
    rw [hdet]
    exact mul_ne_zero two_ne_zero hWnd
  · rw [hdet]
    obtain ⟨s, hs⟩ := (isotropicF_iff_isSquare W).mp hW
    refine ⟨2 * s, ?_⟩
    simp only [map_neg, map_mul, map_ofNat, map_one] at hs ⊢
    linear_combination 4 * hs
  · refine ⟨⟨Pi.single 0 1, ?_⟩⟩
    show qF _ _ = _
    simp only [qF, QuadForm.eval, map_blockForm, evalIn_blockForm]
    have h2 : ∀ j : Fin 2, (Pi.single (0 : Fin (1 + 2)) (1 : F) : Fin (1 + 2) → F) (Fin.natAdd 1 j) = 0 := by
      intro j
      rw [Pi.single_apply, ite_eq_right_iff]
      intro h
      have := congrArg Fin.val h
      simp at this
    simp [QuadForm.evalIn, QuadForm.map, h2, DVR.unary, QuadForm.diag, Pi.single_apply]

end QuadFormsKB.Tamagawa.Indefinite
