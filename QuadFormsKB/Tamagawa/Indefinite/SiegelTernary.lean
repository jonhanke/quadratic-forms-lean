/-
# Siegel's formula for numbers by ternary forms, and the regularized local side

**Layer:** number fields. Consequences of `siegelIndefiniteForms_rank2_uncond` (complement of rank $2$, anisotropic):

* **`multipliable_localDensityForm_rank2`**: the regularized product converges absolutely:
  $\prod_\mathfrak p\beta_\mathfrak p(L,T_0)\,(1-\chi(\mathfrak p)/N\mathfrak p)$ is (unconditionally) multipliable, $\chi$ = `chiForms Q₀ T₀`.
  (At good $\mathfrak p$ the factor is $\alpha_\mathfrak p(L)$, $N\ge3$.)
* **`hasProd_normOrder_localDensityForm_rank2`**: *relation to the naive product.* The plain product
  $\prod_\mathfrak p\beta_\mathfrak p(L,T_0)$ is not absolutely convergent (its factors are $1+\chi(\mathfrak p)/N\mathfrak p+O(N\mathfrak p^{-2})$);
  given the prime ideal theorem for $\chi$ (`NaturalOrderEulerOne χ`, a named input; a theorem over $\mathbb Q$), its partial
  products over $N\mathfrak p\le X$ converge, as $X\to\infty$, to the regularized value `regProd χ 1 β` of the headline.
* **`siegelIndefinite_ternary_uncond`**: the case $r = 1$, $T_0 = \langle m\rangle$: Siegel's formula for the representations
  of $m\ne0$ by a ternary $Q_0$ (any signature, every number field) with $m^\perp$ anisotropic, i.e.
  $-2m\det H_{Q_0}$ not a square in $F$:
  $$c_\infty(m)\sum_i\rho(M_i, m) = |d_F|^{-1}\,L(1,\chi)\prod_\mathfrak p\beta_\mathfrak p(L,m)\Bigl(1-\frac{\chi(\mathfrak p)}{N\mathfrak p}\Bigr)
    \cdot\sum_iv(M_i),$$
  $c_\infty(m)$ = `cInfNF m` $= c_F(3)\prod_{w\mid\infty}|2m|_w^{-2}$, $\rho(M_i,m)$ the measures of the representations
  $x\in M_i$, $Q_0(x) = m$ (as $1$-frames, `ratFrameEquivRatSphere`), $\beta_\mathfrak p(L,m)$ = `NF.localDensity v Q₀ m`.
-/
import QuadFormsKB.Tamagawa.Indefinite.FormsIndefiniteRank2
import QuadFormsKB.Tamagawa.Indefinite.SiegelComplexChecks

open MeasureTheory Set Matrix Filter
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames LocalDensity
  QuadFormsKB.RegProd NFEuler

variable {F : Type} [Field F] [NumberField F] {r : ℕ}

/-! ### The regularized product -/

section Reg

variable (Q₀ : QuadForm (𝓞 F) (r + 2)) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate)
  (hW : ¬ IsSquare (algebraMap (𝓞 F) F (deltaForms Q₀ T₀))) (Ξ : RatFrame Q₀ T₀)

include hQ hT hW Ξ in
/-- **The regularized product converges absolutely**: $\prod_\mathfrak p\beta_\mathfrak p(L,T_0)(1-\chi(\mathfrak p)/N\mathfrak p)$ is
multipliable ($\chi$ = `chiForms Q₀ T₀`, $\delta$ not a square, $T_0$ represented over $F$). -/
@[kb "siegel1935" "Hauptsatz (local side, N − r = 2: absolute convergence of the regularized product) [unverified]"]
theorem multipliable_localDensityForm_rank2 (hr : 1 ≤ r) :
    Multipliable fun v => NF.localDensityForm v Q₀ T₀ * (1 - chiForms Q₀ T₀ v / (normP v : ℝ)) := by
  classical
  set D := chosenTowerRank2 Q₀ hQ T₀ hT hW Ξ
  set χ := chiForms Q₀ T₀
  have hA : AnisotropicF D.Q'' := (anisotropicF_adapted_iff Q₀ T₀ hT (towerAdapted Q₀ hQ T₀ Ξ D hT)).2 hW
  obtain ⟨S, hS⟩ := chiP_frame_eq_chiForms_nf Q₀ T₀ hQ hT hW (towerAdapted Q₀ hQ T₀ Ξ D hT) D.hQ''
  have hχ : ∀ v, |χ v| ≤ 1 := abs_chiForms_le Q₀ T₀
  have hm := multipliable_frameLocFactor_lam Q₀ hQ T₀ Ξ D hT (lamL χ) (lamL_pos hχ)
    (multipliable_muLocSO_lamL D.Q'' D.hQ'' hχ S hS) (finFactor_lamL_pos D.Q'' D.hQ'' hχ S hS) (by norm_num)
    (by omega)
  set g := (towerAdapted Q₀ hQ T₀ Ξ D hT).g.val.det with hgdef
  set h := algebraMap (𝓞 F) F T₀.hessian.det with hhdef
  have hg : g ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)).ne_zero
  have hh : h ≠ 0 := algebraMap_det_ne_zero T₀ hT
  have hfa := mulSupport_finite_norm (F := F) hg
  have hfb := mulSupport_finite_norm (F := F) hh
  set u : HeightOneSpectrum (𝓞 F) → ℝ := fun v => ‖σV v h‖ ^ 2 * (‖σV v g‖ ^ (2 + 1))⁻¹ with hu
  have hufin : (Function.mulSupport u).Finite := by
    refine (hfb.union hfa).subset fun v hv => ?_
    by_contra hcon
    apply hv
    simp only [Set.mem_union, Function.mem_mulSupport, not_or, not_not] at hcon
    show u v = 1
    simp only [hu, hcon.1, hcon.2, one_pow, inv_one, one_mul]
  have hβ : ∀ v, NF.localDensityForm v Q₀ T₀ * (1 - χ v / (normP v : ℝ)) =
      (frameLocFactor Q₀ hQ T₀ Ξ D hT v * lamL χ v) * u v := fun v => by
    have ha : ‖σV v g‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero _).2 hg)
    have hb : ‖σV v h‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero _).2 hh)
    simp only [frameLocFactor, hu, lamL]
    rw [← hgdef, ← hhdef]
    field_simp
  rw [funext hβ]
  exact hm.mul (multipliable_of_hasFiniteMulSupport hufin)

include hQ hT hW Ξ in
/-- **The naive product in the natural order** (given the prime ideal theorem for $\chi$): the partial products
$\prod_{N\mathfrak p\le X}\beta_\mathfrak p(L,T_0)$ converge to the regularized value `regProd χ 1 β`. -/
@[kb "hanke2004" "(5.3), p. 368 (natural order = L(1, χ) × absolutely convergent product) [unverified]"]
theorem hasProd_normOrder_localDensityForm_rank2 (hr : 1 ≤ r) (hN : NaturalOrderEulerOne (chiForms Q₀ T₀)) :
    HasProd (fun v => NF.localDensityForm v Q₀ T₀)
      (regProd (chiForms Q₀ T₀) 1 fun v => NF.localDensityForm v Q₀ T₀) (normOrder F) :=
  hasProd_normOrder_regProd hN (abs_chiForms_le Q₀ T₀)
    (multipliable_localDensityForm_rank2 Q₀ hQ T₀ hT hW Ξ hr).hasProd

end Reg

/-! ### Numbers: ternary forms -/

/-- **The regularized local side for the representations of $m$ by a ternary form**:
$|d_F|^{-1}L(1,\chi)\prod_\mathfrak p\beta_\mathfrak p(L,m)\,(1-\chi(\mathfrak p)/N\mathfrak p)$, $\chi$ = `chiForms Q₀ ⟨m⟩`
($\chi(\mathfrak p) = (-2m\det H/\mathfrak p)$, `chiTern Q₀ m`). -/
@[kb "siegel1935" "Hauptsatz (local side, ternary forms, regularized) [unverified]"]
def ternaryDensityProductReg (Q₀ : QuadForm (𝓞 F) (1 + 2)) (m : 𝓞 F) : ℝ :=
  |(discr F : ℝ)| ^ (-1 : ℝ) * regProd (chiForms Q₀ (DVR.unary m)) 1 (fun v => NF.localDensity v Q₀ m)

theorem algebraMap_deltaForms_unary {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (m : 𝓞 F) :
    algebraMap (𝓞 F) F (deltaForms Q₀ (DVR.unary m)) = -(2 * (m : F) * algebraMap (𝓞 F) F Q₀.hessian.det) := by
  have hdet : (DVR.unary m).hessian.det = 2 * m := by
    rw [Matrix.det_unique]
    simp [DVR.unary, QuadForm.hessian, QuadForm.diag, two_mul]
  rw [deltaForms, hdet]
  simp only [map_neg, map_mul, map_ofNat]
  ring

theorem not_isSquare_deltaForms_unary {N : ℕ} {Q₀ : QuadForm (𝓞 F) N} {m : 𝓞 F}
    (hW : ¬ IsSquare (-(2 * (m : F) * algebraMap (𝓞 F) F Q₀.hessian.det))) :
    ¬ IsSquare (algebraMap (𝓞 F) F (deltaForms Q₀ (DVR.unary m))) := by
  rwa [algebraMap_deltaForms_unary]

theorem frameDensityProductReg_unary (Q₀ : QuadForm (𝓞 F) (1 + 2)) (m : 𝓞 F) :
    frameDensityProductReg Q₀ (DVR.unary m) = ternaryDensityProductReg Q₀ m := by
  rw [frameDensityProductReg, ternaryDensityProductReg]
  simp only [NF.localDensityForm_unary]
  norm_num

/-- **Siegel's formula for numbers by ternary forms, indefinite (any signature), every number field —
unconditional** (Siegel 1935/1936, measure form; the case $r = 1$ of `siegelIndefiniteForms_rank2_uncond`): for $Q_0$
nondegenerate ternary over $\mathcal O_F$, $m\in\mathcal O_F$, $m\ne0$, represented by $Q_0$ over $F$ (a rational point $\xi$
with $Q_0(\xi) = m$), and $m^\perp$ anisotropic, i.e. $-2m\det H_{Q_0}$ not a square in $F$,
$$c_\infty(m)\sum_i\rho(M_i, m) = |d_F|^{-1}\,L(1,\chi)\prod_\mathfrak p\beta_\mathfrak p(L,m)\Bigl(1-\frac{\chi(\mathfrak p)}{N\mathfrak p}\Bigr)
  \cdot\sum_iv(M_i),$$
$c_\infty(m)$ = `cInfNF m` $= c_F(3)\prod_{w\mid\infty}|2m|_w^{-2}$, $\rho$ the measures of the representations of $m$
(vectors as $1$-frames; stabilizer measures of `frameArchFibrationRank2`), $\chi(\mathfrak p) = (-2m\det H_{Q_0}/\mathfrak p)$. -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form; ternary forms, numbers; every number field) [unverified]"]
theorem siegelIndefinite_ternary_uncond (Q₀ : QuadForm (𝓞 F) (1 + 2)) (hQ : Q₀.Nondegenerate) {m : 𝓞 F}
    (hm : (m : F) ≠ 0) (hW : ¬ IsSquare (-(2 * (m : F) * algebraMap (𝓞 F) F Q₀.hessian.det)))
    (ξ : RatSphere Q₀ (m : F)) :
    cInfNF (k := 2) (m : F) * ∑' i, repMeasureT Q₀ (DVR.unary m) hQ
        (frameArchFibrationRank2 Q₀ hQ (DVR.unary m) (unary_nondegenerate hm) (not_isSquare_deltaForms_unary hW)
          ((ratFrameEquivRatSphere Q₀ m).symm ξ)) i =
      ENNReal.ofReal (ternaryDensityProductReg Q₀ m) * ∑' i, unitVolume Q₀ hQ i := by
  rw [← cInfTNF_unary Q₀ m, ← frameDensityProductReg_unary]
  exact siegelIndefiniteForms_rank2_uncond Q₀ hQ (DVR.unary m) (unary_nondegenerate hm)
    (not_isSquare_deltaForms_unary hW) _ le_rfl

end QuadFormsKB.Tamagawa.Indefinite
