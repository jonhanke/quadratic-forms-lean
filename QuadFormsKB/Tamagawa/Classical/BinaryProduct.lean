/-
# Classical special cases over $\mathbb Q$: the binary local product converges

**Layer:** number fields.

For an anisotropic nondegenerate binary $Q_0$ over $\mathcal O_F$ with discriminant field $E$ and a nondegenerate unary $T_0$
with a rational point, the family $\beta_v(L,T_0)/\lambda_v$ ($\lambda_v = 1-\chi_E(v)/Nv$) of `binDensityProduct` is
multipliable (`multipliable_binDensity`). This is the step `hmβ` inside the proofs of `siegelIndefinite_binary_uncond`
and `densityIdentity_corankOne`, made a statement so that `binDensityProduct` can be compared at two values of $m$.
-/
import QuadFormsKB.Tamagawa.Classical.Basic

open MeasureTheory Set Matrix MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil LocalDensity RegProd QuadFormsKB.NFEuler

variable {F : Type} [Field F] [NumberField F]

/-- **The local factors of `binDensityProduct` form a multipliable family.** -/
theorem multipliable_binDensity (Q₀ : QuadForm (𝓞 F) 2) (hQ : Q₀.Nondegenerate)
    (E : Type) [Field E] [NumberField E] [Algebra F E] (hE : IsDiscField Q₀ E)
    (T₀ : QuadForm (𝓞 F) 1) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀) :
    Multipliable fun v => NF.localDensityForm v Q₀ T₀ / lamL (chiE F E) v := by
  set lam := lamL (chiE F E) with hlamdef
  have hlam : ∀ v, 0 < lam v := lamL_pos (abs_chiE_le hE.finrank_eq_two)
  obtain ⟨S, hS⟩ := eventually_muLocSO_lamL_chiE Q₀ hQ hE
  have haS : ∀ v ∉ S, aSO Q₀ v / lam v = 1 := by
    intro v hv
    have h := hS v hv
    have h0 : 0 ≤ NF.siegelDensity v Q₀ Q₀ / lam v :=
      div_nonneg (siegelDensity_self_pos' Q₀ hQ v).le (hlam v).le
    rw [muLocSO_soStabSO, ← ENNReal.ofReal_one] at h
    rw [aSO_eq_siegelDensity Q₀ hQ v]
    exact (ENNReal.ofReal_eq_ofReal_iff h0 zero_le_one).mp h
  have hafin : (Function.mulSupport fun v => aSO Q₀ v / lam v).Finite :=
    S.finite_toSet.subset fun v hv => by
      by_contra h; exact hv (haS v h)
  have ha : Multipliable fun v => aSO Q₀ v / lam v := multipliable_of_hasFiniteMulSupport hafin
  obtain ⟨hm, -⟩ := count_mul_tprod (r := 1) Q₀ hQ T₀ hT Ξ lam hlam ha
  set D := towerCorankOne (r := 1) Q₀ hQ T₀ hT Ξ
  set G := (towerAdapted (r := 1) (n' := 1) Q₀ hQ T₀ Ξ D hT).g.val.det with hGdef
  set h := algebraMap (𝓞 F) F T₀.hessian.det with hhdef
  have hG : G ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)).ne_zero
  have hh : h ≠ 0 := algebraMap_det_ne_zero T₀ hT
  have hGv : ∀ v : HeightOneSpectrum (𝓞 F), ‖σV v G‖ ≠ 0 := fun v => norm_ne_zero_iff.2 ((map_ne_zero _).2 hG)
  have hhv : ∀ v : HeightOneSpectrum (𝓞 F), ‖σV v h‖ ≠ 0 := fun v => norm_ne_zero_iff.2 ((map_ne_zero _).2 hh)
  have hfG := mulSupport_finite_norm (F := F) hG
  have hfh := mulSupport_finite_norm (F := F) hh
  set u : HeightOneSpectrum (𝓞 F) → ℝ := fun v => ‖σV v G‖ ^ 2 * ‖σV v h‖⁻¹ with hu
  have hufin : (Function.mulSupport fun v => (u v)⁻¹).Finite := by
    refine (hfG.union hfh).subset fun v hv => ?_
    by_contra hcon
    apply hv
    simp only [Set.mem_union, Function.mem_mulSupport, not_or, not_not] at hcon
    show (‖σV v G‖ ^ 2 * ‖σV v h‖⁻¹)⁻¹ = 1
    rw [hcon.1, hcon.2]; norm_num
  have hu0 : ∀ v, u v ≠ 0 := fun v => mul_ne_zero (pow_ne_zero _ (hGv v)) (inv_ne_zero (hhv v))
  have hfu : ∀ v, frameLocFactor (r := 1) (n' := 1) Q₀ hQ T₀ Ξ D hT v / lam v = NF.localDensityForm v Q₀ T₀ / lam v * u v := by
    intro v
    simp only [frameLocFactor, hu, ← hGdef, ← hhdef, pow_one]
    field_simp
  have : (fun v => NF.localDensityForm v Q₀ T₀ / lam v) =
      fun v => frameLocFactor (r := 1) (n' := 1) Q₀ hQ T₀ Ξ D hT v / lam v * (u v)⁻¹ := by
    funext v; rw [hfu, mul_assoc, mul_inv_cancel₀ (hu0 v), mul_one]
  rw [this]
  exact hm.mul (multipliable_of_hasFiniteMulSupport hufin)

end QuadFormsKB.Tamagawa.Indefinite
