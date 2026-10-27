import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereBox
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarGlobal

/-!
# The local constants of the adelic sphere and the product formula

With $x_1 = \det G/d$ and $x_2 = 2\rho$ in $F^\times$, the local constants of the orbital identities are
$c_v = |x_1|_v^{N}\,|x_2|_v^{-k}$ at every place (`cFin_eq`, `cReal_eq'`), so their product over all places is $1$
(`prod_cReal_mul_tprod_cFin`, totally real $F$; Weil's product formula, Mathlib's `prod_eq_abs_norm` and
`FinitePlace.prod_eq_inv_abs_norm`).
-/

open MeasureTheory Set Matrix
open scoped ENNReal RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure

variable {F : Type} [Field F] [NumberField F] {k : ℕ} {Q₀ : QuadForm (𝓞 F) (k + 1)} {ρ : F}

/-! ### The product formula -/

theorem mulSupport_finite_norm {x : F} (hx : x ≠ 0) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => ‖σV v x‖).Finite := by
  have h := sph_eventually_valued_eq_one hx
  rw [Filter.eventually_cofinite] at h
  refine h.subset fun v hv => ?_
  intro h1
  apply hv
  show ‖σV v x‖ = 1
  rw [FinitePlace.norm_def, h1, map_one]; rfl

/-- **The product formula** for $x\in F^\times$: $\prod_{w\mid\infty}|x|_w^{m_w}\cdot\prod_v\|x\|_v = 1$. -/
theorem prod_infinitePlace_mul_tprod {x : F} (hx : x ≠ 0) :
    (∏ w : InfinitePlace F, w x ^ w.mult) * ∏' v : HeightOneSpectrum (𝓞 F), ‖σV v x‖ = 1 := by
  have h2 := FinitePlace.prod_eq_inv_abs_norm hx
  rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm] at h2
  simp only [FinitePlace.equivHeightOneSpectrum_symm_apply] at h2
  rw [tprod_eq_finprod (mulSupport_finite_norm hx)]
  rw [show (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖σV v x‖) =
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v x‖ from rfl, h2, InfinitePlace.prod_eq_abs_norm]
  have hN : (|Algebra.norm ℚ x| : ℝ) ≠ 0 := by
    have : Algebra.norm ℚ x ≠ 0 := (Algebra.norm_ne_zero_iff).mpr hx
    exact_mod_cast abs_ne_zero.mpr this
  push_cast
  exact mul_inv_cancel₀ hN

open Classical in
/-- **The product formula, totally real form**: $\prod_{w\ \mathrm{real}}|\sigma_w x|\cdot\prod_v\|x\|_v = 1$. -/
theorem prod_real_mul_tprod [IsEmpty {w : InfinitePlace F // w.IsComplex}] {x : F} (hx : x ≠ 0) :
    (∏ w : {w : InfinitePlace F // w.IsReal}, |σR w x|) * ∏' v : HeightOneSpectrum (𝓞 F), ‖σV v x‖ = 1 := by
  have h := prod_infinitePlace_mul_tprod hx
  rw [← sim_prod_places, Fintype.prod_empty (ι := {w : InfinitePlace F // w.IsComplex}), mul_one] at h
  convert h using 2
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [mult_isReal w, pow_one, ← norm_embedding_of_isReal w.2, Real.norm_eq_abs]

namespace AdelicSphereSetup

variable (S : AdelicSphereSetup Q₀ ρ) (hρ : ρ ≠ 0)

/-- $x_1 = \det G/d\in F^\times$. -/
abbrev x1 : F := algebraMap (𝓞 F) F S.C.G.det / algebraMap (𝓞 F) F S.C.d

theorem x1_ne_zero : S.x1 ≠ 0 :=
  div_ne_zero ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr S.C.hG)
    ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr S.C.hd)

theorem det_PAt {K : Type*} [Field K] (σ : F →+* K) :
    (S.PAt σ).val.det = σ (algebraMap (𝓞 F) F S.C.G.det) := by
  rw [PAt_val, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

include hρ in
/-- **The finite constant in closed form**: $c_v = |x_1|_v^{N}|2\rho|_v^{-k}$. -/
theorem cFin_eq (v : HeightOneSpectrum (𝓞 F)) :
    S.cFin v = ENNReal.ofReal (‖σV v S.x1‖ ^ (k + 1) * (‖σV v (2 * ρ)‖ ^ k)⁻¹) := by
  have hd : ‖S.dV v‖ ≠ 0 := norm_ne_zero_iff.mpr (S.dV_ne_zero v)
  have hG : ‖σV v (algebraMap (𝓞 F) F S.C.G.det)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr ((map_ne_zero _).mpr ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr S.C.hG))
  have hr : ‖σV v ρ‖ ≠ 0 := norm_ne_zero_iff.mpr ((map_ne_zero _).mpr hρ)
  have h2 : ‖(2 : v.adicCompletion F)‖ ≠ 0 := norm_ne_zero_iff.mpr two_ne_zero
  have e1 : ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F (simJac 1 S.C.G))‖ =
      ‖σV v (algebraMap (𝓞 F) F S.C.G.det)‖ ^ (k + 1 + 1) := by
    rw [show simJac 1 S.C.G = 1 ^ ((k + 1) * (k + 1 + 1) / 2) * S.C.G.det ^ (k + 1 + 1) from rfl, one_pow, one_mul,
      map_pow, map_pow, norm_pow]
    rfl
  have e2 : S.bPsi v = ENNReal.ofReal (‖S.dV v‖⁻¹ ^ 2 / (‖S.dV v‖⁻¹ ^ (k + 1) *
      ‖σV v (algebraMap (𝓞 F) F S.C.G.det)‖)) := by
    rw [bPsi]
    have a1 : (distribHaarChar (v.adicCompletion F) (S.cPsi v) : ℝ) = ‖S.dV v‖⁻¹ ^ 2 := by
      rw [distribHaarChar_adic_norm, cPsi, Units.val_mk0, norm_pow, norm_inv]
    have a2 : (distribHaarChar (v.adicCompletion F) (Matrix.GeneralLinearGroup.det (S.psiGL v)) : ℝ) =
        ‖S.dV v‖⁻¹ ^ (k + 1) * ‖σV v (algebraMap (𝓞 F) F S.C.G.det)‖ := by
      rw [distribHaarChar_adic_norm, Matrix.GeneralLinearGroup.val_det_apply, psiGL_val, Matrix.det_smul,
        norm_mul, norm_pow, norm_inv, S.det_PAt, Fintype.card_fin]
    rw [ENNReal.ofReal_div_of_pos (by positivity), ← a1, ← a2, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  have e3 : absTwoM v S.C.m₀ = ‖σV v (2 * ρ)‖ * ‖S.dV v‖ ^ 2 := by
    rw [absTwoM, show NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F (2 * S.C.m₀)) =
      σV v (algebraMap (𝓞 F) F (2 * S.C.m₀)) from rfl, map_mul, S.C.m₀_eq, map_mul, map_mul, map_mul]
    have hq : qF Q₀ S.ξ.1 = ρ := S.ξ.2
    rw [hq, map_ofNat, map_pow, norm_mul, norm_mul, norm_mul, norm_pow]
    ring
  rw [cFin, e1, e2, e3, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [div_eq_mul_inv]
  simp only [x1, map_div₀, norm_div]
  rw [show ‖σV v (algebraMap (𝓞 F) F S.C.d)‖ = ‖S.dV v‖ from rfl]
  generalize ‖S.dV v‖ = D at hd ⊢
  generalize ‖σV v (algebraMap (𝓞 F) F S.C.G.det)‖ = Gn at hG ⊢
  generalize ‖σV v (2 * ρ)‖ = R
  have hD : D ^ 2 * D⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hd, one_pow]
  field_simp
  calc _ = Gn ^ 2 * Gn ^ k * (D ^ 2 * D⁻¹ ^ 2) * D⁻¹ ^ (k * 2) * R⁻¹ ^ k := by rw [hD]; ring
    _ = _ := by ring

include hρ in
/-- $x_2 = 2\rho\ne0$. -/
theorem x2_ne_zero : (2 * ρ : F) ≠ 0 := mul_ne_zero two_ne_zero hρ

include hρ in
theorem cFin_toReal (v : HeightOneSpectrum (𝓞 F)) :
    (S.cFin v).toReal = ‖σV v S.x1‖ ^ (k + 1) * (‖σV v (2 * ρ)‖ ^ k)⁻¹ := by
  rw [S.cFin_eq hρ v, ENNReal.toReal_ofReal (by positivity)]

include hρ in
theorem cReal_toReal (w : {w : InfinitePlace F // w.IsReal}) :
    (S.cReal w).toReal = |σR w S.x1| ^ (k + 1) * (|σR w (2 * ρ)| ^ k)⁻¹ := by
  rw [S.cReal_eq hρ w, ENNReal.toReal_ofReal (by positivity), S.det_PAt, x1, map_div₀, map_mul, map_ofNat]

open Classical in
include hρ in
/-- **The local constants multiply to $1$** (totally real $F$; product formula for $x_1$ and $x_2$). -/
theorem prod_cReal_mul_tprod_cFin [IsEmpty {w : InfinitePlace F // w.IsComplex}] :
    (∏ w : {w : InfinitePlace F // w.IsReal}, (S.cReal w).toReal) * ∏' v, (S.cFin v).toReal = 1 := by
  set T : Finset (HeightOneSpectrum (𝓞 F)) :=
    (mulSupport_finite_norm S.x1_ne_zero).toFinset ∪ (mulSupport_finite_norm (x2_ne_zero hρ)).toFinset
  have h1 : ∀ v ∉ T, ‖σV v S.x1‖ = 1 := fun v hv => by
    by_contra h; exact hv (Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr h))
  have h2 : ∀ v ∉ T, ‖σV v (2 * ρ)‖ = 1 := fun v hv => by
    by_contra h; exact hv (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr h))
  have p1 : ∏' v : HeightOneSpectrum (𝓞 F), ‖σV v S.x1‖ = ∏ v ∈ T, ‖σV v S.x1‖ := tprod_eq_prod h1
  have p2 : ∏' v : HeightOneSpectrum (𝓞 F), ‖σV v (2 * ρ)‖ = ∏ v ∈ T, ‖σV v (2 * ρ)‖ := tprod_eq_prod h2
  have p3 : ∏' v, (S.cFin v).toReal = ∏ v ∈ T, (S.cFin v).toReal :=
    tprod_eq_prod fun v hv => by rw [S.cFin_toReal hρ, h1 v hv, h2 v hv]; simp
  have f1 := prod_real_mul_tprod S.x1_ne_zero
  have f2 := prod_real_mul_tprod (x2_ne_zero hρ)
  rw [p1] at f1
  rw [p2] at f2
  rw [p3]
  simp only [S.cReal_toReal hρ, S.cFin_toReal hρ, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_inv_distrib]
  calc (∏ w, |σR w S.x1|) ^ (k + 1) * ((∏ w, |σR w (2 * ρ)|) ^ k)⁻¹ *
        ((∏ v ∈ T, ‖σV v S.x1‖) ^ (k + 1) * ((∏ v ∈ T, ‖σV v (2 * ρ)‖) ^ k)⁻¹)
      = ((∏ w, |σR w S.x1|) * ∏ v ∈ T, ‖σV v S.x1‖) ^ (k + 1) *
          (((∏ w, |σR w (2 * ρ)|) * ∏ v ∈ T, ‖σV v (2 * ρ)‖) ^ k)⁻¹ := by
        rw [mul_pow, mul_pow, mul_inv]; ring
    _ = 1 := by rw [f1, f2]; simp

end AdelicSphereSetup

end QuadFormsKB.Tamagawa.Measure.Weil

end
