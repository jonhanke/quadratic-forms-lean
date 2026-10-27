/-
# The product formula with convergence factors, for the algebraic frame data

`frameDensity_identity_lam` (`FormsIndefiniteRank2.lean`) uses only the adapted frame $g = [\Xi\mid C]$ of the
tower;
this is the same statement and proof for `D : FrameTowerAlg` (namespace `IsoAlg`): the identity in $\mathbb R$
$$c_F(N)\prod_{w\mid\infty}|\det H_{T_0}|_w^{-n'}\cdot\frac{\prod_{w\mid\infty}|\det g|_w^{n'+1}}{c_F(n')}\cdot
  \prod_\mathfrak p\beta_\mathfrak p\,|\det g|_\mathfrak p^{n'+1}|\det H_{T_0}|_\mathfrak p^{-n'}\lambda_\mathfrak p =
  |d_F|^{-(N(N-1)-n'(n'-1))/4}\prod_\mathfrak p\beta_\mathfrak p(L,T_0)\,\lambda_\mathfrak p.$$
-/
import QuadFormsKB.Tamagawa.Indefinite.IsoOrbitAlg
import QuadFormsKB.Tamagawa.Indefinite.FormsIndefiniteRank2

open MeasureTheory Set Matrix MulAction Filter
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite.IsoAlg

open QuadFormsKB.Tamagawa.Indefinite
open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames LocalDensity
  QuadFormsKB.RegProd NFEuler

variable {F : Type} [Field F] [NumberField F] {r : ℕ}

section Identity

variable {n' : ℕ} (Q₀ : QuadForm (𝓞 F) (r + n')) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r)
  (Ξ : RatFrame Q₀ T₀)

open Classical in
/-- The identity in $\mathbb R$ behind the headline: the product formula for $\det g$ and $\det H_{T_0}$, with the
convergence factors $\lambda_v$ carried along. -/
theorem frameDensity_identity_lam (D : FrameTowerAlg Q₀ hQ n' (cols Ξ.1)) (hT : T₀.Nondegenerate)
    (lam : HeightOneSpectrum (𝓞 F) → ℝ) (hm : Multipliable fun v => frameLocFactor Q₀ hQ T₀ Ξ D hT v * lam v) :
    cF F (r + n') * ((∏ w : {w : InfinitePlace F // w.IsReal},
        (|σR w (algebraMap (𝓞 F) F T₀.hessian.det)| ^ n')⁻¹) *
        ∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ (2 * n'))⁻¹) *
      ((∏ w : {w : InfinitePlace F // w.IsReal}, |σR w (towerAdapted Q₀ hQ T₀ Ξ D hT).g.val.det| ^ (n' + 1)) *
        (∏ w : {w : InfinitePlace F // w.IsComplex}, ‖σC w (towerAdapted Q₀ hQ T₀ Ξ D hT).g.val.det‖ ^ (2 * (n' + 1))) /
        cF F n') * ∏' v, frameLocFactor Q₀ hQ T₀ Ξ D hT v * lam v =
      |(discr F : ℝ)| ^ (-(((r + n' : ℕ) : ℝ) * ((r + n' : ℕ) - 1) - (n' : ℝ) * (n' - 1)) / 4) *
        ∏' v, NF.localDensityForm v Q₀ T₀ * lam v := by
  set g := (towerAdapted Q₀ hQ T₀ Ξ D hT).g.val.det with hgdef
  set h := algebraMap (𝓞 F) F T₀.hessian.det with hhdef
  have hg : g ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)).ne_zero
  have hh : h ≠ 0 := algebraMap_det_ne_zero T₀ hT
  have ha : ∀ v : HeightOneSpectrum (𝓞 F), ‖σV v g‖ ≠ 0 := fun v => norm_ne_zero_iff.2 ((map_ne_zero _).2 hg)
  have hb : ∀ v : HeightOneSpectrum (𝓞 F), ‖σV v h‖ ≠ 0 := fun v => norm_ne_zero_iff.2 ((map_ne_zero _).2 hh)
  have hfa := mulSupport_finite_norm (F := F) hg
  have hfb := mulSupport_finite_norm (F := F) hh
  have hpow : ∀ (f : HeightOneSpectrum (𝓞 F) → ℝ) (k : ℕ), (Function.mulSupport f).Finite →
      (Function.mulSupport fun v => f v ^ k).Finite := fun f k hf => hf.subset fun v hv => by
    intro h1
    apply hv
    show f v ^ k = 1
    rw [show f v = 1 from h1, one_pow]
  set u : HeightOneSpectrum (𝓞 F) → ℝ := fun v => ‖σV v h‖ ^ n' * (‖σV v g‖ ^ (n' + 1))⁻¹ with hu
  have hpa := hpow _ (n' + 1) hfa
  have hpb := hpow _ n' hfb
  have hpai : (Function.mulSupport fun v => (‖σV v g‖ ^ (n' + 1))⁻¹).Finite := by
    refine hpa.subset fun v hv => ?_
    intro h1
    apply hv
    show (‖σV v g‖ ^ (n' + 1))⁻¹ = 1
    rw [show ‖σV v g‖ ^ (n' + 1) = 1 from h1, inv_one]
  have hufin : (Function.mulSupport u).Finite := by
    refine (hpb.union hpai).subset fun v hv => ?_
    by_contra hcon
    apply hv
    simp only [Set.mem_union, Function.mem_mulSupport, not_or, not_not] at hcon
    show u v = 1
    simp only [hu, hcon.1, hcon.2, one_mul]
  have hUval : ∏' v, u v = (∏' v, ‖σV v h‖) ^ n' * ((∏' v, ‖σV v g‖) ^ (n' + 1))⁻¹ := by
    rw [tprod_eq_finprod hufin, tprod_eq_finprod hfa, tprod_eq_finprod hfb, finprod_mul_distrib hpb hpai,
      finprod_inv_distrib, finprod_pow hfb, finprod_pow hfa]
  have hβ : ∀ v, NF.localDensityForm v Q₀ T₀ * lam v = (frameLocFactor Q₀ hQ T₀ Ξ D hT v * lam v) * u v :=
    fun v => by
      have := ha v
      have := hb v
      simp only [frameLocFactor, hu]
      rw [← hgdef, ← hhdef]
      field_simp
  have hprod : ∏' v, NF.localDensityForm v Q₀ T₀ * lam v =
      (∏' v, frameLocFactor Q₀ hQ T₀ Ξ D hT v * lam v) * ∏' v, u v := by
    rw [tprod_congr hβ]
    exact hm.tprod_mul (multipliable_of_hasFiniteMulSupport hufin)
  have hPg := prod_places_mul_tprod (F := F) hg
  have hPh := prod_places_mul_tprod (F := F) hh
  set Gs := (∏ w : {w : InfinitePlace F // w.IsReal}, |σR w g|) *
    ∏ w : {w : InfinitePlace F // w.IsComplex}, ‖σC w g‖ ^ 2 with hGs
  set Hs := (∏ w : {w : InfinitePlace F // w.IsReal}, |σR w h|) *
    ∏ w : {w : InfinitePlace F // w.IsComplex}, ‖σC w h‖ ^ 2 with hHs
  have hGne : Gs ≠ 0 := left_ne_zero_of_mul_eq_one hPg
  have hHne : Hs ≠ 0 := left_ne_zero_of_mul_eq_one hPh
  have hA : ∏' v, ‖σV v g‖ = Gs⁻¹ := eq_inv_of_mul_eq_one_right hPg
  have hB : ∏' v, ‖σV v h‖ = Hs⁻¹ := eq_inv_of_mul_eq_one_right hPh
  have h1 : (∏ w : {w : InfinitePlace F // w.IsReal}, (|σR w h| ^ n')⁻¹) *
      (∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w h‖ ^ (2 * n'))⁻¹) = (Hs ^ n')⁻¹ := by
    rw [Finset.prod_inv_distrib, Finset.prod_inv_distrib, Finset.prod_pow, ← mul_inv, hHs, mul_pow,
      ← Finset.prod_pow, ← Finset.prod_pow]
    simp_rw [← pow_mul]
  have h2 : (∏ w : {w : InfinitePlace F // w.IsReal}, |σR w g| ^ (n' + 1)) *
      (∏ w : {w : InfinitePlace F // w.IsComplex}, ‖σC w g‖ ^ (2 * (n' + 1))) = Gs ^ (n' + 1) := by
    rw [hGs, mul_pow, ← Finset.prod_pow, ← Finset.prod_pow]
    simp_rw [← pow_mul]
  have hcd : cF F (r + n') / cF F n' =
      |(discr F : ℝ)| ^ (-(((r + n' : ℕ) : ℝ) * ((r + n' : ℕ) - 1) - (n' : ℝ) * (n' - 1)) / 4) := by
    unfold cF
    rw [← Real.rpow_sub (abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero F))]
    congr 1
    ring
  have hcn : cF F n' ≠ 0 := (cF_pos' _).ne'
  rw [hprod, hUval, hA, hB, h1, h2, ← hcd]
  simp only [inv_pow, inv_inv]
  field_simp

end Identity

end QuadFormsKB.Tamagawa.Indefinite.IsoAlg
