import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqGeneral
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSiegelTotallyReal

/-!
# `GnatTamagawaComparison F` for every number field, up to the indefinite non-square models

**Layer:** $F$ any number field. The input `GnatTamagawaComparison F`
(Weil 1982, Thm 2.3.1 for $G^\natural\to SO(V)$, $m = 4$) has two fields, the square model and the non-square model.

* **Square model: proved for every number field** (`map_muP_sqPEquiv_eq_muTam_any`, `gnatTamagawaComparison_square_any`):
  every quaternion algebra $\mathbb H[F,a,b]$, every signature, complex places allowed.
* **Non-square model:** proved when $F$ is totally real and $-a, -b, d\gg0$ (`gnatMeasureComparisonNS`). The other
  non-square models are the named input
  - **`GnatMeasureComparisonNSIndef F`**: $\Phi_*\mu_P = \mu_{\mathrm{Tam}}$ for $\Phi$ = `nsPEquiv` and every non-square model
    that is *not* totally definite over a totally real field.

  It is a statement about two explicit Haar measures on two explicit groups (no covolume, no Tamagawa number), so it is not
  equivalent to any $\tau = 2$ statement; what it needs is the archimedean local ratio of the spin covering
  $\mathrm{SL}_1(D\otimes E_w)\to SO(V_0)(F_w)$ at the real places with $E_w = \mathbb R\times\mathbb R$ or $\mathbb C$ and at the complex
  places.

* **`gnatMeasureComparison_of_nsIndef`**, **`gnatTamagawaComparison_of_nsIndef`**: `GnatMeasureComparison F` and
  `GnatTamagawaComparison F` from the input.
-/

open MeasureTheory NumberField NumberField.InfinitePlace

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa

variable {F : Type} [Field F] [NumberField F]

/-- **The square field of `GnatTamagawaComparison F`, for every number field**: the isomorphism $\Phi$ = `sqPEquiv` carries
$\pi(\Gamma)$ onto $SO(V)(F)$ and $\mu_P$ onto `muTam` (`map_muP_sqPEquiv_eq_muTam_any`). -/
@[kb "weil1982" "Thm 2.3.1 (local ratios, ∏ r_v = 1) and §3.7, pp. 64-65 [unverified page]"]
theorem gnatTamagawaComparison_square_any (a b : 𝓞 F) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hQ : (qSq a b).Nondegenerate) :
    ∃ Φ : (gnatSqO ha0 hb0).P ≃ₜ* SOAdele (qSq a b),
      (gnatSqO ha0 hb0).gamP.map Φ.toMulEquiv.toMonoidHom = GammaSOAdele (qSq a b) ∧
      ((gnatSqO ha0 hb0).muP (muSq ha0 hb0)).map Φ = muTam (qSq a b) hQ (fun _ => 1) :=
  ⟨sqPEquiv ha0 hb0, map_gamP_sqPEquiv ha0 hb0, map_muP_sqPEquiv_eq_muTam_any ha0 hb0 hQ⟩

variable (F) in
/-- **Input (named): Weil's local-ratio identity for the non-square model, indefinite cases** (Weil 1982, Thm 2.3.1 and
§3.7, pp. 64–65 [unverified page]).

Field `nonsquare`: for $a, b, d\in\mathcal O_F$, every number field $K\supseteq F$ with an $F$-basis $(1,\delta)$, $\delta^2 = d$,
$\alpha = a$, $\beta = b$ in $\mathcal O_K$, $\alpha,\beta\neq0$, $Q_0 = \langle1,-ad,-bd,abd\rangle$ (`qNS a b d`) nondegenerate, **unless**
$F$ is totally real and $-a, -b, d$ are totally positive (that case is the theorem `gnatMeasureComparisonNS`):
$\Phi_*\mu_P = \mu_{\mathrm{Tam}}$ for $\Phi$ = `nsPEquiv`.

*Hypothesis hygiene.* An identity between two explicit Haar measures; no covolume, Tamagawa number or representation number
occurs, so it is not equivalent to `TamagawaNumberTwoAdelic` or `RankFourUnitSiegel`. -/
@[kb "weil1982" "Thm 2.3.1 (local ratios) and §3.7, pp. 64-65 [unverified page]"]
structure GnatMeasureComparisonNSIndef : Prop where
  nonsquare : ∀ (a b d : 𝓞 F) (K : Type) [Field K] [NumberField K] [Algebra F K]
    (bK : Module.Basis (Fin 2) F K) (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
    (α β : 𝓞 K) (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))
    (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (hQ : (qNS a b d).Nondegenerate),
    ¬ (IsTotallyReal F ∧ IsTotallyPos (-(a : F)) ∧ IsTotallyPos (-(b : F)) ∧ IsTotallyPos (d : F)) →
    ((gnatBCO bK 0 hb₀ hα0 hβ0).muP (muBC bK 0 hb₀ hα0 hβ0)).map
      (nsPEquiv hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) (ne_zero_of_algebraMap_eq hα hα0)
        (ne_zero_of_algebraMap_eq hβ hβ0) (d_ne_zero_of_basis hb₁)) = muTam (qNS a b d) hQ (fun _ => 1)

/-- **`GnatMeasureComparison F` from the indefinite non-square input** (the square half and the totally definite non-square
models are theorems). -/
@[kb "weil1982" "Thm 2.3.1 [unverified page]"]
theorem gnatMeasureComparison_of_nsIndef (h : GnatMeasureComparisonNSIndef F) : GnatMeasureComparison F := by
  refine ⟨fun a b ha0 hb0 hQ => map_muP_sqPEquiv_eq_muTam_any ha0 hb0 hQ, ?_⟩
  intro a b d K _ _ _ bK hb₀ hb₁ α β hα hβ hα0 hβ0 hQ
  by_cases hdef : IsTotallyReal F ∧ IsTotallyPos (-(a : F)) ∧ IsTotallyPos (-(b : F)) ∧ IsTotallyPos (d : F)
  · obtain ⟨hTR, hna, hnb, hdpos⟩ := hdef
    exact (gnatMeasureComparisonNS F).nonsquare a b d K bK hb₀ hb₁ α β hα hβ hα0 hβ0 hna hnb hdpos hQ
  · exact h.nonsquare a b d K bK hb₀ hb₁ α β hα hβ hα0 hβ0 hQ hdef

/-- **`GnatTamagawaComparison F` from the indefinite non-square input.** -/
@[kb "weil1982" "Thm 2.3.1, §3.7, pp. 64-65 [unverified page]"]
theorem gnatTamagawaComparison_of_nsIndef (h : GnatMeasureComparisonNSIndef F) : GnatTamagawaComparison F :=
  gnatTamagawaComparison_of_measure (gnatMeasureComparison_of_nsIndef h)

/-- Over a totally real field, the input holds for the totally definite models (so `GnatMeasureComparisonNSIndef F` is
exactly the statement for the remaining ones). -/
theorem nsIndef_input_scope [IsTotallyReal F] {a b d : 𝓞 F} (hna : IsTotallyPos (-(a : F)))
    (hnb : IsTotallyPos (-(b : F))) (hdpos : IsTotallyPos (d : F)) :
    IsTotallyReal F ∧ IsTotallyPos (-(a : F)) ∧ IsTotallyPos (-(b : F)) ∧ IsTotallyPos (d : F) :=
  ⟨inferInstance, hna, hnb, hdpos⟩

end QuadFormsKB.Tamagawa.Measure.Weil

end
