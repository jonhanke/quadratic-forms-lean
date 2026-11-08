/-
# The conductor at a non-dyadic ramified place; Gan–Hanke–Yu Prop. 7.5 from the dyadic places alone

W. T. Gan, J. Hanke, J.-K. Yu, *On an exact mass formula of Shimura*, Duke Math. J. 107 (2001), Lemma A.1(iv), (6.5),
(6.13), Prop. 7.5; O. T. O'Meara, *Introduction to quadratic forms*, §63.

At a non-dyadic place $v$ ramified in $F_v(\sqrt x)$ (i.e. $x$ of odd order):
* the conductor exponent is $f_v = 1$ (`condExp_eq_one`): a unit $\equiv1 \bmod \pi$ is a square (local square theorem),
  hence a norm; and some unit is not a norm (nondegeneracy of the Hilbert symbol, `SqDual.hilbCl_nondeg_fin`, with
  $(\pi\varepsilon,\pi)(\pi\varepsilon,-\varepsilon) = (\pi\varepsilon,-\pi\varepsilon) = 1$);
* for even $n\ge4$ and $\mathcal O_F^n$ maximal, $[\widetilde\Lambda_v:\Lambda_v] = q_v$ (`dualIndexAt_ram_nondyadic`; Jordan shape
  $\langle u\rangle\perp\pi W$ with $b = 1$, `oddMaximalShape_at`).

Hence the named input `RamifiedDualIndexConductor` of Gan–Hanke–Yu Prop. 7.5 holds at every non-dyadic place, and it shrinks to its
dyadic part `RamifiedDualIndexConductorDyadic` (`ramifiedDualIndexConductor_of_dyadic`, `ghy_prop75_of_dyadic`).
-/
import QuadFormsKB.Literature.Hanke2005.GHYMassFormulaEven
import QuadFormsKB.Literature.OMeara.Sec63Rest

open NumberField IsDedekindDomain
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.Tamagawa.LatChange

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem hilbertSymbol_sq_right' (K : Type*) [Field K] (x a : K) : hilbertSymbol K x (a ^ 2) = 1 := by
  unfold hilbertSymbol
  rw [if_pos]
  exact ⟨0, 1, a, by simp, by ring⟩

theorem hilbertSymbol_neg_self' (K : Type*) [Field K] (a : K) : hilbertSymbol K a (-a) = 1 := by
  unfold hilbertSymbol
  rw [if_pos]
  exact ⟨1, 1, 0, by simp, by ring⟩

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The conductor exponent at a non-dyadic ramified place is $1$** (Gan–Hanke–Yu 2001, Lemma A.1(iv) with $d = 1$; O'Meara §63). -/
@[kb "ganhankeyu2001" "Lemma A.1(iv), p. 123 (non-dyadic case: f = d = 1)"]
theorem condExp_eq_one (h2 : IsUnit (2 : 𝔬)) {x : Fv} (hx : x ≠ 0) (hr : ¬ IsUnramSqrt v x) : condExp v x = 1 := by
  classical
  have hπ := NF.irreducible_π v
  have hπ2 : ¬ NF.π v ∣ 2 := DensitySD.not_dvd_two v h2
  have hcoe : ∀ u : 𝔬, algebraMap 𝔬 Fv u = (u : Fv) := fun _ => rfl
  have P1 : ∀ u : 𝔬, IsUnit u → NF.π v ^ 1 ∣ u - 1 → hilbertSymbol Fv x (u : Fv) = 1 := by
    intro u _ hd
    obtain ⟨a, ha⟩ := LocalZeta.exists_sq_of_dvd_sub_one v hπ2 (by simpa using hd)
    rw [ha]; push_cast; exact hilbertSymbol_sq_right' _ x _
  have hex : ∃ c : ℕ, ∀ u : 𝔬, IsUnit u → NF.π v ^ c ∣ u - 1 → hilbertSymbol Fv x (u : Fv) = 1 := ⟨1, P1⟩
  have h4 : IsUnit (4 : 𝔬) := by
    rw [show (4 : 𝔬) = 2 * 2 by norm_num]; exact h2.mul h2
  -- `x` is not a unit times a square
  have hnu : x ∉ OMeara.unitSqClass 𝔬 Fv := by
    rintro ⟨ε, hε, z, hz, rfl⟩
    apply hr
    obtain ⟨i4, hi4⟩ : ∃ i4 : 𝔬, 4 * i4 = 1 := ⟨_, h4.mul_val_inv⟩
    refine ⟨z⁻¹, inv_ne_zero hz, (ε - 1) * i4, ?_, ?_⟩
    · rw [show 1 + 4 * ((ε - 1) * i4) = ε by linear_combination (ε - 1) * hi4]; exact hε
    · have hi4' : (4 : Fv) * (i4 : Fv) = 1 := by
        have := congrArg (fun t : 𝔬 => (t : Fv)) hi4
        simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
        rwa [show ((4 : 𝔬) : Fv) = 4 from map_ofNat (algebraMap 𝔬 Fv) 4] at this
      rw [hcoe]
      push_cast
      field_simp
      linear_combination (-(ε : Fv) + 1) * hi4'
  have hodd : x ∈ OMeara.primeUnitSqClass (F := Fv) hπ := by
    rw [OMeara.mem_primeUnitSqClass_iff]
    refine ⟨hx, ?_⟩
    by_contra hne
    exact hnu ((OMeara.mem_unitSqClass_iff hπ).2 ⟨hx, Int.not_odd_iff_even.mp hne⟩)
  obtain ⟨ε, hε, z, hz, hxe⟩ := hodd
  have hπ0 : algebraMap 𝔬 Fv (NF.π v) ≠ 0 := pi_ne_zero_Fv v
  have hε0 : algebraMap 𝔬 Fv ε ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).mpr hε.ne_zero
  -- a unit `u` with `(x, u) = -1`
  have hns : ¬ IsSquare x := by
    rintro ⟨s, hs⟩
    apply hr
    have hs0 : s ≠ 0 := by rintro rfl; exact hx (by simpa using hs)
    exact ⟨s⁻¹, inv_ne_zero hs0, 0, by simp, by rw [hs]; field_simp; simp⟩
  obtain ⟨y, hy⟩ := SqDual.hilbCl_nondeg_fin v (QuotientGroup.mk (Units.mk0 x hx)) (fun h1 =>
    hns ((SqDual.mk_eq_one_iff_isSquare _ _).mp h1))
  induction y using QuotientGroup.induction_on with
  | H c =>
  have hcx : hilbertSymbol Fv x (c : Fv) = -1 := by
    rw [hilbertSymbol_comm]; exact hy
  have hc0 : (c : Fv) ≠ 0 := c.ne_zero
  have key : ∃ u : 𝔬, IsUnit u ∧ hilbertSymbol Fv x (u : Fv) = -1 := by
    by_cases hce : Even (OMeara.dord hπ (c : Fv))
    · obtain ⟨ε', hε', z', hz', hc'⟩ := (OMeara.mem_unitSqClass_iff hπ).2 ⟨hc0, hce⟩
      refine ⟨ε', hε', ?_⟩
      rw [hc', SqDual.hilbertSymbol_mul_sq_right _ _ _ _ hz'] at hcx
      exact hcx
    · obtain ⟨ε', hε', z', hz', hc'⟩ :=
        (OMeara.mem_primeUnitSqClass_iff hπ).2 ⟨hc0, Int.not_even_iff_odd.mp hce⟩
      have hε'0 : algebraMap 𝔬 Fv ε' ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).mpr hε'.ne_zero
      rw [hc', SqDual.hilbertSymbol_mul_sq_right _ _ _ _ hz',
        OMeara.hilbertSymbol_mul_right_finite v hx hπ0 hε'0] at hcx
      by_cases hu' : hilbertSymbol Fv x (algebraMap 𝔬 Fv ε') = -1
      · exact ⟨ε', hε', hu'⟩
      · have hu1 : hilbertSymbol Fv x (algebraMap 𝔬 Fv ε') = 1 :=
          (HN.hilbertSymbol_eq_one_or Fv _ _).resolve_right hu'
        have hpi : hilbertSymbol Fv x (algebraMap 𝔬 Fv (NF.π v)) = -1 := by
          rw [hu1, mul_one] at hcx; exact hcx
        refine ⟨-ε, hε.neg, ?_⟩
        have hxπε : algebraMap 𝔬 Fv (NF.π v) * algebraMap 𝔬 Fv ε ≠ 0 := mul_ne_zero hπ0 hε0
        -- `(πε, π) (πε, -ε) = (πε, -πε) = 1`
        have hprod := hilbertSymbol_neg_self' Fv (algebraMap 𝔬 Fv (NF.π v) * algebraMap 𝔬 Fv ε)
        rw [show -(algebraMap 𝔬 Fv (NF.π v) * algebraMap 𝔬 Fv ε) =
            algebraMap 𝔬 Fv (NF.π v) * (-algebraMap 𝔬 Fv ε) by ring,
          OMeara.hilbertSymbol_mul_right_finite v hxπε hπ0 (neg_ne_zero.mpr hε0)] at hprod
        rw [hxe, HN.hilbertSymbol_mul_sq_left _ _ _ _ hz] at hpi
        rw [hpi, neg_one_mul, neg_eq_iff_eq_neg] at hprod
        rw [hxe, HN.hilbertSymbol_mul_sq_left _ _ _ _ hz]
        push_cast
        exact hprod
  obtain ⟨u, hu, hux⟩ := key
  have P0 : ¬ ∀ u : 𝔬, IsUnit u → NF.π v ^ 0 ∣ u - 1 → hilbertSymbol Fv x (u : Fv) = 1 := fun h => by
    have := h u hu (by simp)
    rw [hux] at this
    norm_num at this
  unfold condExp
  rw [dif_pos hex, Nat.find_eq_iff]
  refine ⟨P1, fun m hm => ?_⟩
  obtain rfl : m = 0 := by omega
  exact P0

/-- **The dual index at a non-dyadic ramified place is $q$** (even $n\ge4$, $\mathcal O_F^n$ maximal; Jordan shape with
$b = 1$). -/
@[kb "ganhankeyu2001" "(6.5), (6.13) (dual index at a ramified non-dyadic place)"]
theorem dualIndexAt_ram_nondyadic (hn : 4 ≤ n) (heven : Even n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hmax : StdIsMaximal Q₀) (h2 : IsUnit (2 : 𝔬)) (hr : IsRamifiedAt v Q₀) :
    dualIndexAt v Q₀ = (normQ v) ^ 1 := by
  have h1 : dualIndexAt v Q₀ ≠ 1 := fun h => (not_isRamifiedAt_of_dualIndexAt_eq_one v Q₀ heven h) hr
  obtain ⟨a, b, h, u, W, T, hu, hW, hT, hb, hχW, hequiv, hb1, hb2⟩ :=
    oddMaximalShape_at (by omega) Q₀ hQ hmax v h2 h1
  subst h
  have hπ := NF.irreducible_π v
  have hq := DensitySD.q_eq v
  obtain ⟨U, hU, hUe⟩ := hequiv
  obtain ⟨w, hwc, hD2⟩ := det_shape v h2 u hu W T hW hT (NF.Qp v Q₀) ⟨U, hU, hUe⟩
  set D := (NF.Qp v Q₀).hessian.det with hDdef
  have hnorm : ‖((D : 𝔬) : Fv)‖ = ((DVR.q 𝔬 : ℝ) ^ b)⁻¹ :=
    norm_coe_of_pow_dvd v ⟨_, hD2⟩ (by
      rw [hD2, pow_succ]
      intro hd
      exact hπ.not_isUnit (isUnit_of_dvd_unit ((mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero)).1 hd) hwc))
  have hdual : dualIndexAt v Q₀ = (normQ v) ^ b := by
    unfold dualIndexAt
    rw [← hDdef, hnorm, inv_inv, hq]
  rcases hb with rfl | rfl
  · exact hdual
  · exact absurd hr (hb2 rfl).1

end Local

/-- **The dyadic part of `RamifiedDualIndexConductor`** (a **named input**; Gan–Hanke–Yu 2001, Lemma A.1(iv), (6.5), (6.13)): the
statement of `RamifiedDualIndexConductor` at the dyadic places only (the non-dyadic places are proved,
`condExp_eq_one`, `dualIndexAt_ram_nondyadic`). Field: `dual_eq`. -/
@[kb "ganhankeyu2001" "Lemma A.1(iv), p. 123; (6.5), (6.13) (dyadic places)"]
structure RamifiedDualIndexConductorDyadic (F : Type) [Field F] [NumberField F] : Prop where
  /-- $[\widetilde\Lambda_v:\Lambda_v] = q_v^{f_v}$ at a ramified dyadic place. -/
  dual_eq : ∀ {n : ℕ}, 4 ≤ n → Even n → ∀ Q₀ : QuadForm (𝓞 F) n, Q₀.Nondegenerate → StdIsMaximal Q₀ →
    ∀ v : HeightOneSpectrum (𝓞 F), ¬ IsUnit (2 : v.adicCompletionIntegers F) → IsRamifiedAt v Q₀ →
      dualIndexAt v Q₀ = (normQ v) ^ condExp v (algebraMap F (v.adicCompletion F) (discK Q₀))

/-- **`RamifiedDualIndexConductor` from its dyadic part.** -/
@[kb "ganhankeyu2001" "Lemma A.1(iv), p. 123 (non-dyadic places proved)"]
theorem ramifiedDualIndexConductor_of_dyadic (I : RamifiedDualIndexConductorDyadic F) :
    RamifiedDualIndexConductor F := by
  refine ⟨fun {n} hn heven Q₀ hQ hmax v hr => ?_⟩
  by_cases h2 : IsUnit (2 : v.adicCompletionIntegers F)
  · have hd : algebraMap F (v.adicCompletion F) (discK Q₀) ≠ 0 := by
      rw [map_ne_zero_iff _ (algebraMap F (v.adicCompletion F)).injective]
      unfold discK
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (hessian_det_F_ne_zero Q₀ hQ)
    rw [condExp_eq_one v h2 hd hr]
    exact dualIndexAt_ram_nondyadic v hn heven Q₀ hQ hmax h2 hr
  · exact I.dual_eq hn heven Q₀ hQ hmax v h2 hr

/-- **Gan–Hanke–Yu 2001, Proposition 7.5, conditional only on the dyadic places** of the conductor input. -/
@[kb "ganhankeyu2001" "Proposition 7.5, p. 119 (conditional on the dyadic conductor input)"]
theorem ghy_prop75_of_dyadic [IsTotallyReal F] (I : RamifiedDualIndexConductorDyadic F) (hn : 4 ≤ n) (heven : Even n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hmax : StdIsMaximal Q₀) :
    ∑' i : DC Q₀, ((Nat.card (unitGroup Q₀ i) : ℝ≥0∞))⁻¹ =
      ENNReal.ofReal (((2 : ℝ) ^ ((n / 2) * Module.finrank ℚ F))⁻¹ * lMotiveEven Q₀ (n / 2) * 2 *
        ∏' v : HeightOneSpectrum (𝓞 F), lambdaGHYEvenAt v Q₀) :=
  ghy_prop75 (ramifiedDualIndexConductor_of_dyadic I) hn heven Q₀ hQ hpd hmax

end QuadFormsKB.Hanke2005
