/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.SiegelLatRanks
import QuadFormsKB.Tamagawa.BinaryTauNF

/-!
# G4: Siegel's formula in rank 3 for every genus, every totally real field

**Layer:** $F$ totally real (any class number); $Q_0$ a totally positive definite ternary form over $\mathcal O_F$; $L$ an **arbitrary**
$\mathcal O_F$-lattice on $(F^3, Q_0)$ with $Q_0$ integral on $L$ (any Steinitz class); $m \in \mathcal O_F$ totally positive.

In rank $3$ the plain product $\prod_\mathfrak p\beta_\mathfrak p$ does not converge unconditionally, so, as for $\mathcal O_F^3$ (
`siegelProduct3`), the lattice product is the regularized product with the **same** character $\chi_m$ = `chiTern Q₀ m`:
$$S_3(L, m) = |d_F|^{-1}\prod_\sigma\beta_\sigma(m)\cdot L_F(1,\chi_m)\prod_\mathfrak p\beta_\mathfrak p(L, m)\bigl(1-\chi_m(\mathfrak p)N\mathfrak p^{-1}\bigr)$$
(`siegelProduct3Lat`); $\beta_\mathfrak p(L, m) = \beta_\mathfrak p(\mathcal O_F^3, m)$ at the almost all primes where $L_\mathfrak p = \mathfrak o_\mathfrak p^3$
(`latBeta_eq_of_loc_std`), so the corrected product converges.

**Proves**
* `two_mul_tamagawaKLat_mul_repMass_frame3`: $2\,\mu_{\mathrm{Tam}}(K_{SO}(L))\,\mathrm{repMass}(L, m) = \tau^{\mathrm{reg}}(SO(Q_0'))\cdot S_3(L, m)$ for
  every adapted frame (`two_mul_tamagawaK_mul_repMass_frame3` for an arbitrary lattice; local input
  `latOrbitalIdentity`);
* **`siegelFormulaAt3Lat_totallyReal`** (headline, unconditional): `SiegelFormulaAt3Lat Q₀ L m`; for $L = \mathcal O_F^3$ it is
  `siegelFormulaAt3_nf_uncond` (`siegelFormulaAt3Lat_std_iff`).

Sources: Weil 1982, §4.5, p. 100 and p. 109 [unverified]; Siegel 1935, Hauptsatz ($n = 3$; over $F$ [unverified]).
-/

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.SiegelLat

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.LocalDensity QuadFormsKB.QuadForm
open QuadFormsKB.HilbertModular LatChange QuadFormsKB.NFEuler QuadFormsKB.RegProd

variable {F : Type} [Field F] [NumberField F]

/-- $\beta_\mathfrak p(L, m) = \beta_\mathfrak p(\mathcal O_F^N, m)$ where $L_\mathfrak p = \mathfrak o_\mathfrak p^N$. -/
theorem latBeta_eq_of_loc_std [IsTotallyReal F] {N : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) N)
    (L : Lat F N) (hLi : Lattices.IsIntegral (formF Q₀) L.1) (h : loc v L.1 = std v) (m : 𝓞 F) :
    latBeta v Q₀ L m = NF.localDensity v Q₀ m := by
  rcases N with _ | N
  · -- rank 0: every lattice is `intVec`
    have hL : L = stdLat F 0 := Subtype.ext (Subsingleton.elim _ _)
    subst hL; exact latBeta_std v Q₀ m
  obtain ⟨A, hA⟩ := exists_isLocModel v L
  have hint := hA.isIntegral v hLi
  rw [latBeta_eq v Q₀ L hA hint, normDet_mul_localDensity_eq v Q₀ hint (isIntegral_latOf_one Q₀)
    (by rw [hA.2, h, HilbertModular.latOf_one, loc_intVec]), gramZ_one, Units.val_one, det_one, map_one, norm_one,
    one_mul]

/-- **The rank-3 Siegel product of an arbitrary lattice** (regularized, with the character $\chi_m$ = `chiTern Q₀ m` of
$\mathcal O_F^3$): `siegelProductWith Q₀ m (regProd (chiTern Q₀ m) 1 β(L, ·))`. For $L = \mathcal O_F^3$ it is `siegelProduct3`. -/
@[kb "siegel1935" "Hauptsatz, n = 3 (local side, regularized, arbitrary lattice; over F [unverified])"]
def siegelProduct3Lat (Q₀ : QuadForm (𝓞 F) 3) (L : Lat F 3) (m : 𝓞 F) : ℝ :=
  siegelProductWith Q₀ m (regProd (chiTern Q₀ m) 1 fun v => latBeta v Q₀ L m)

theorem siegelProduct3Lat_std [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) 3) (m : 𝓞 F) :
    siegelProduct3Lat Q₀ (stdLat F 3) m = siegelProduct3 Q₀ m := by
  unfold siegelProduct3Lat siegelProduct3; simp_rw [latBeta_std]

/-- **Siegel's formula in rank 3 for the genus of an arbitrary lattice $L$** (regularized product):
$$\sum_{\mathrm{cls}M\subseteq\mathrm{gen}L}\frac{r_M(m)}{|O(M)|} = \mathrm{Mass}(L)\cdot S_3(L, m).$$

Field:
- `repMass_eq`: `repMass (formF Q₀) L m = mass (formF Q₀) L * siegelProduct3Lat Q₀ L m`.

For $L = \mathcal O_F^3$ it is `SiegelFormulaAt3 Q₀ m` (`siegelFormulaAt3Lat_std_iff`). A statement (a conclusion), never assumed. -/
@[kb "siegel1935" "Hauptsatz, n = 3 (arbitrary lattice; over F [unverified])"]
structure SiegelFormulaAt3Lat (Q₀ : QuadForm (𝓞 F) 3) (L : Lat F 3) (m : 𝓞 F) : Prop where
  repMass_eq : repMass (formF Q₀) L (algebraMap (𝓞 F) F m) = mass (formF Q₀) L * siegelProduct3Lat Q₀ L m

theorem siegelFormulaAt3Lat_std_iff [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) 3) (m : 𝓞 F) :
    SiegelFormulaAt3Lat Q₀ (stdLat F 3) m ↔ SiegelFormulaAt3 Q₀ m := by
  constructor
  · intro h; exact ⟨by rw [← siegelProduct3Lat_std]; exact h.repMass_eq⟩
  · intro h; exact ⟨by rw [siegelProduct3Lat_std]; exact h.repMass_eq⟩

variable [IsTotallyReal F]

/-- **The rank-3 frame identity for an arbitrary lattice** (Weil 1982, §4.5, p. 100 and p. 109 [unverified], $N = 3$):
$$2\,\mu_{\mathrm{Tam}}(K_{SO}(L))\cdot\mathrm{repMass}(L, m) = \tau^{\mathrm{reg}}(SO(Q_0'))\cdot S_3(L, m).$$
the proof with `latOrbitalIdentity` and the index ratios $r_\mathfrak p(L)$ of `tamagawaKLat_eq_finprod`. -/
@[kb "weil1982" "§4.5, p. 100 and p. 109 (N = 3, regularized, arbitrary lattice) [unverified]"]
theorem two_mul_tamagawaKLat_mul_repMass_frame3 (Q₀ : QuadForm (𝓞 F) (2 + 1)) (hpd : IsTotallyPosDef (formF Q₀))
    (L : Lat F (2 + 1)) (hLi : Lattices.IsIntegral (formF Q₀) L.1)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (fr : AdaptedFrame (formF Q₀) (algebraMap (𝓞 F) F m)) :
    2 * tamagawaKLat Q₀ L * repMass (formF Q₀) L (algebraMap (𝓞 F) F m) =
      tauSOReg fr.Q' * siegelProduct3Lat Q₀ L m := by
  classical
  have hρ : (algebraMap (𝓞 F) F m) ≠ 0 :=
    (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (ne_zero_of_totallyPos hm)
  have hQF : (formF Q₀).Nondegenerate := hpd.nondegenerate
  have hQ₀ : Q₀.Nondegenerate := nondegenerate_of_map hQF
  have hQ'nd : fr.Q'.Nondegenerate := fr.nondegenerate hQF hρ
  have hpd' : IsTotallyPosDef (formF fr.Q') := by
    have h1 := isTotallyPosDef_compMat (formF Q₀) fr.g hpd
    rw [fr.compMat_eq] at h1
    exact isTotallyPosDef_of_splitForm h1
  set QF' := fr.Q'.map (algebraMap (𝓞 F) F)
  -- the local factors
  set W0 : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    locTypeSumG v (algebraMap (𝓞 F) F m) QF' (loc v (glImage fr.g⁻¹ L.1)) (algebraMap F (v.adicCompletion F) 1)
  set r : HeightOneSpectrum (𝓞 F) → ℝ := fun v => locRatio v Q₀ L
  set α : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.siegelDensity v Q₀ Q₀
  set α' : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.siegelDensity v fr.Q' fr.Q'
  set E : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (2 + 1) / ‖algebraMap F (v.adicCompletion F) (2 * (algebraMap (𝓞 F) F m))‖ ^ 2
  set β : HeightOneSpectrum (𝓞 F) → ℝ := fun v => latBeta v Q₀ L m
  have hEpos : ∀ v, 0 < E v := fun v => by
    have h1 : algebraMap F (v.adicCompletion F) fr.g.val.det ≠ 0 :=
      (map_ne_zero _).mpr (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero
    have h2 : algebraMap F (v.adicCompletion F) (2 * (algebraMap (𝓞 F) F m)) ≠ 0 := (map_ne_zero _).mpr (mul_ne_zero two_ne_zero hρ)
    exact div_pos (pow_pos (norm_pos_iff.mpr h1) _) (pow_pos (norm_pos_iff.mpr h2) _)
  have hαpos : ∀ v, 0 < α v := fun v => siegelDensity_pos v Q₀ hQ₀
  have hα'pos : ∀ v, 0 < α' v := fun v => siegelDensity_pos v fr.Q' hQ'nd
  have hrpos : ∀ v, 0 < r v := fun v => locRatio_pos v hQ₀ L hLi
  have hW : ∀ v, W0 v = α' v * E v * β v / (α v * r v) := by
    intro v
    have hj := latOrbitalIdentity v Q₀ hQ₀ (by norm_num) L hLi rfl hρ fr
    rw [show (2 : v.adicCompletion F) * algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F m) =
      algebraMap F (v.adicCompletion F) (2 * (algebraMap (𝓞 F) F m)) by rw [map_mul, map_ofNat]] at hj
    have hdet : 0 < ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (2 + 1) :=
      pow_pos (norm_pos_iff.mpr ((map_ne_zero _).mpr (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero)) _
    have h2ρ : 0 < ‖algebraMap F (v.adicCompletion F) (2 * (algebraMap (𝓞 F) F m))‖ ^ 2 :=
      pow_pos (norm_pos_iff.mpr ((map_ne_zero _).mpr (mul_ne_zero two_ne_zero hρ))) _
    have hα := hαpos v
    have hr := hrpos v
    simp only [W0, E, α, α', β, r] at hj ⊢
    generalize ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (2 + 1) = D at hj hdet ⊢
    generalize ‖algebraMap F (v.adicCompletion F) (2 * (algebraMap (𝓞 F) F m))‖ ^ 2 = B2 at hj h2ρ ⊢
    rw [eq_div_iff (mul_pos hα hr).ne']
    field_simp at hj ⊢
    linear_combination hj
  -- finite supports
  have hglat : (glImage fr.g⁻¹ L.1).IsLattice F := glImage_isLattice fr.g⁻¹ L.2
  have hfin₀ : {v : HeightOneSpectrum (𝓞 F) | loc v (glImage fr.g⁻¹ L.1) ≠ std v ∨ v.valuation F (algebraMap (𝓞 F) F m) ≠ 1 ∨
      v.valuation F 2 ≠ 1}.Finite :=
    ((Filter.eventually_cofinite.mp (loc_eventually_std hglat)).union
      ((finite_valuation_ne_one hρ).union (finite_valuation_ne_one (two_ne_zero (α := F))))).subset fun v hv => by
        simpa [or_assoc] using hv
  have hW0fin : Function.HasFiniteMulSupport W0 := by
    refine hfin₀.subset fun v hv => ?_
    by_contra h
    simp only [Set.mem_ofPred_eq, not_or, not_not] at h
    apply hv
    show locTypeSumG v (algebraMap (𝓞 F) F m) QF' (loc v (glImage fr.g⁻¹ L.1)) (algebraMap F (v.adicCompletion F) 1) = 1
    rw [h.1, map_one]
    exact locTypeSumG_std_one_of_units v fr.Q' hQ'nd h.2.1 h.2.2
  have hrfin : Function.HasFiniteMulSupport r := by
    refine (Filter.eventually_cofinite.mp (loc_eventually_std L.2)).subset fun v hv => ?_
    by_contra h
    exact hv (locRatio_eq_one v Q₀ L (by simpa using h))
  have hEfin : Function.HasFiniteMulSupport E := by
    have hdet : fr.g.val.det ≠ 0 := (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero
    refine ((finite_valuation_ne_one hdet).union (finite_valuation_ne_one (mul_ne_zero two_ne_zero hρ))).subset
      fun v hv => ?_
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
    apply hv
    show E v = 1
    simp only [E, norm_algebraMap_eq_one h.1, norm_algebraMap_eq_one h.2, one_pow, div_one]
  have hfp : ∀ {f : HeightOneSpectrum (𝓞 F) → ℝ}, Function.HasFiniteMulSupport f → HasProd f (∏ᶠ v, f v) :=
    fun {f} hf => by
      have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hf).hasProd
      rwa [tprod_eq_finprod hf] at this
  have hfpos : ∀ {f : HeightOneSpectrum (𝓞 F) → ℝ}, Function.HasFiniteMulSupport f → (∀ v, 0 < f v) →
      0 < ∏ᶠ v, f v := fun {f} hf hpos => by
    rw [finprod_eq_prod_of_mulSupport_subset f (s := hf.toFinset) fun v hv => (Set.Finite.mem_toFinset _).mpr hv]
    exact Finset.prod_pos fun v _ => hpos v
  -- the absolutely convergent product
  have hαm : Multipliable α := multipliable_siegelDensity (N := 2 + 1) (by omega) (by omega) Q₀ hQ₀
  have hEprod : 0 < ∏ᶠ v, E v := hfpos hEfin hEpos
  -- the character and the regularized products
  obtain ⟨hL0, hL⟩ := lOne_chiTern_pos hpd hm
  obtain ⟨S, hS⟩ := chiP_frame_eq_chiTern hpd hm fr
  have hχ : ∀ v, |chiTern Q₀ m v| ≤ 1 := fun v => abs_chiTern_le v Q₀ m
  have hlam : ∀ v, 0 < 1 - chiTern Q₀ m v / (normP v : ℝ) := fun v => one_sub_div_pos (hχ v) v
  set g : HeightOneSpectrum (𝓞 F) → ℝ := fun v => α' v * (1 - chiTern Q₀ m v / (normP v : ℝ)) ^ (-1 : ℤ)
  have hgfin : Function.HasFiniteMulSupport g := hasFiniteMulSupport_siegelDensity_binary_reg hQ'nd S hS
  have hgpos : ∀ v, 0 < g v := fun v => mul_pos (hα'pos v) (zpow_pos (hlam v) _)
  have hG : 0 < ∏ᶠ v, g v := hfpos hgfin hgpos
  have hβp : HasProd (fun v => β v * (1 - chiTern Q₀ m v / (normP v : ℝ)) ^ (1 : ℤ))
      ((∏ᶠ v, W0 v) * (∏' v, α v) * (∏ᶠ v, r v) / ((∏ᶠ v, E v) * ∏ᶠ v, g v)) := by
    refine ((((hfp hW0fin).mul hαm.hasProd).mul (hfp hrfin)).div₀ ((hfp hEfin).mul (hfp hgfin))
      (mul_pos hEprod hG).ne').congr_fun fun v => ?_
    simp only [g, hW v, zpow_one, _root_.zpow_neg_one]
    have := hα'pos v; have := hEpos v; have := hαpos v; have := (hlam v).ne'; have := hrpos v
    field_simp
  have hreg3 : regProd (chiTern Q₀ m) 1 β =
      LOne (chiTern Q₀ m) * ((∏ᶠ v, W0 v) * (∏' v, α v) * (∏ᶠ v, r v) / ((∏ᶠ v, E v) * ∏ᶠ v, g v)) := by
    show LOne (chiTern Q₀ m) ^ (1 : ℤ) * ∏' v, β v * (1 - chiTern Q₀ m v / (normP v : ℝ)) ^ (1 : ℤ) = _
    rw [hβp.tprod_eq, zpow_one]
  have hreg2 : regProd (fun v => chiP v fr.Q') (-1) α' = (LOne (chiTern Q₀ m))⁻¹ * ∏ᶠ v, g v := by
    rw [regProd_congr_finite (fun v => abs_chiP_le fr.Q' v) hχ S hS hL (-1) α'
      (multipliable_of_hasFiniteMulSupport hgfin)]
    show LOne (chiTern Q₀ m) ^ (-1 : ℤ) * ∏' v, g v = _
    rw [(hfp hgfin).tprod_eq, _root_.zpow_neg_one]
  -- `repMass` through the frame
  have hrep : repMass (formF Q₀) L (algebraMap (𝓞 F) F m) = mass (formF fr.Q') (stdLat F 2) * ∏ᶠ v, W0 v := by
    have h1 := repMass_eq_mass_mul_finprod_lat Q₀ hpd hρ fr (β := 1) one_ne_zero L hLi
    rw [one_pow, one_mul] at h1
    exact h1
  -- the archimedean products
  have key : (∏ σ : F →ₐ[ℚ] ℂ, archVolSO (2 + 1) (detGram Q₀ σ)) * ∏ᶠ v, E v =
      (∏ σ : F →ₐ[ℚ] ℂ, archVolSO 2 (detGram fr.Q' σ)) *
        ∏ σ : F →ₐ[ℚ] ℂ, archRepDensity (2 + 1) ‖σ (algebraMap (𝓞 F) F m)‖ (detGram Q₀ σ) := by
    rw [finprod_frameJac fr hρ, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun σ _ => arch_place_siegel Q₀ hpd fr hρ σ
  have hδ : 0 < |(NumberField.discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F)
  rw [tamagawaKLat_eq_finprod, hrep, tauSOReg_eq fr.Q' hQ'nd hpd']
  unfold tamagawaK tamagawaKReg siegelProduct3Lat siegelProductWith
  rw [hreg2, hreg3]
  have hδe : |(NumberField.discr F : ℝ)| ^ (-(((2 + 1 : ℕ) : ℝ) * (((2 + 1 : ℕ) : ℝ) - 1) / 4)) =
      |(NumberField.discr F : ℝ)| ^ (-((2 : ℝ) * (2 - 1) / 4)) *
        |(NumberField.discr F : ℝ)| ^ (-(((3 : ℕ) : ℝ) - 1) / 2) := by
    rw [← Real.rpow_add hδ]; push_cast; ring_nf
  have hV₀ : (∏ σ : F →ₐ[ℚ] ℂ, archVolSO (2 + 1) (detGram Q₀ σ)) =
      (∏ σ : F →ₐ[ℚ] ℂ, archVolSO 2 (detGram fr.Q' σ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 3 ‖σ (algebraMap (𝓞 F) F m)‖ (detGram Q₀ σ)) / ∏ᶠ v, E v := by
    rw [eq_div_iff hEprod.ne']; exact key
  rw [hδe, hV₀]
  have hL0' := hL0.ne'
  have hG' := hG.ne'
  have hE' := hEprod.ne'
  field_simp
  ring

/-- **Numbers not represented over $F$:** $S_3(L, m) = 0$ (a prime with $\beta_\mathfrak p(L, m) = 0$ gives a zero factor). -/
theorem siegelProduct3Lat_eq_zero_of_not_rep (Q₀ : QuadForm (𝓞 F) 3) (hpd : IsTotallyPosDef (formF Q₀))
    (L : Lat F 3) (hLi : Lattices.IsIntegral (formF Q₀) L.1) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (h : ¬ ∃ ξ, (formF Q₀).eval ξ = algebraMap (𝓞 F) F m) : siegelProduct3Lat Q₀ L m = 0 := by
  have hρ : algebraMap (𝓞 F) F m ≠ 0 :=
    (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (ne_zero_of_totallyPos hm)
  have hQF := hpd.nondegenerate
  have hQ₀ : Q₀.Nondegenerate := nondegenerate_of_map hQF
  have hnot : ¬ (formF Q₀).RepresentsIn F (algebraMap (𝓞 F) F m) := by
    rintro ⟨x, hx⟩; exact h ⟨x, hx⟩
  rw [represents_iff_everywhere_nf (formF Q₀) hQF _ hρ] at hnot
  simp only [NFPlace.Everywhere, not_forall] at hnot
  obtain ⟨p, hp⟩ := hnot
  cases p with
  | infinite w => exact absurd (representsIn_real Q₀ hpd hm w) hp
  | finite v =>
    obtain ⟨A, hA⟩ := exists_isLocModel v L
    have hint := hA.isIntegral v hLi
    have hQ₁ := nondegenerate_gramZ hQ₀ A hint
    have hp₁ : ¬ (formF (gramZ (formF Q₀) A hint)).RepresentsIn (v.adicCompletion F) (algebraMap (𝓞 F) F m) := by
      rintro ⟨x, hx⟩
      apply hp
      refine ⟨(A.val.map (algebraMap F (v.adicCompletion F))) *ᵥ x, ?_⟩
      rw [← evalIn_compMat_gl, ← formF_gramZ Q₀ A hint]
      exact hx
    have h0 : latBeta v Q₀ L m = 0 := by
      rw [latBeta_eq v Q₀ L hA hint, ← betaZ_algebraMap,
        betaZ_eq_zero_of_not_rep _ hQ₁ (by omega) v hρ hp₁, mul_zero]
    unfold siegelProduct3Lat siegelProductWith regProd
    rw [tprod_of_exists_eq_zero ⟨v, by simp only [h0, zero_mul]⟩, mul_zero, mul_zero]

/-- **Siegel's formula in rank 3 for every genus over every totally real field** (unconditional; Siegel 1935, Hauptsatz, $n = 3$, over
$F$ [unverified]; regularized product). For $F$ totally real (any class number), $Q_0$ totally positive definite ternary
over $\mathcal O_F$, **every** lattice $L$ on $(F^3, Q_0)$ with $Q_0$ integral on $L$ (any Steinitz class) and every totally positive $m$:
`SiegelFormulaAt3Lat Q₀ L m`. *Proof:* the frame identity with $\tau(SO(Q_0)) = 2$ (`tamagawaNumberTwo_ternary_nf`, the mass formula
for $L$: `massFormula_lat_nf`) and $\tau^{\mathrm{reg}}(SO(Q_0')) = 2$ (`binaryTamagawaTwoReg_nf`). -/
@[kb "siegel1935" "Hauptsatz, n = 3, every genus, over a totally real field (regularized product) [unverified for F]"]
theorem siegelFormulaAt3Lat_totallyReal (Q₀ : QuadForm (𝓞 F) 3) (hpd : IsTotallyPosDef (formF Q₀))
    (L : Lat F 3) (hLi : Lattices.IsIntegral (formF Q₀) L.1) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAt3Lat Q₀ L m := by
  refine ⟨?_⟩
  have hρ : algebraMap (𝓞 F) F m ≠ 0 :=
    (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (ne_zero_of_totallyPos hm)
  have hQ₀ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  by_cases h : ∃ ξ, (formF Q₀).eval ξ = algebraMap (𝓞 F) F m
  · obtain ⟨ξ, hξ⟩ := h
    obtain ⟨fr⟩ := exists_adaptedFrame (formF Q₀) hξ hρ
    have hpd' : IsTotallyPosDef (formF fr.Q') := by
      have h1 := isTotallyPosDef_compMat (formF Q₀) fr.g hpd
      rw [fr.compMat_eq] at h1
      exact isTotallyPosDef_of_splitForm h1
    have key := two_mul_tamagawaKLat_mul_repMass_frame3 Q₀ hpd L hLi hm fr
    rw [binaryTamagawaTwoReg_nf.tau_eq_two fr.Q' hpd'] at key
    have hmass := massFormula_lat_nf Q₀ hQ₀ (by norm_num) hpd (tamagawaNumberTwo_ternary_nf Q₀ hpd) L hLi
    have hpos := mass_pos hpd L hLi
    have hμ : tamagawaKLat Q₀ L ≠ 0 := by
      intro h0; rw [hmass, h0, _root_.inv_zero] at hpos; exact lt_irrefl 0 hpos
    rw [hmass]
    field_simp
    linarith
  · rw [repMass_eq_zero_of_not_rep _ _ h, siegelProduct3Lat_eq_zero_of_not_rep Q₀ hpd L hLi hm h, mul_zero]

/-- The rank-3 headline for $L = \mathcal O_F^3$ is the existing `siegelFormulaAt3_nf_uncond`. -/
theorem siegelFormulaAt3Lat_totallyReal_std (Q₀ : QuadForm (𝓞 F) 3) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAt3 Q₀ m :=
  (siegelFormulaAt3Lat_std_iff Q₀ m).mp
    (siegelFormulaAt3Lat_totallyReal Q₀ hpd (stdLat F 3) (HilbertModular.isIntegral_stdLat Q₀) hm)

end QuadFormsKB.Tamagawa.SiegelLat
