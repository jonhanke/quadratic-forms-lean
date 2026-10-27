/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.SiegelLatRank3
import QuadFormsKB.Tamagawa.SiegelBinaryNF
import QuadFormsKB.Tamagawa.SiegelLatRankOne

/-!
# G5: Siegel's formula in rank 2 for every genus, every totally real field

**Layer:** $F$ totally real (any class number); $Q$ a totally positive definite **binary** form over $\mathcal O_F$; $L$ an **arbitrary**
lattice on $(F^2, Q)$ with $Q$ integral on $L$ (any Steinitz class); $m \in \mathcal O_F$ totally positive.

In rank $2$ both $\prod_\mathfrak p\alpha_\mathfrak p(Q)$ and $\prod_\mathfrak p\beta_\mathfrak p$ diverge; as for $\mathcal O_F^2$ both are regularized by
the character $\chi_Q$ = `chiP · Q` with exponent $-1$, and Siegel's constant is $\varepsilon = \tfrac12$. `tamagawaKLat_eq_local` excludes
$n = 2$, so the lattice measure is transported directly by the index ratio (the Haar property):
* `tamagawaKRegLat Q L` $= \mu^{\mathrm{reg}}_{\mathrm{Tam}}(K_{SO}(\mathcal O_F^2))\cdot r(K(L), K(\mathcal O_F^2))$ (`tamagawaKReg` times `relRatio`);
* `siegelProduct2RegLat Q L m` $= |d_F|^{-1/2}\prod_\sigma\beta_\sigma(m)\cdot L_F(1,\chi_Q)^{-1}\prod_\mathfrak p\beta_\mathfrak p(L, m)(1-\chi_Q(\mathfrak p)N\mathfrak p^{-1})^{-1}$.

**Proves**
* `tamagawaKRegLat_mul_mass`: $\mu^{\mathrm{reg}}(K_{SO}(L))\cdot 2\,\mathrm{Mass}(L) = \tau^{\mathrm{reg}}(SO(Q))$ (the regularized $\tau$ does not depend on
  the lattice);
* `two_mul_tamagawaKRegLat_mul_repMass_frame2`: Weil's step $1 \to 2$ for $L$ (local input: `latOrbitalIdentity` at $n = 1$);
* **`siegelFormulaAt2Lat_totallyReal`** (headline, unconditional):
  $\mathrm{repMass}(L, m) = \tfrac12\,\mathrm{Mass}(L)\cdot S^{\mathrm{reg}}_2(L, m)$; for $L = \mathcal O_F^2$ it is `siegelFormulaAt2_nf`.

Sources: Siegel 1935, Hauptsatz ($n = 2$, $\varepsilon = \tfrac12$; over $F$ [unverified]); Weil 1982, §4.5 and Thm. 3.7.1 [unverified].
-/

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.SiegelLat

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.LocalDensity QuadFormsKB.QuadForm
open QuadFormsKB.HilbertModular LatChange QuadFormsKB.NFEuler QuadFormsKB.RegProd

variable {F : Type} [Field F] [NumberField F]

/-- **The global index ratio is the restricted product of the local ones**: $r(K(L), K(\mathcal O_F^N)) = \prod_\mathfrak pr_\mathfrak p(L)$. -/
theorem relRatio_locStab_eq_finprod [IsTotallyReal F] {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (L : Lat F N) :
    relRatio (locStab (formF Q₀) L) (locStab (formF Q₀) (stdLat F N)) = ∏ᶠ v, locRatio v Q₀ L := by
  classical
  have hSfin : {v : HeightOneSpectrum (𝓞 F) | ¬ loc v L.1 = std v}.Finite :=
    Filter.eventually_cofinite.mp (loc_eventually_std L.2)
  set S := hSfin.toFinset
  have hS : ∀ v ∉ S, loc v L.1 = std v := fun v hv => by
    by_contra h; exact hv (hSfin.mem_toFinset.mpr h)
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) fun v hv => by
    by_contra h; exact hv (locRatio_eq_one v Q₀ L (hS v h))]
  rw [relRatio_symm', relRatio_locStab_eq_prod (formF Q₀) L S hS, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun v _ => (relRatio_symm' _ _).symm

/-- **The regularized rank-2 Tamagawa measure of $K_{SO}(L)$** for an arbitrary lattice $L$: `tamagawaKReg Q` transported by
the index ratio $r(K(L), K(\mathcal O_F^2))$ (Haar property). -/
@[kb "weil1982" "§2.3 and Lemma 2.4.2 (convergence factors), arbitrary lattice [unverified]"]
def tamagawaKRegLat (Q : QuadForm (𝓞 F) 2) (L : Lat F 2) : ℝ :=
  tamagawaKReg Q * relRatio (locStab (formF Q) L) (locStab (formF Q) (stdLat F 2))

/-- **The regularized rank-2 Siegel product of an arbitrary lattice** (character $\chi_Q$ = `chiP · Q`, exponent $-1$). For
$L = \mathcal O_F^2$ it is `siegelProduct2Reg`. -/
@[kb "siegel1935" "Hauptsatz, n = 2 (local side, regularized, arbitrary lattice; over F [unverified])"]
def siegelProduct2RegLat (Q : QuadForm (𝓞 F) 2) (L : Lat F 2) (m : 𝓞 F) : ℝ :=
  siegelProductWith Q m (regProd (fun v => chiP v Q) (-1) fun v => latBeta v Q L m)

theorem siegelProduct2RegLat_std [IsTotallyReal F] (Q : QuadForm (𝓞 F) 2) (m : 𝓞 F) :
    siegelProduct2RegLat Q (stdLat F 2) m = siegelProduct2Reg Q m := by
  unfold siegelProduct2RegLat siegelProduct2Reg; simp_rw [latBeta_std]

/-- **Siegel's formula in rank 2 for the genus of an arbitrary lattice** ($\varepsilon = \tfrac12$, regularized product):
$$\sum_{\mathrm{cls}M\subseteq\mathrm{gen}L}\frac{r_M(m)}{|O(M)|} = \tfrac12\,\mathrm{Mass}(L)\cdot S^{\mathrm{reg}}_2(L, m).$$

Field:
- `repMass_eq`: `repMass (formF Q) L m = (1/2) * mass (formF Q) L * siegelProduct2RegLat Q L m`.

For $L = \mathcal O_F^2$ it is `SiegelFormulaAt2 Q m` (`siegelFormulaAt2Lat_std_iff`). A statement (a conclusion), never assumed. -/
@[kb "siegel1935" "Hauptsatz, n = 2 (ε = 1/2, regularized, arbitrary lattice; over F [unverified])"]
structure SiegelFormulaAt2Lat (Q : QuadForm (𝓞 F) 2) (L : Lat F 2) (m : 𝓞 F) : Prop where
  repMass_eq : repMass (formF Q) L (algebraMap (𝓞 F) F m) =
    (1 / 2 : ℝ) * mass (formF Q) L * siegelProduct2RegLat Q L m

theorem siegelFormulaAt2Lat_std_iff [IsTotallyReal F] (Q : QuadForm (𝓞 F) 2) (m : 𝓞 F) :
    SiegelFormulaAt2Lat Q (stdLat F 2) m ↔ SiegelFormulaAt2 Q m := by
  constructor
  · intro h; exact ⟨by rw [← siegelProduct2RegLat_std]; exact h.repMass_eq⟩
  · intro h; exact ⟨by rw [siegelProduct2RegLat_std]; exact h.repMass_eq⟩

variable [IsTotallyReal F]

/-- **$\tau^{\mathrm{reg}}$ computed with any integral lattice**: $\mu^{\mathrm{reg}}(K_{SO}(L))\cdot2\,\mathrm{Mass}(L) = \tau^{\mathrm{reg}}(SO(Q))$
(`mass_eq_mass_mul_relRatio` and $r(A, B)\,r(B, A) = 1$, as in `tauSOLat_eq_tauSO`). -/
theorem tamagawaKRegLat_mul_mass (Q : QuadForm (𝓞 F) 2) (hQ : Q.Nondegenerate) (hpd : IsTotallyPosDef (formF Q))
    (L : Lat F 2) (hLi : Lattices.IsIntegral (formF Q) L.1) :
    tamagawaKRegLat Q L * (2 * mass (formF Q) L) = tauSOReg Q := by
  rw [tauSOReg_eq Q hQ hpd]
  unfold tamagawaKRegLat
  rw [mass_eq_mass_mul_relRatio hpd (stdLat F 2) L (isIntegral_std Q) hLi]
  have hc := commensurable_locStab (formF Q) (stdLat F 2) L
  have h1 : relRatio (locStab (formF Q) L) (locStab (formF Q) (stdLat F 2)) *
      relRatio (locStab (formF Q) (stdLat F 2)) (locStab (formF Q) L) = 1 :=
    relRatio_mul_relRatio_symm ⟨hc.2.relIndex_ne_zero, hc.1.relIndex_ne_zero⟩
  linear_combination (tamagawaKReg Q * 2 * mass (formF Q) (stdLat F 2)) * h1

set_option maxHeartbeats 800000 in
/-- **Weil's step $1 \to 2$ for an arbitrary lattice, regularized** (Weil 1982, §4.5, p. 100 and p. 109 [unverified], $N = 2$):
$$2\,\mu^{\mathrm{reg}}(K_{SO}(L))\cdot\mathrm{repMass}(L, a) = \tau(SO(Q''))\cdot S^{\mathrm{reg}}_2(L, a).$$
the proof with `latOrbitalIdentity` ($n = 1$) and the index ratios $r_\mathfrak p(L)$. -/
@[kb "weil1982" "§4.5, p. 100 and p. 109 (N = 2, regularized, arbitrary lattice) [unverified]"]
theorem two_mul_tamagawaKRegLat_mul_repMass_frame2 (Q : QuadForm (𝓞 F) (1 + 1)) (hpd : IsTotallyPosDef (formF Q))
    (L : Lat F (1 + 1)) (hLi : Lattices.IsIntegral (formF Q) L.1)
    {a : 𝓞 F} (ha : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F a))
    (fr : AdaptedFrame (formF Q) (algebraMap (𝓞 F) F a)) :
    2 * tamagawaKRegLat Q L * repMass (formF Q) L (algebraMap (𝓞 F) F a) =
      tauSO fr.Q' * siegelProduct2RegLat Q L a := by
  classical
  have hρ : algebraMap (𝓞 F) F a ≠ 0 :=
    (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (ne_zero_of_totallyPos ha)
  have hQF : (formF Q).Nondegenerate := hpd.nondegenerate
  have hQ : Q.Nondegenerate := nondegenerate_of_map hQF
  have hQ'nd : fr.Q'.Nondegenerate := fr.nondegenerate hQF hρ
  have hpd' : IsTotallyPosDef (formF fr.Q') := by
    have h1 := isTotallyPosDef_compMat (formF Q) fr.g hpd
    rw [fr.compMat_eq] at h1
    exact isTotallyPosDef_of_splitForm h1
  set QF' := fr.Q'.map (algebraMap (𝓞 F) F)
  -- the local factors
  set W0 : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    locTypeSumG v (algebraMap (𝓞 F) F a) QF' (loc v (glImage fr.g⁻¹ L.1)) (algebraMap F (v.adicCompletion F) 1)
  set r : HeightOneSpectrum (𝓞 F) → ℝ := fun v => locRatio v Q L
  set α : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.siegelDensity v Q Q
  set α' : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.siegelDensity v fr.Q' fr.Q'
  set E : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (1 + 1) /
      ‖algebraMap F (v.adicCompletion F) (2 * algebraMap (𝓞 F) F a)‖ ^ 1
  set β : HeightOneSpectrum (𝓞 F) → ℝ := fun v => latBeta v Q L a
  set χ : HeightOneSpectrum (𝓞 F) → ℝ := fun v => chiP v Q
  have hχ : ∀ v, |χ v| ≤ 1 := fun v => abs_chiP_le Q v
  have hlam : ∀ v, 0 < 1 - χ v / (normP v : ℝ) := fun v => one_sub_div_pos (hχ v) v
  have hEpos : ∀ v, 0 < E v := fun v => by
    have h1 : algebraMap F (v.adicCompletion F) fr.g.val.det ≠ 0 :=
      (map_ne_zero _).mpr (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero
    have h2 : algebraMap F (v.adicCompletion F) (2 * algebraMap (𝓞 F) F a) ≠ 0 :=
      (map_ne_zero _).mpr (mul_ne_zero two_ne_zero hρ)
    exact div_pos (pow_pos (norm_pos_iff.mpr h1) _) (pow_pos (norm_pos_iff.mpr h2) _)
  have hα'pos : ∀ v, 0 < α' v := fun v => siegelDensity_pos v fr.Q' hQ'nd
  have hrpos : ∀ v, 0 < r v := fun v => locRatio_pos v hQ L hLi
  have hW : ∀ v, W0 v * α v * r v = α' v * E v * β v := by
    intro v
    have hj := latOrbitalIdentity v Q hQ le_rfl L hLi rfl hρ fr
    rw [show (2 : v.adicCompletion F) * algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) =
      algebraMap F (v.adicCompletion F) (2 * algebraMap (𝓞 F) F a) by rw [map_mul, map_ofNat]] at hj
    have hdet : 0 < ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (1 + 1) :=
      pow_pos (norm_pos_iff.mpr ((map_ne_zero _).mpr (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero)) _
    have hB : 0 < ‖algebraMap F (v.adicCompletion F) (2 * algebraMap (𝓞 F) F a)‖ ^ 1 :=
      pow_pos (norm_pos_iff.mpr ((map_ne_zero _).mpr (mul_ne_zero two_ne_zero hρ))) _
    simp only [W0, E, α, α', β, r] at hj ⊢
    generalize ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (1 + 1) = D at hj hdet ⊢
    generalize ‖algebraMap F (v.adicCompletion F) (2 * algebraMap (𝓞 F) F a)‖ ^ 1 = B at hj hB ⊢
    field_simp at hj ⊢
    linear_combination hj
  -- finite supports
  have hglat : (glImage fr.g⁻¹ L.1).IsLattice F := glImage_isLattice fr.g⁻¹ L.2
  have hfin₀ : {v : HeightOneSpectrum (𝓞 F) | loc v (glImage fr.g⁻¹ L.1) ≠ std v ∨
      v.valuation F (algebraMap (𝓞 F) F a) ≠ 1 ∨ v.valuation F 2 ≠ 1}.Finite :=
    ((Filter.eventually_cofinite.mp (loc_eventually_std hglat)).union
      ((finite_valuation_ne_one hρ).union (finite_valuation_ne_one (two_ne_zero (α := F))))).subset fun v hv => by
        simpa [or_assoc] using hv
  have hW0fin : Function.HasFiniteMulSupport W0 := by
    refine hfin₀.subset fun v hv => ?_
    by_contra h
    simp only [Set.mem_ofPred_eq, not_or, not_not] at h
    apply hv
    show locTypeSumG v (algebraMap (𝓞 F) F a) QF' (loc v (glImage fr.g⁻¹ L.1))
      (algebraMap F (v.adicCompletion F) 1) = 1
    rw [h.1, map_one]
    exact locTypeSumG_std_one_of_units v fr.Q' hQ'nd h.2.1 h.2.2
  have hrfin : Function.HasFiniteMulSupport r := by
    refine (Filter.eventually_cofinite.mp (loc_eventually_std L.2)).subset fun v hv => ?_
    by_contra h
    exact hv (locRatio_eq_one v Q L (by simpa using h))
  have hEfin : Function.HasFiniteMulSupport E := by
    have hdet : fr.g.val.det ≠ 0 := (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero
    refine ((finite_valuation_ne_one hdet).union
      (finite_valuation_ne_one (mul_ne_zero two_ne_zero hρ))).subset fun v hv => ?_
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
    apply hv
    show E v = 1
    simp only [E, norm_algebraMap_eq_one h.1, norm_algebraMap_eq_one h.2, one_pow, div_one]
  set g : HeightOneSpectrum (𝓞 F) → ℝ := fun v => α v * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ)
  have hgfin : Function.HasFiniteMulSupport g :=
    hasFiniteMulSupport_siegelDensity_binary_reg hQ ∅ fun _ _ => rfl
  have hα'fin : Function.HasFiniteMulSupport α' := by
    refine (finite_badPrimes fr.Q' hQ'nd).subset fun v hv => ?_
    by_contra h
    exact hv (RankOne.siegelDensity_rankOne_good fr.Q' hQ'nd v h)
  have hfp : ∀ {f : HeightOneSpectrum (𝓞 F) → ℝ}, Function.HasFiniteMulSupport f → HasProd f (∏ᶠ v, f v) :=
    fun {f} hf => by
      have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hf).hasProd
      rwa [tprod_eq_finprod hf] at this
  have hfpos : ∀ {f : HeightOneSpectrum (𝓞 F) → ℝ}, Function.HasFiniteMulSupport f → (∀ v, 0 < f v) →
      0 < ∏ᶠ v, f v := fun {f} hf hpos => by
    rw [finprod_eq_prod_of_mulSupport_subset f (s := hf.toFinset) fun v hv => (Set.Finite.mem_toFinset _).mpr hv]
    exact Finset.prod_pos fun v _ => hpos v
  have hEprod : 0 < ∏ᶠ v, E v := hfpos hEfin hEpos
  have hA' : 0 < ∏ᶠ v, α' v := hfpos hα'fin hα'pos
  -- β λ⁻¹ = W₀ (α λ⁻¹) r / (α'' E)
  have hβeq : ∀ v, β v * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ) = W0 v * g v * r v / (α' v * E v) := fun v => by
    simp only [g]
    have := hα'pos v; have := hEpos v; have := (hlam v).ne'
    rw [eq_div_iff (by positivity),
      show W0 v * (α v * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ)) * r v =
        W0 v * α v * r v * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ) by ring, hW v]
    ring
  have hβp : HasProd (fun v => β v * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ))
      ((∏ᶠ v, W0 v) * (∏ᶠ v, g v) * (∏ᶠ v, r v) / ((∏ᶠ v, α' v) * ∏ᶠ v, E v)) :=
    ((((hfp hW0fin).mul (hfp hgfin)).mul (hfp hrfin)).div₀ ((hfp hα'fin).mul (hfp hEfin))
      (mul_pos hA' hEprod).ne').congr_fun fun v => hβeq v
  -- the character and the regularized products
  obtain ⟨hL0, -⟩ := lOne_chiP_binary hpd
  have hreg2 : regProd χ (-1) β =
      (LOne χ)⁻¹ * ((∏ᶠ v, W0 v) * (∏ᶠ v, g v) * (∏ᶠ v, r v) / ((∏ᶠ v, α' v) * ∏ᶠ v, E v)) := by
    show LOne χ ^ (-1 : ℤ) * ∏' v, β v * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ) = _
    rw [hβp.tprod_eq, _root_.zpow_neg_one]
  have hregα : regProd χ (-1) α = (LOne χ)⁻¹ * ∏ᶠ v, g v := by
    show LOne χ ^ (-1 : ℤ) * ∏' v, g v = _
    rw [(hfp hgfin).tprod_eq, _root_.zpow_neg_one]
  -- `repMass` through the frame
  have hrep : repMass (formF Q) L (algebraMap (𝓞 F) F a) = mass (formF fr.Q') (stdLat F 1) * ∏ᶠ v, W0 v := by
    have h1 := repMass_eq_mass_mul_finprod_lat (n := 1) Q hpd hρ fr (β := 1) one_ne_zero L hLi
    rw [one_pow, one_mul] at h1
    exact h1
  -- the archimedean products
  have key : (∏ σ : F →ₐ[ℚ] ℂ, archVolSO (1 + 1) (detGram Q σ)) * ∏ᶠ v, E v =
      (∏ σ : F →ₐ[ℚ] ℂ, archVolSO 1 (detGram fr.Q' σ)) *
        ∏ σ : F →ₐ[ℚ] ℂ, archRepDensity (1 + 1) ‖σ (algebraMap (𝓞 F) F a)‖ (detGram Q σ) := by
    rw [finprod_frameJac fr hρ, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun σ _ => arch_place_siegel (n := 1) Q hpd fr hρ σ
  have hV : (∏ σ : F →ₐ[ℚ] ℂ, archVolSO 2 (detGram Q σ)) =
      (∏ σ : F →ₐ[ℚ] ℂ, archVolSO 1 (detGram fr.Q' σ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 2 ‖σ (algebraMap (𝓞 F) F a)‖ (detGram Q σ)) / ∏ᶠ v, E v := by
    rw [eq_div_iff hEprod.ne']; exact key
  have hτ : tauSO fr.Q' = tamagawaK fr.Q' * (2 * mass (formF fr.Q') (stdLat F 1)) := by
    rw [tauSO, mass_SO_eq_two_mul_mass fr.Q' hQ'nd (by norm_num) hpd' (HilbertModular.isIntegral_stdLat fr.Q')]
  have hK : tamagawaK fr.Q' = (∏ σ : F →ₐ[ℚ] ℂ, archVolSO 1 (detGram fr.Q' σ)) * ∏ᶠ v, α' v := by
    rw [tamagawaK, (hfp hα'fin).tprod_eq]
    norm_num
  unfold tamagawaKRegLat
  rw [relRatio_locStab_eq_finprod, hrep, hτ, hK]
  unfold tamagawaKReg siegelProduct2RegLat siegelProductWith
  rw [hreg2, hregα, hV]
  have hL0' := hL0.ne'
  have hA'' := hA'.ne'
  have hE' := hEprod.ne'
  norm_num
  field_simp
  simp only [r]
  ring

/-- **Siegel's formula in rank 2 for every genus over every totally real field** (unconditional; Siegel 1935, Hauptsatz, $n = 2$,
$\varepsilon = \tfrac12$, over $F$ [unverified]): for every totally positive definite binary $Q$ over $\mathcal O_F$, **every** lattice $L$ on
$(F^2, Q)$ with $Q$ integral on $L$ (any Steinitz class) and every totally positive $m$, `SiegelFormulaAt2Lat Q L m`. *Proof:* Weil's
step $1\to2$ for $L$ with $\tau(SO_1) = 1$ (`tauSO_rankOne_eq_one`) and $\tau^{\mathrm{reg}}(SO(Q)) = 2$ (`binaryTamagawaTwoReg_nf`) through
`tamagawaKRegLat_mul_mass`; both sides vanish when $Q$ does not represent $m$ over $F$. -/
@[kb "siegel1935" "Hauptsatz, n = 2 (ε = 1/2, regularized), every genus, over a totally real field [unverified for F]"]
theorem siegelFormulaAt2Lat_totallyReal (Q : QuadForm (𝓞 F) 2) (hpd : IsTotallyPosDef (formF Q))
    (L : Lat F 2) (hLi : Lattices.IsIntegral (formF Q) L.1) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAt2Lat Q L m := by
  refine ⟨?_⟩
  have hQ : Q.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  have hρ : algebraMap (𝓞 F) F m ≠ 0 :=
    (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (ne_zero_of_totallyPos hm)
  by_cases h : ∃ ξ, (formF Q).eval ξ = algebraMap (𝓞 F) F m
  · obtain ⟨ξ, hξ⟩ := h
    obtain ⟨fr⟩ := exists_adaptedFrame (n := 1) (formF Q) hξ hρ
    have hQ'nd : fr.Q'.Nondegenerate := fr.nondegenerate hpd.nondegenerate hρ
    have hpd' : IsTotallyPosDef (formF fr.Q') := by
      have h1 := isTotallyPosDef_compMat (formF Q) fr.g hpd
      rw [fr.compMat_eq] at h1
      exact isTotallyPosDef_of_splitForm h1
    have key := two_mul_tamagawaKRegLat_mul_repMass_frame2 Q hpd L hLi hm fr
    rw [TauSOOne.tauSO_rankOne_eq_one fr.Q' hQ'nd hpd' (HilbertModular.isIntegral_stdLat fr.Q'), one_mul] at key
    have hmass := tamagawaKRegLat_mul_mass Q hQ hpd L hLi
    rw [binaryTamagawaTwoReg_nf.tau_eq_two Q hpd] at hmass
    rw [← key]
    linear_combination (-(repMass (formF Q) L (algebraMap (𝓞 F) F m)) / 2) * hmass
  · rw [repMass_eq_zero_of_not_rep _ _ h]
    obtain ⟨v, hv⟩ := exists_latBeta_eq_zero_of_not_rep (n := 1) Q hpd L hLi hm h
    unfold siegelProduct2RegLat siegelProductWith regProd
    rw [tprod_of_exists_eq_zero ⟨v, by simp only [hv, zero_mul]⟩, mul_zero, mul_zero, mul_zero]

/-- The rank-2 headline for $L = \mathcal O_F^2$ is the existing `siegelFormulaAt2_nf`. -/
theorem siegelFormulaAt2Lat_totallyReal_std (Q : QuadForm (𝓞 F) 2) (hpd : IsTotallyPosDef (formF Q)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAt2 Q m :=
  (siegelFormulaAt2Lat_std_iff Q m).mp
    (siegelFormulaAt2Lat_totallyReal Q hpd (stdLat F 2) (HilbertModular.isIntegral_stdLat Q) hm)

end QuadFormsKB.Tamagawa.SiegelLat
