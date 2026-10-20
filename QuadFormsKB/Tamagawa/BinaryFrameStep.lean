import QuadFormsKB.Tamagawa.BinaryRegChange
import QuadFormsKB.Tamagawa.TauSOOne

/-!
# Weil's step $1 \to 2$ with the regularized rank-2 measure

**Layer:** forms over $\mathcal O_F$, $F$ totally real; a totally positive definite **binary** form $Q$ ($L = \mathcal O_F^2$),
a totally positive $a \in \mathcal O_F$, and an adapted frame $Q\circ g = \langle a\rangle\perp Q''$ (`AdaptedFrame`) with
**rank-one** complement $Q''$.

This is the frame identity (`two_mul_tamagawaK_mul_repMass_frame3`) one rank lower: now the *form* is binary, so both
$\prod_\mathfrak p\alpha_\mathfrak p(Q)$ (`tamagawaK`) and $\prod_\mathfrak p\beta_\mathfrak p(Q, a)$ diverge, and both are regularized by
the same character $\chi_Q$ = `chiP · Q` with exponent $-1$ (`docs/rank3-siegel-design.md` §2.2, option (ii)):

* `siegelProduct2Reg Q a` $= |d_F|^{-1/2}\prod_\sigma\beta_\sigma(a)\cdot L_F(1,\chi_Q)^{-1}\prod_\mathfrak p\beta_\mathfrak p(Q,a)
  (1-\chi_Q(\mathfrak p)/N\mathfrak p)^{-1}$ (the rank-2 analogue of `siegelProduct3`; the product has finite support,
  `hasFiniteMulSupport_localDensity_binary_reg`).
* **`two_mul_tamagawaKReg_mul_repMass_frame2`** (unconditional):
  $$2\,\mu^{\mathrm{reg}}_{\mathrm{Tam}}(K_{SO}(Q))\cdot\mathrm{repMass}(\mathcal O_F^2, a) = \tau(SO(Q''))\cdot S^{\mathrm{reg}}_2(Q, a).$$
  The local orbital identities are `orbitalLocalIdentities` ($n = 1$ included); the factors $L_F(1,\chi_Q)^{-1}$ on the
  two sides are the same and cancel.
* With the $\tau(SO_1) = 1$ (`tauSO_rankOne_eq_one`): `two_mul_tamagawaKReg_mul_repMass` —
  $2\,\mu^{\mathrm{reg}}(Q)\,\mathrm{repMass}(Q, a) = S^{\mathrm{reg}}_2(Q, a)$ for every totally positive $a$ represented by $Q$
  over $F$ — and `tauSOReg_eq_two_iff`: $\tau^{\mathrm{reg}}(SO(Q)) = 2$ iff $S^{\mathrm{reg}}_2(Q,a) = 2\,\mathrm{repMass}/\mathrm{Mass}$
  at one $a$ with $\mathrm{repMass}(Q, a) \ne 0$ (i.e. the binary Siegel formula with $\varepsilon = \frac12$ at one number).
* `chiP_eq_of_localDensity`: as a by-product, $\beta_\mathfrak p(Q,a) = 1 - \chi_Q(\mathfrak p)/N\mathfrak p$ outside a finite set (used in
  part 2 to compare $\chi_Q$ with $\chi_D$ over $\mathbb Q$ without computing residue symbols).

Part 2 (`BinaryTauRat.lean`) feeds in the binary Siegel formula over $\mathbb Q$.

-/

open NumberField IsDedekindDomain Matrix Filter Topology
open scoped Real

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open Lattices NFEuler RegProd LocalDensity QuadForm QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F]

/-- **The regularized local side in rank 2:** the local side with $P = L_F(1,\chi_Q)^{-1}\prod_\mathfrak p\beta_\mathfrak p(Q,a)
(1-\chi_Q(\mathfrak p)/N\mathfrak p)^{-1}$, $\chi_Q$ = `chiP · Q` (the character of `tamagawaKReg Q`). In rank 2 the plain product
$\prod\beta_\mathfrak p$ diverges, as for `siegelProduct3`. -/
@[kb "siegel1935" "Hauptsatz, n = 2 (local side, regularized) [unverified]"]
def siegelProduct2Reg (Q : QuadForm (𝓞 F) 2) (a : 𝓞 F) : ℝ :=
  siegelProductWith Q a (regProd (fun v => chiP v Q) (-1) fun v => NF.localDensity v Q a)

variable [IsTotallyReal F]

/-- The local factors of the step $1 \to 2$ at one prime (`orbitalLocalIdentities` at $j = 0$, $n = 1$):
$W_\mathfrak p(0)\,\alpha_\mathfrak p(Q) = \alpha_\mathfrak p(Q'')\,E_\mathfrak p\,\beta_\mathfrak p(Q,a)$. -/
theorem locW_mul_siegelDensity_frame2 (Q : QuadForm (𝓞 F) (1 + 1)) (hQ : Q.Nondegenerate) {a : 𝓞 F}
    (ha : algebraMap (𝓞 F) F a ≠ 0) (fr : AdaptedFrame (formF Q) (algebraMap (𝓞 F) F a))
    (v : HeightOneSpectrum (𝓞 F)) :
    locW v fr 0 * NF.siegelDensity v Q Q =
      NF.siegelDensity v fr.Q' fr.Q' *
        (‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (1 + 1) /
          ‖algebraMap F (v.adicCompletion F) (2 * algebraMap (𝓞 F) F a)‖ ^ 1) * NF.localDensity v Q a := by
  have hj := (orbitalLocalIdentityAt_all (orbitalLocalIdentities Q hQ) hQ le_rfl ha fr v).eq 0
  simp only [zero_mul, zpow_zero, mul_zero, mul_one] at hj
  rw [show (2 : v.adicCompletion F) * algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) =
    algebraMap F (v.adicCompletion F) (2 * algebraMap (𝓞 F) F a) by rw [map_mul, map_ofNat]] at hj
  rw [betaZ_algebraMap v Q a] at hj
  have hdet : 0 < ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (1 + 1) :=
    pow_pos (norm_pos_iff.mpr ((map_ne_zero _).mpr (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero)) _
  generalize ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (1 + 1) = D at hj hdet ⊢
  have hB : 0 < ‖algebraMap F (v.adicCompletion F) (2 * algebraMap (𝓞 F) F a)‖ ^ 1 :=
    pow_pos (norm_pos_iff.mpr ((map_ne_zero _).mpr (mul_ne_zero two_ne_zero ha))) _
  generalize ‖algebraMap F (v.adicCompletion F) (2 * algebraMap (𝓞 F) F a)‖ ^ 1 = B at hj hB ⊢
  calc locW v fr 0 * NF.siegelDensity v Q Q
      = locW v fr 0 * NF.siegelDensity v Q Q * B * D⁻¹ * (D / B) := by field_simp
    _ = _ := by rw [hj]; ring

set_option maxHeartbeats 800000 in
/-- **Weil's step $1 \to 2$ (the binary frame identity), regularized** (Weil 1982, §4.5, p. 100 and p. 109 [unverified], at
$N = 2$). For $Q$ totally positive definite binary over $\mathcal O_F$ ($F$ totally real, any class number), $a \in \mathcal O_F$
totally positive and any adapted frame $Q\circ g = \langle a\rangle\perp Q''$:
$$2\,\mu^{\mathrm{reg}}_{\mathrm{Tam}}(K_{SO}(Q))\cdot\mathrm{repMass}(\mathcal O_F^2, a) = \tau(SO(Q''))\cdot S^{\mathrm{reg}}_2(Q, a).$$
**Unconditional.** *Proof.* the proof with $n = 1$: the per-prime identity (`locW_mul_siegelDensity_frame2`) gives
$\beta_\mathfrak p\lambda_\mathfrak p^{-1} = W_\mathfrak p(0)\cdot\alpha_\mathfrak p(Q)\lambda_\mathfrak p^{-1}/(\alpha_\mathfrak p(Q'')E_\mathfrak p)$ with
$\lambda_\mathfrak p = 1-\chi_Q(\mathfrak p)/N\mathfrak p$; $W$, $E$, $\alpha(Q)\lambda^{-1}$ have finite support and $\prod\alpha(Q'')$ converges
(rank one), so $\prod\beta\lambda^{-1}$ converges and the two factors $L_F(1,\chi_Q)^{-1}$ cancel. -/
@[kb "weil1982" "§4.5, p. 100 and p. 109 (Siegel's theorem from the fibration over T(ρ), one number; N = 2, regularized) [unverified]"]
theorem two_mul_tamagawaKReg_mul_repMass_frame2 (Q : QuadForm (𝓞 F) 2) (hpd : IsTotallyPosDef (formF Q))
    {a : 𝓞 F} (ha : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F a))
    (fr : AdaptedFrame (formF Q) (algebraMap (𝓞 F) F a)) :
    2 * tamagawaKReg Q * repMass (formF Q) (stdLat F 2) (algebraMap (𝓞 F) F a) =
      tauSO fr.Q' * siegelProduct2Reg Q a ∧
    Function.HasFiniteMulSupport fun v =>
      NF.localDensity v Q a * (1 - chiP v Q / (normP v : ℝ)) ^ (-1 : ℤ) := by
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
  -- the local factors
  set W0 : HeightOneSpectrum (𝓞 F) → ℝ := fun v => locW v fr 0
  set α : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.siegelDensity v Q Q
  set α' : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.siegelDensity v fr.Q' fr.Q'
  set E : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (1 + 1) /
      ‖algebraMap F (v.adicCompletion F) (2 * algebraMap (𝓞 F) F a)‖ ^ 1
  set β : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.localDensity v Q a
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
  have hW : ∀ v, W0 v * α v = α' v * E v * β v := fun v =>
    locW_mul_siegelDensity_frame2 Q hQ hρ fr v
  have hfin₀ : {v : HeightOneSpectrum (𝓞 F) | frameLat v fr.g ≠ std v ∨
      v.valuation F (algebraMap (𝓞 F) F a) ≠ 1 ∨ v.valuation F 2 ≠ 1}.Finite := by
    refine ((Filter.eventually_cofinite.mp (loc_eventually_std (glImage_isLattice fr.g⁻¹ intVec_isLattice))).union
      ((finite_valuation_ne_one hρ).union (finite_valuation_ne_one (two_ne_zero (α := F))))).subset fun v hv => ?_
    simpa [frameLat, or_assoc] using hv
  have hW0fin : Function.HasFiniteMulSupport W0 := by
    refine hfin₀.subset fun v hv => ?_
    by_contra h
    simp only [Set.mem_ofPred_eq, not_or, not_not] at h
    apply hv
    show locW v fr 0 = 1
    unfold locW
    rw [zpow_zero, h.1]
    exact locTypeSumG_std_one_of_units v fr.Q' hQ'nd h.2.1 h.2.2
  have hEfin : Function.HasFiniteMulSupport E := by
    have hdet : fr.g.val.det ≠ 0 := (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero
    refine ((finite_valuation_ne_one hdet).union
      (finite_valuation_ne_one (mul_ne_zero two_ne_zero hρ))).subset fun v hv => ?_
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
    apply hv
    show E v = 1
    simp only [E, norm_algebraMap_eq_one h.1, norm_algebraMap_eq_one h.2, one_pow, div_one]
  -- the regularized binary factors of `Q`
  set g : HeightOneSpectrum (𝓞 F) → ℝ := fun v => α v * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ)
  have hgfin : Function.HasFiniteMulSupport g :=
    hasFiniteMulSupport_siegelDensity_binary_reg hQ ∅ fun _ _ => rfl
  -- the rank-one complement: a finite product
  have hα'fin : Function.HasFiniteMulSupport α' := by
    refine (finite_badPrimes fr.Q' hQ'nd).subset fun v hv => ?_
    by_contra h
    exact hv (RankOne.siegelDensity_rankOne_good fr.Q' hQ'nd v h)
  have hW0p : HasProd W0 (∏ᶠ v, W0 v) := by
    have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hW0fin).hasProd
    rwa [tprod_eq_finprod hW0fin] at this
  have hEp : HasProd E (∏ᶠ v, E v) := by
    have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hEfin).hasProd
    rwa [tprod_eq_finprod hEfin] at this
  have hGp : HasProd g (∏ᶠ v, g v) := by
    have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hgfin).hasProd
    rwa [tprod_eq_finprod hgfin] at this
  have hA'p : HasProd α' (∏ᶠ v, α' v) := by
    have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hα'fin).hasProd
    rwa [tprod_eq_finprod hα'fin] at this
  have hEprod : 0 < ∏ᶠ v, E v := by
    rw [finprod_eq_prod_of_mulSupport_subset E (s := hEfin.toFinset) fun v hv => (Set.Finite.mem_toFinset _).mpr hv]
    exact Finset.prod_pos fun v _ => hEpos v
  have hA' : 0 < ∏ᶠ v, α' v := by
    rw [finprod_eq_prod_of_mulSupport_subset α' (s := hα'fin.toFinset) fun v hv => (Set.Finite.mem_toFinset _).mpr hv]
    exact Finset.prod_pos fun v _ => hα'pos v
  -- β λ⁻¹ = W₀ · (α λ⁻¹) / (α'' E)
  have hβeq : ∀ v, β v * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ) = W0 v * g v / (α' v * E v) := fun v => by
    simp only [g]
    have := hα'pos v; have := hEpos v; have := (hlam v).ne'
    rw [eq_div_iff (by positivity),
      show W0 v * (α v * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ)) = W0 v * α v * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ)
        by ring, hW v]
    ring
  have hβp : HasProd (fun v => β v * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ))
      ((∏ᶠ v, W0 v) * (∏ᶠ v, g v) / ((∏ᶠ v, α' v) * ∏ᶠ v, E v)) :=
    ((hW0p.mul hGp).div₀ (hA'p.mul hEp) (mul_pos hA' hEprod).ne').congr_fun fun v => hβeq v
  have hβfin : Function.HasFiniteMulSupport fun v => β v * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ) := by
    refine (((hW0fin.union hgfin).union hα'fin).union hEfin).subset fun v hv => ?_
    by_contra h
    simp only [Set.mem_union, Function.mem_mulSupport, not_or, not_not] at h
    apply hv
    show β v * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ) = 1
    rw [hβeq v, h.1.1.1, h.1.1.2, h.1.2, h.2]
    norm_num
  refine ⟨?_, hβfin⟩
  -- the character and the regularized products
  obtain ⟨hL0, -⟩ := lOne_chiP_binary hpd
  have hreg2 : regProd χ (-1) β =
      (LOne χ)⁻¹ * ((∏ᶠ v, W0 v) * (∏ᶠ v, g v) / ((∏ᶠ v, α' v) * ∏ᶠ v, E v)) := by
    show LOne χ ^ (-1 : ℤ) * ∏' v, β v * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ) = _
    rw [hβp.tprod_eq, _root_.zpow_neg_one]
  have hregα : regProd χ (-1) α = (LOne χ)⁻¹ * ∏ᶠ v, g v := by
    show LOne χ ^ (-1 : ℤ) * ∏' v, g v = _
    rw [hGp.tprod_eq, _root_.zpow_neg_one]
  -- `repMass` through the frame
  have hrep : repMass (formF Q) (stdLat F (1 + 1)) (algebraMap (𝓞 F) F a) =
      mass (formF fr.Q') (stdLat F 1) * ∏ᶠ v, W0 v := by
    have h1 := repMass_eq_mass_mul_finprod (n := 1) Q hpd hρ fr (β := 1) one_ne_zero
    rw [one_pow, one_mul] at h1
    rw [h1]
    congr 1
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
    rw [tamagawaK, hA'p.tprod_eq]
    norm_num
  rw [show (stdLat F 2) = stdLat F (1 + 1) from rfl, hrep, hτ, hK]
  unfold tamagawaKReg siegelProduct2Reg siegelProductWith
  rw [hreg2, hregα, hV]
  have hL0' := hL0.ne'
  have hA'' := hA'.ne'
  have hE' := hEprod.ne'
  norm_num
  field_simp

/-- **The step $1 \to 2$ with $\tau(SO_1) = 1$** (`tauSO_rankOne_eq_one`): for $Q$ totally positive definite binary and
$a$ totally positive and represented by $Q$ over $F$,
$$2\,\mu^{\mathrm{reg}}_{\mathrm{Tam}}(K_{SO}(Q))\cdot\mathrm{repMass}(\mathcal O_F^2, a) = S^{\mathrm{reg}}_2(Q, a).$$ -/
theorem two_mul_tamagawaKReg_mul_repMass (Q : QuadForm (𝓞 F) 2) (hpd : IsTotallyPosDef (formF Q))
    {a : 𝓞 F} (ha : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F a))
    (hrep : ∃ ξ, (formF Q).eval ξ = algebraMap (𝓞 F) F a) :
    2 * tamagawaKReg Q * repMass (formF Q) (stdLat F 2) (algebraMap (𝓞 F) F a) = siegelProduct2Reg Q a := by
  have hρ : algebraMap (𝓞 F) F a ≠ 0 :=
    (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (ne_zero_of_totallyPos ha)
  obtain ⟨ξ, hξ⟩ := hrep
  obtain ⟨fr⟩ := exists_adaptedFrame (n := 1) (formF Q) hξ hρ
  have hQ'nd : fr.Q'.Nondegenerate := fr.nondegenerate hpd.nondegenerate hρ
  have hpd' : IsTotallyPosDef (formF fr.Q') := by
    have h1 := isTotallyPosDef_compMat (formF Q) fr.g hpd
    rw [fr.compMat_eq] at h1
    exact isTotallyPosDef_of_splitForm h1
  rw [(two_mul_tamagawaKReg_mul_repMass_frame2 Q hpd ha fr).1,
    TauSOOne.tauSO_rankOne_eq_one fr.Q' hQ'nd hpd' (HilbertModular.isIntegral_stdLat fr.Q'), one_mul]

/-- **The binary densities at almost all primes** (a by-product of the step $1\to2$, no residue-symbol computation):
for $a$ totally positive and represented by $Q$ over $F$, $\beta_\mathfrak p(Q, a) = 1 - \chi_Q(\mathfrak p)/N\mathfrak p$ outside a
finite set of primes. -/
theorem localDensity_eq_one_sub_chiP (Q : QuadForm (𝓞 F) 2) (hpd : IsTotallyPosDef (formF Q))
    {a : 𝓞 F} (ha : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F a))
    (hrep : ∃ ξ, (formF Q).eval ξ = algebraMap (𝓞 F) F a) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, NF.localDensity v Q a = 1 - chiP v Q / (normP v : ℝ) := by
  have hρ : algebraMap (𝓞 F) F a ≠ 0 :=
    (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (ne_zero_of_totallyPos ha)
  obtain ⟨ξ, hξ⟩ := hrep
  obtain ⟨fr⟩ := exists_adaptedFrame (n := 1) (formF Q) hξ hρ
  have hfin := (two_mul_tamagawaKReg_mul_repMass_frame2 Q hpd ha fr).2
  refine ⟨hfin.toFinset, fun v hv => ?_⟩
  have h1 : NF.localDensity v Q a * (1 - chiP v Q / (normP v : ℝ)) ^ (-1 : ℤ) = 1 := by
    by_contra h; exact hv ((Set.Finite.mem_toFinset _).mpr h)
  have hl := (one_sub_div_pos (abs_chiP_le Q v) v).ne'
  rw [_root_.zpow_neg_one, mul_inv_eq_one₀ hl] at h1
  exact h1

/-- **$\tau^{\mathrm{reg}}(SO_2) = 2$ from the binary Siegel formula at one number** (the backwards step $1 \to 2$,
`docs/rank3-siegel-design.md` §2.2 option (ii)). If, for one totally positive $a$ with $\mathrm{repMass}(\mathcal O_F^2, a) \ne 0$,
Siegel's formula with $\varepsilon = \frac12$ holds,
$$\mathrm{repMass}(\mathcal O_F^2, a) = \tfrac12\,\mathrm{Mass}(\mathcal O_F^2)\cdot S^{\mathrm{reg}}_2(Q, a),$$
then $\tau^{\mathrm{reg}}(SO(Q)) = 2$. (With `two_mul_tamagawaKReg_mul_repMass`: $2\mu^{\mathrm{reg}}\,\mathrm{repMass} =
\mu^{\mathrm{reg}}\,\mathrm{Mass}\cdot S^{\mathrm{reg}}_2 = S^{\mathrm{reg}}_2$, so $\mu^{\mathrm{reg}}\,\mathrm{Mass} = 1$.) -/
theorem tauSOReg_eq_two_of_siegel (Q : QuadForm (𝓞 F) 2) (hpd : IsTotallyPosDef (formF Q))
    {a : 𝓞 F} (ha : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F a))
    (hne : repMass (formF Q) (stdLat F 2) (algebraMap (𝓞 F) F a) ≠ 0)
    (hS : repMass (formF Q) (stdLat F 2) (algebraMap (𝓞 F) F a) =
      (1 / 2 : ℝ) * mass (formF Q) (stdLat F 2) * siegelProduct2Reg Q a) :
    tauSOReg Q = 2 := by
  have hrep : ∃ ξ, (formF Q).eval ξ = algebraMap (𝓞 F) F a := by
    by_contra h; exact hne (repMass_eq_zero_of_not_rep _ _ h)
  have key := two_mul_tamagawaKReg_mul_repMass Q hpd ha hrep
  have hQ : Q.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  rw [tauSOReg_eq Q hQ hpd]
  rw [← key] at hS
  have h1 : (tamagawaKReg Q * mass (formF Q) (stdLat F 2) - 1) *
      repMass (formF Q) (stdLat F 2) (algebraMap (𝓞 F) F a) = 0 := by
    linear_combination -hS
  rcases mul_eq_zero.mp h1 with h | h
  · linear_combination 2 * h
  · exact absurd h hne

end QuadFormsKB.Tamagawa
