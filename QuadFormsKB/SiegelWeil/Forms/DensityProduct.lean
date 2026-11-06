/-
# Siegel's product of forms-by-forms local densities converges
**Layer:** global, number fields. $F$ a totally real number field; $Q_0$ a totally positive definite quadratic form of rank $N$ and $T_0$ a
totally positive definite quadratic form of rank $r \ge 1$ over $\mathcal O_F$, with $N - r \ge 3$.

**Statement.** The Euler product of the local densities
$$\prod_{\mathfrak p}\beta_\mathfrak p(Q_0, T_0)$$
(`NF.localDensityForm`, product over the nonzero prime ideals of $\mathcal O_F$) is multipliable, with no hypothesis beyond total positive
definiteness and the ranks (`multipliable_localDensityForm`).

*Proof:* extracted from `siegelFormsAt_of_frame` (`Tamagawa/FrameSiegelGen`) and `siegelFormsAt_totallyReal_general`
(`Tamagawa/FrameSiegelUncond`). If $Q_0$ does not represent $T_0$ over $F$, some local density vanishes (`exists_local_not_rep`), and a
product with a vanishing factor is multipliable. Otherwise an adapted frame gives the local identity
$\beta_\mathfrak p(Q_0,T_0) = W_\mathfrak p E_\mathfrak p\alpha_\mathfrak p / (\alpha'_\mathfrak p G_\mathfrak p)$ at every prime, where
$W_\mathfrak p = 1$, $E_\mathfrak p = 1$ and $G_\mathfrak p = 1$ off a finite set, and $\alpha_\mathfrak p$, $\alpha'_\mathfrak p$ are the
(multipliable, positive-product) self-densities of $Q_0$ and of the complement $Q'$.

Sources: Siegel 1935 [unverified].

Indices are 0-based.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.FrameSiegelUncond

open NumberField Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

open QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Frames Lattices LocalDensity IsDedekindDomain QuadFormsKB.RegProd NFEuler
  QuadFormsKB.HilbertModular Filter

variable {F : Type} [Field F] [NumberField F] {N r : ℕ}

/-- **The product of local densities converges, given an adapted frame** ($n' \ge 3$): for $Q_0$ of rank $r + n'$ with a frame adapted to
$T_0$, the local identity at every prime and total positive definiteness, $\prod_\mathfrak p\beta_\mathfrak p(Q_0,T_0)$ is multipliable. -/
theorem multipliable_localDensityForm_of_frame [IsTotallyReal F] {n' : ℕ} (Q₀ : QuadForm (𝓞 F) (r + n')) (T₀ : QuadForm (𝓞 F) r)
    (hn' : 3 ≤ n')
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F)))
    (fr : AdaptedFrameT (Q₀.map (algebraMap (𝓞 F) F)) (T₀.map (algebraMap (𝓞 F) F)))
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F), locFrameTypeSumG v (T₀.map (algebraMap (𝓞 F) F))
      (fr.Q'.map (algebraMap (𝓞 F) F))
      (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v)) *
        NF.localDensityForm v Q₀ Q₀ * ‖algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ n' =
      NF.localDensityForm v fr.Q' fr.Q' * NF.localDensityForm v Q₀ T₀ *
        ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (n' + 1))
    (hr : 1 ≤ r) :
    Multipliable fun v : HeightOneSpectrum (𝓞 F) => NF.localDensityForm v Q₀ T₀ := by
  classical
  have hpdB : IsTotallyPosDef (blockForm (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F))) := by
    rw [← fr.compMat_eq]; exact isTotallyPosDef_compMat _ fr.g hpd
  have hpdQ := isTotallyPosDef_of_blockForm_right hpdB
  have hT : T₀.Nondegenerate := nondegenerate_of_map hpdT.nondegenerate
  have hQ' : fr.Q'.Nondegenerate := nondegenerate_of_map hpdQ.nondegenerate
  have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  obtain ⟨L', hL'⟩ : ∃ L' : Lat F (r + n'), L' = Lat.image fr.g⁻¹ (stdLat F (r + n')) := ⟨_, rfl⟩
  have hlocL : ∀ v : HeightOneSpectrum (𝓞 F), loc v L'.1 =
      locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v) := by
    intro v
    rw [hL']
    show loc v (glImage fr.g⁻¹ intVec) = _
    rw [loc_glImage, loc_intVec, map_inv]
  obtain ⟨x, hxdef⟩ : ∃ x : F, x = algebraMap (𝓞 F) F T₀.hessian.det := ⟨_, rfl⟩
  have hx : x ≠ 0 := by
    rw [hxdef]; exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hT
  obtain ⟨d, hddef⟩ : ∃ d : F, d = fr.g.val.det := ⟨_, rfl⟩
  have hd0 : d ≠ 0 := by
    rw [hddef]; exact (Matrix.isUnits_det_units fr.g).ne_zero
  obtain ⟨W, hW⟩ : ∃ W : HeightOneSpectrum (𝓞 F) → ℝ, ∀ v, W v =
      locFrameTypeSumG v (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F))
        (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : HeightOneSpectrum (𝓞 F) → ℝ, ∀ v,
      E v = ‖algebraMap F (v.adicCompletion F) x‖ ^ n' := ⟨_, fun _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : HeightOneSpectrum (𝓞 F) → ℝ, ∀ v,
      G v = ‖algebraMap F (v.adicCompletion F) d‖ ^ (n' + 1) := ⟨_, fun _ => rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : HeightOneSpectrum (𝓞 F) → ℝ, ∀ v, α v = NF.siegelDensity v Q₀ Q₀ := ⟨_, fun _ => rfl⟩
  obtain ⟨α', hα'⟩ : ∃ α' : HeightOneSpectrum (𝓞 F) → ℝ, ∀ v, α' v = NF.siegelDensity v fr.Q' fr.Q' :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : HeightOneSpectrum (𝓞 F) → ℝ, ∀ v, γ v = NF.localDensityForm v Q₀ T₀ :=
    ⟨_, fun _ => rfl⟩
  have hαfun : α = fun v => NF.siegelDensity v Q₀ Q₀ := funext hα
  have hα'fun : α' = fun v => NF.siegelDensity v fr.Q' fr.Q' := funext hα'
  have hGpos : ∀ v, 0 < G v := fun v => by
    rw [hG]
    exact pow_pos (norm_pos_iff.mpr ((map_ne_zero _).mpr hd0)) _
  have hγeq : ∀ v, γ v = W v * E v * α v / (α' v * G v) := by
    intro v
    have hid := hloc v
    rw [← hxdef, ← hddef, ← hE v, ← hG v, ← hW v] at hid
    have h1 : α v = 1 / 2 * NF.localDensityForm v Q₀ Q₀ := by
      rw [hα]; unfold NF.siegelDensity; rw [if_pos rfl]
    have h2 : α' v = 1 / 2 * NF.localDensityForm v fr.Q' fr.Q' := by
      rw [hα']; unfold NF.siegelDensity; rw [if_pos rfl]
    have hpos : 0 < α' v := by rw [hα']; exact siegelDensity_pos v fr.Q' hQ'
    have hGv := hGpos v
    rw [hγ, h1]
    rw [h2] at hpos ⊢
    rw [eq_div_iff (mul_pos hpos hGv).ne']
    linear_combination (-1 / 2 : ℝ) * hid
  set S := frameBadSetG T₀ hT L' with hS
  have hW1 : ∀ v ∉ S, W v = 1 := fun v hv => by
    obtain ⟨hv0, hL⟩ := not_mem_frameBadSetG T₀ hT L' hv
    rw [hW, ← hlocL v]
    exact locFrameTypeSumG_eq_one_of_good T₀ hT fr.Q' hQ' L' hL hv0
  have hWfin : Function.HasFiniteMulSupport W :=
    S.finite_toSet.subset fun v hv => by
      by_contra h; exact hv (hW1 v h)
  have hEfin : Function.HasFiniteMulSupport E :=
    (finite_valuation_ne_one hx).subset fun v hv => by
      by_contra h
      simp only [Set.mem_setOf_eq, not_not] at h
      apply hv
      rw [hE, norm_algebraMap_eq_one h, one_pow]
  have hGfin : Function.HasFiniteMulSupport G :=
    (finite_valuation_ne_one hd0).subset fun v hv => by
      by_contra h
      simp only [Set.mem_setOf_eq, not_not] at h
      apply hv
      rw [hG, norm_algebraMap_eq_one h, one_pow]
  have hαm : Multipliable α := by
    rw [hαfun]; exact multipliable_siegelDensity (N := r + n') (by omega) (by omega) _ hQ
  have hα'm : Multipliable α' := by
    rw [hα'fun]; exact multipliable_siegelDensity (N := n') (by omega) (by omega) _ hQ'
  have hA' : 0 < ∏' v, α' v := by
    rw [hα'fun]; exact tprod_siegelDensity_pos (N := n') (by omega) _ hQ'
  have hWp : HasProd W (∏ᶠ v, W v) := by
    have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hWfin).hasProd
    rwa [tprod_eq_finprod hWfin] at this
  have hEp : HasProd E (∏ᶠ v, E v) := by
    have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hEfin).hasProd
    rwa [tprod_eq_finprod hEfin] at this
  have hGp : HasProd G (∏ᶠ v, G v) := by
    have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hGfin).hasProd
    rwa [tprod_eq_finprod hGfin] at this
  have hGpv : ∏ᶠ v, G v = ((∏ σ : F →ₐ[ℚ] ℂ, ‖σ d‖)⁻¹) ^ (n' + 1) := by
    rw [← finprod_norm_pow_eq d hd0 (n' + 1)]
    exact finprod_congr hG
  have hGprodpos : 0 < ∏ᶠ v, G v := by
    rw [hGpv]
    have : 0 < ∏ σ : F →ₐ[ℚ] ℂ, ‖σ d‖ :=
      Finset.prod_pos fun σ _ => norm_pos_iff.mpr ((map_ne_zero σ).mpr hd0)
    positivity
  have hγp : HasProd γ ((∏ᶠ v, W v) * (∏ᶠ v, E v) * (∏' v, α v) / ((∏' v, α' v) * ∏ᶠ v, G v)) := by
    have hfun : γ = fun v => W v * E v * α v / (α' v * G v) := funext hγeq
    rw [hfun]
    exact ((hWp.mul hEp).mul hαm.hasProd).div₀ (hα'm.hasProd.mul hGp) (mul_pos hA' hGprodpos).ne'
  have hfun : (fun v : HeightOneSpectrum (𝓞 F) => NF.localDensityForm v Q₀ T₀) = γ :=
    funext fun v => (hγ v).symm
  rw [hfun]
  exact hγp.multipliable

/-- **Siegel's product of forms-by-forms local densities converges** ($N - r \ge 3$, every totally real field, unconditional): for
$Q_0$ totally positive definite of rank $N$ and $T_0$ totally positive definite of rank $r \ge 1$ over $\mathcal O_F$ with
$N - r \ge 3$, the Euler product $\prod_\mathfrak p\beta_\mathfrak p(Q_0, T_0)$ of the local densities
`NF.localDensityForm` over the nonzero prime ideals $\mathfrak p$ of $\mathcal O_F$ is multipliable.
*Proof:* if $Q_0$ does not represent $T_0$ over $F$, some local density is $0$ (`exists_local_not_rep`), so the product is trivially
multipliable; otherwise an adapted frame (`exists_adaptedFrameT`) and the local identity (`frameLocalIdentityGen`) express the factors
as a ratio of finite-support factors and the multipliable self-density products
(`multipliable_localDensityForm_of_frame`). -/
@[kb "siegel1935" "Hauptsatz (absolute convergence of the product of local densities, N - r ≥ 3) [unverified]"]
theorem multipliable_localDensityForm [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r)
    (hr : 1 ≤ r) (hrN : r + 3 ≤ N) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F))) :
    Multipliable fun v : HeightOneSpectrum (𝓞 F) => NF.localDensityForm v Q₀ T₀ := by
  obtain ⟨n', rfl⟩ : ∃ n', N = r + n' := ⟨N - r, by omega⟩
  by_cases h : ∃ X : Matrix (Fin (r + n')) (Fin r) F,
      (Q₀.map (algebraMap (𝓞 F) F)).compMat X = T₀.map (algebraMap (𝓞 F) F)
  · obtain ⟨X, hX⟩ := h
    obtain ⟨fr⟩ := exists_adaptedFrameT _ _ hpdT.nondegenerate X hX
    have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
    have hT : T₀.Nondegenerate := nondegenerate_of_map hpdT.nondegenerate
    exact multipliable_localDensityForm_of_frame Q₀ T₀ (by omega) hpd hpdT fr
      (fun v => frameLocalIdentityGen v Q₀ hQ T₀ hT fr) hr
  · obtain ⟨v, hv⟩ := exists_local_not_rep Q₀ T₀ hpd hpdT h
    have hT0 : T₀.Nondegenerate := nondegenerate_of_map hpdT.nondegenerate
    have h0 := localDensityForm_eq_zero_of_not_rep v Q₀ T₀ hT0 (by omega) hv
    exact multipliable_of_exists_eq_zero ⟨v, h0⟩

end QuadFormsKB.SiegelWeil.Forms
