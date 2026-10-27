/-
# Siegel's formula for representations of forms by forms, $N - r \ge 3$

**Layer:** $F$ a totally real number field; $Q = T_0\perp Q_0'$ over $\mathcal O_F$ totally positive definite, $T_0$ of rank $r \ge 1$, $Q_0'$ of
rank $n' = N - r \ge 3$; $L = \mathcal O_F^{N}$.

**Proves**
* `archVolSO_blockForm` (**the archimedean fibration for frames**): $\mathrm{vol}(SO_N, D_TD')\,(2^rD_T)^{n'} = \mathrm{vol}(SO_{n'}, D')\,\beta_\infty(Q, T)$,
  the frame version of `archVolSO_succ` (a computation with the closed form `archVolSO`);
* **`siegelFormsAt_block`**: `SiegelFormsAt (T₀ ⊥ Q₀') T₀`, given $\tau(SO(Q_0')) = 2$ and the mass formula in rank $N$:
  $$\sum_{\mathrm{cls}M\subseteq\mathrm{gen}L}\frac{r_M(T)}{|O(M)|} = \mathrm{Mass}(L)\,|d_F|^{-r(2N-r-1)/4}\prod_\sigma\beta_\sigma(Q,T)\prod_\mathfrak p\beta_\mathfrak p(Q,T).$$
  *Proof* (Weil 1982, §3.4–3.5, §4.5 [unverified]): $\mathrm{repMassT} = \mathrm{Mass}(\mathcal O_F^{n'})\sum_tw(t)$ (`repMassT_eq_mass_mul`),
  $\sum_tw(t) = \prod_{\mathfrak p\in S}W_\mathfrak p$ (`typeSumT_eq_prod`), the local identity at every prime (`frameLocalIdentity`), the mass
  formula in ranks $N$ and $n'$, the product formula for $\det H_T$ and the archimedean fibration;
* the named input **`ComplementTauTwo F n'`** ($\tau(SO) = 2$ for every totally positive definite form of rank $n'$) and
  `siegelFormsAt_block_of_input` (conditional on it only); **`complementTauTwo_totallyReal`** (it holds over every totally real $F$,
  $n' \ge 3$) and the unconditional **`siegelFormsAt_block_totallyReal`**.

Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.FrameSiegel
import QuadFormsKB.Tamagawa.FrameGlobal
import QuadFormsKB.Tamagawa.FrameLocalId
import QuadFormsKB.Tamagawa.TernaryTamagawaNF

open NumberField Matrix
open scoped Real

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Frames

open QuadFormsKB.Tamagawa Lattices LocalDensity IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {r n' : ℕ}

theorem detGram_blockForm (T₀ : QuadForm (𝓞 F) r) (Q₀' : QuadForm (𝓞 F) n') (σ : F →ₐ[ℚ] ℂ) :
    detGram (blockForm T₀ Q₀') σ = detGram T₀ σ * detGram Q₀' σ := by
  unfold detGram
  rw [det_hessian_blockForm, map_mul, pow_add, mul_div_mul_comm, map_mul, norm_mul]

/-- `IsTotallyPosDef` of an orthogonal sum gives it for the first summand. -/
theorem isTotallyPosDef_of_blockForm_left {T : QuadForm F r} {Q' : QuadForm F n'}
    (h : IsTotallyPosDef (blockForm T Q')) : IsTotallyPosDef T := by
  intro x hx
  have h1 : (Fin.append x (0 : Fin n' → F) : Fin (r + n') → F) ≠ 0 := by
    intro h0; apply hx; funext i
    simpa using congrFun h0 (Fin.castAdd n' i)
  have := h _ h1
  rw [QuadForm.eval, evalIn_blockForm] at this
  simpa [Fin.append, QuadForm.evalIn] using this

/-- `detGram` of a nondegenerate form is positive. -/
theorem detGram_pos_frames {m : ℕ} (Q : QuadForm (𝓞 F) m) (hQ : Q.Nondegenerate) (σ : F →ₐ[ℚ] ℂ) :
    0 < detGram Q σ := by
  refine norm_pos_iff.mpr ((map_ne_zero σ).mpr (div_ne_zero ?_ (pow_ne_zero _ two_ne_zero)))
  exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ

/-- The finite product of the powers $|x|_\mathfrak p^k$ over all primes, by the product formula. -/
theorem finprod_norm_pow_eq (x : F) (hx : x ≠ 0) (k : ℕ) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (v.adicCompletion F) x‖ ^ k =
      ((∏ σ : F →ₐ[ℚ] ℂ, ‖σ x‖)⁻¹) ^ k := by
  classical
  have hfin := finite_valuation_ne_one hx
  have h1 : ∀ v ∉ hfin.toFinset, ‖algebraMap F (v.adicCompletion F) x‖ = 1 := fun v hv =>
    norm_algebraMap_eq_one (by simpa using hv)
  rw [finprod_eq_prod_of_one hfin.toFinset (fun v hv => by simp [h1 v hv]), Finset.prod_pow,
    ← finprod_eq_prod_of_one hfin.toFinset h1, finprod_norm_eq x hx]

/-- **Siegel's formula for $T$ by the genus of $T\perp Q'$**, $N - r \ge 3$, given $\tau(SO(Q_0')) = 2$ and the mass formula for
$T_0\perp Q_0'$ (see the module docstring). -/
@[kb "siegel1935" "Hauptsatz (forms by forms) [unverified]"]
theorem siegelFormsAt_block (T₀ : QuadForm (𝓞 F) r) (Q₀' : QuadForm (𝓞 F) n') (hr : 1 ≤ r) (hn' : 3 ≤ n')
    (hpd : IsTotallyPosDef ((blockForm T₀ Q₀').map (algebraMap (𝓞 F) F)))
    (hτ' : TamagawaNumberTwo Q₀') (hmass : MassFormulaHolds (blockForm T₀ Q₀')) :
    SiegelFormsAt (blockForm T₀ Q₀') T₀ := by
  classical
  have hpdB := hpd
  rw [map_blockForm] at hpdB
  have hpdT := isTotallyPosDef_of_blockForm_left hpdB
  have hpdQ := isTotallyPosDef_of_blockForm_right hpdB
  have hT : T₀.Nondegenerate := nondegenerate_of_map hpdT.nondegenerate
  have hQ' : Q₀'.Nondegenerate := nondegenerate_of_map hpdQ.nondegenerate
  have hQ : (blockForm T₀ Q₀').Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  have hLi : IsIntegral (blockForm (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)))
      (stdLat F (r + n')).1 := by
    have := isIntegral_stdLat_map (blockForm T₀ Q₀')
    rwa [map_blockForm] at this
  have hrep := repMassT_eq_mass_mul (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F))
    (stdLat F (r + n')) hpdB hLi hpdT.nondegenerate hpdQ (isIntegral_stdLat_map Q₀')
  have hsum := typeSumT_eq_prod T₀ hT Q₀' hpd
  have hmass' : MassFormulaHolds Q₀' :=
    (massFormulaHolds_iff_tamagawaNumberTwo Q₀' hQ' (by omega) hpdQ (isIntegral_stdLat_map Q₀')).mpr hτ'
  unfold MassFormulaHolds at hmass hmass'
  rw [map_blockForm] at hmass
  refine ⟨?_⟩
  rw [map_blockForm, hrep, hsum, hmass, hmass']
  -- the local data
  obtain ⟨x, hxdef⟩ : ∃ x : F, x = algebraMap (𝓞 F) F T₀.hessian.det := ⟨_, rfl⟩
  have hx : x ≠ 0 := by
    rw [hxdef]; exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hT
  obtain ⟨W, hW⟩ : ∃ W : HeightOneSpectrum (𝓞 F) → ℝ, ∀ v, W v =
      locFrameTypeSum v (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) := ⟨_, fun _ => rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : HeightOneSpectrum (𝓞 F) → ℝ, ∀ v,
      E v = ‖algebraMap F (v.adicCompletion F) x‖ ^ n' := ⟨_, fun _ => rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : HeightOneSpectrum (𝓞 F) → ℝ, ∀ v,
      α v = NF.siegelDensity v (blockForm T₀ Q₀') (blockForm T₀ Q₀') := ⟨_, fun _ => rfl⟩
  obtain ⟨α', hα'⟩ : ∃ α' : HeightOneSpectrum (𝓞 F) → ℝ, ∀ v,
      α' v = NF.siegelDensity v Q₀' Q₀' := ⟨_, fun _ => rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : HeightOneSpectrum (𝓞 F) → ℝ, ∀ v,
      γ v = NF.siegelDensity v (blockForm T₀ Q₀') T₀ := ⟨_, fun _ => rfl⟩
  have hαfun : α = fun v => NF.siegelDensity v (blockForm T₀ Q₀') (blockForm T₀ Q₀') := funext hα
  have hα'fun : α' = fun v => NF.siegelDensity v Q₀' Q₀' := funext hα'
  have hγeq : ∀ v, γ v = W v * E v * α v / α' v := by
    intro v
    have hid := frameLocalIdentity v T₀ Q₀' hT hQ'
    rw [← hxdef, ← hE v, ← hW v] at hid
    have h1 : α v = 1 / 2 * NF.localDensityForm v (blockForm T₀ Q₀') (blockForm T₀ Q₀') := by
      rw [hα]; unfold NF.siegelDensity; rw [if_pos rfl]
    have h2 : α' v = 1 / 2 * NF.localDensityForm v Q₀' Q₀' := by
      rw [hα']; unfold NF.siegelDensity; rw [if_pos rfl]
    have h3 : γ v = NF.localDensityForm v (blockForm T₀ Q₀') T₀ := by
      rw [hγ]; unfold NF.siegelDensity; rw [if_neg (by omega), one_mul]
    have hpos : 0 < α' v := by rw [hα']; exact siegelDensity_pos v Q₀' hQ'
    rw [h3, h1]
    rw [h2] at hpos ⊢
    rw [eq_div_iff hpos.ne']
    linear_combination (-1 / 2 : ℝ) * hid
  -- finite supports
  set S := frameBadSet T₀ hT with hS
  have hW1 : ∀ v ∉ S, W v = 1 := fun v hv => by
    rw [hW]; exact locFrameTypeSum_eq_one T₀ hT Q₀' hQ' hv
  have hWfin : Function.HasFiniteMulSupport W :=
    S.finite_toSet.subset fun v hv => by
      by_contra h; exact hv (hW1 v h)
  have hEfin : Function.HasFiniteMulSupport E :=
    (finite_valuation_ne_one hx).subset fun v hv => by
      by_contra h
      simp only [Set.mem_setOf_eq, not_not] at h
      apply hv
      rw [hE, norm_algebraMap_eq_one h, one_pow]
  have hαm : Multipliable α := by
    rw [hαfun]; exact multipliable_siegelDensity (N := r + n') (by omega) (by omega) _ hQ
  have hα'm : Multipliable α' := by
    rw [hα'fun]; exact multipliable_siegelDensity (N := n') (by omega) (by omega) _ hQ'
  have hA : 0 < ∏' v, α v := by
    rw [hαfun]; exact tprod_siegelDensity_pos (N := r + n') (by omega) _ hQ
  have hA' : 0 < ∏' v, α' v := by
    rw [hα'fun]; exact tprod_siegelDensity_pos (N := n') (by omega) _ hQ'
  have hWp : HasProd W (∏ᶠ v, W v) := by
    have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hWfin).hasProd
    rwa [tprod_eq_finprod hWfin] at this
  have hEp : HasProd E (∏ᶠ v, E v) := by
    have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hEfin).hasProd
    rwa [tprod_eq_finprod hEfin] at this
  have hPS : ∏ᶠ v, W v = ∏ v ∈ S, W v := finprod_eq_prod_of_one S hW1
  have hEpv : ∏ᶠ v, E v = ((∏ σ : F →ₐ[ℚ] ℂ, ‖σ x‖)⁻¹) ^ n' := by
    rw [← finprod_norm_pow_eq x hx n']
    exact finprod_congr hE
  have hγp : HasProd γ ((∏ᶠ v, W v) * (∏ᶠ v, E v) * (∏' v, α v) / ∏' v, α' v) := by
    have hfun : γ = fun v => W v * E v * α v / α' v := funext hγeq
    rw [hfun]
    exact ((hWp.mul hEp).mul hαm.hasProd).div₀ hα'm.hasProd hA'.ne'
  -- the archimedean side
  have hnx : ∀ σ : F →ₐ[ℚ] ℂ, ‖σ x‖ = 2 ^ r * detGram T₀ σ := by
    intro σ
    unfold detGram
    rw [← hxdef, map_div₀, norm_div, map_pow, map_ofNat, norm_pow, Complex.norm_ofNat]
    field_simp
  have harch : ∀ σ : F →ₐ[ℚ] ℂ, archVolSO (r + n') (detGram (blockForm T₀ Q₀') σ) * ‖σ x‖ ^ n' =
      archVolSO n' (detGram Q₀' σ) *
        archDensityForm (r + n') r (detGram (blockForm T₀ Q₀') σ) (detGram T₀ σ) := by
    intro σ
    rw [hnx, detGram_blockForm]
    exact archVolSO_blockForm r n' (detGram_pos_frames T₀ hT σ) (detGram_pos_frames Q₀' hQ' σ)
  have hprod : (∏ σ : F →ₐ[ℚ] ℂ, archVolSO (r + n') (detGram (blockForm T₀ Q₀') σ)) *
      (∏ σ : F →ₐ[ℚ] ℂ, ‖σ x‖ ^ n') =
      (∏ σ : F →ₐ[ℚ] ℂ, archVolSO n' (detGram Q₀' σ)) *
        ∏ σ : F →ₐ[ℚ] ℂ, archDensityForm (r + n') r (detGram (blockForm T₀ Q₀') σ) (detGram T₀ σ) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun σ _ => harch σ
  have hnxpos : ∀ σ : F →ₐ[ℚ] ℂ, 0 < ‖σ x‖ := fun σ => norm_pos_iff.mpr ((map_ne_zero σ).mpr hx)
  have hPn : 0 < ∏ σ : F →ₐ[ℚ] ℂ, ‖σ x‖ := Finset.prod_pos fun σ _ => hnxpos σ
  have hVpos : 0 < ∏ σ : F →ₐ[ℚ] ℂ, archVolSO (r + n') (detGram (blockForm T₀ Q₀') σ) :=
    Finset.prod_pos fun σ _ => QuadFormsKB.Tamagawa.ArchSOMeasure.archVolSO_pos _
      (detGram_pos_frames _ hQ σ)
  have hV'pos : 0 < ∏ σ : F →ₐ[ℚ] ℂ, archVolSO n' (detGram Q₀' σ) :=
    Finset.prod_pos fun σ _ => QuadFormsKB.Tamagawa.ArchSOMeasure.archVolSO_pos _
      (detGram_pos_frames _ hQ' σ)
  have hV : (∏ σ : F →ₐ[ℚ] ℂ, archVolSO (r + n') (detGram (blockForm T₀ Q₀') σ)) =
      (∏ σ : F →ₐ[ℚ] ℂ, archVolSO n' (detGram Q₀' σ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archDensityForm (r + n') r (detGram (blockForm T₀ Q₀') σ) (detGram T₀ σ)) *
        ((∏ σ : F →ₐ[ℚ] ℂ, ‖σ x‖)⁻¹) ^ n' := by
    rw [Finset.prod_pow] at hprod
    have hne : (∏ σ : F →ₐ[ℚ] ℂ, ‖σ x‖) ^ n' ≠ 0 := by positivity
    rw [inv_pow, ← div_eq_mul_inv, eq_div_iff hne]
    exact hprod
  -- assemble
  have hε : epsNR (r + n') r = 1 := by unfold epsNR; rw [if_neg (by omega)]
  have hAeq : (∏' v : HeightOneSpectrum (𝓞 F), NF.siegelDensity v (blockForm T₀ Q₀') (blockForm T₀ Q₀')) =
      ∏' v, α v := by rw [hαfun]
  have hA'eq : (∏' v : HeightOneSpectrum (𝓞 F), NF.siegelDensity v Q₀' Q₀') = ∏' v, α' v := by rw [hα'fun]
  have hγt : (∏' v : HeightOneSpectrum (𝓞 F), NF.siegelDensity v (blockForm T₀ Q₀') T₀) = ∏' v, γ v := by
    rw [show (fun v => NF.siegelDensity v (blockForm T₀ Q₀') T₀) = γ from (funext hγ).symm]
  unfold siegelProductT tamagawaK
  rw [show epsCodimOne (r + n') r = 1 from if_neg (by omega), one_mul]
  rw [hAeq, hA'eq, hγt, hγp.tprod_eq, hPS, hEpv, hε]
  simp only [one_mul]
  set δ := |(NumberField.discr F : ℝ)| with hδdef
  have hδ : 0 < δ := abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F)
  have hδe : δ ^ (-(((r + n' : ℕ) : ℝ) * (((r + n' : ℕ) : ℝ) - 1) / 4)) =
      δ ^ (-((n' : ℝ) * ((n' : ℝ) - 1) / 4)) *
        δ ^ (-((r : ℝ) * (2 * ((r + n' : ℕ) : ℝ) - r - 1)) / 4) := by
    rw [← Real.rpow_add hδ]; congr 1; push_cast; ring
  rw [hδe, hV]
  set V' := ∏ σ : F →ₐ[ℚ] ℂ, archVolSO n' (detGram Q₀' σ)
  set R := ∏ σ : F →ₐ[ℚ] ℂ, archDensityForm (r + n') r (detGram (blockForm T₀ Q₀') σ) (detGram T₀ σ)
  set Ep := ((∏ σ : F →ₐ[ℚ] ℂ, ‖σ x‖)⁻¹) ^ n' with hEpdef
  have hEppos : 0 < Ep := by rw [hEpdef]; positivity
  have hRne : R ≠ 0 := by
    intro h
    have := hVpos
    rw [hV, h] at this
    simp at this
  have h1 := Real.rpow_pos_of_pos hδ (-((n' : ℝ) * ((n' : ℝ) - 1) / 4))
  have h2 := Real.rpow_pos_of_pos hδ (-((r : ℝ) * (2 * ((r + n' : ℕ) : ℝ) - r - 1)) / 4)
  have hA1 := hA.ne'
  have hA2 := hA'.ne'
  field_simp
  exact Finset.prod_congr rfl fun v _ => (hW v).symm

/-- **Input: $\tau(SO) = 2$ in rank $n'$** (Weil 1982, Thm. 4.5.1 [unverified]): for every totally positive definite form $Q_0'$ of rank $n'$
over $\mathcal O_F$, `TamagawaNumberTwo Q₀'`.

Field:
- `tau_eq_two`: the displayed statement.

*Independence:* a statement about orthogonal groups of rank $n'$ only; it mentions no representation numbers of forms of rank $r$, and
Siegel's formula for $T$ by $T\perp Q'$ needs in addition the local orbital identity for frames (proved) and the global reduction
(proved). It is a theorem over every totally real field for $n' \ge 3$ (`complementTauTwo_totallyReal`). -/
@[kb "weil1982" "Thm. 4.5.1 (τ(SO) = 2) [unverified]"]
structure ComplementTauTwo (F : Type) [Field F] [NumberField F] (n' : ℕ) : Prop where
  tau_eq_two : ∀ Q₀' : QuadForm (𝓞 F) n', IsTotallyPosDef (Q₀'.map (algebraMap (𝓞 F) F)) → TamagawaNumberTwo Q₀'

/-- `IsTotallyPosDef` of an orthogonal sum over $\mathcal O_F$ gives it for the second summand. -/
theorem isTotallyPosDef_of_blockForm_right₀ {T₀ : QuadForm (𝓞 F) r} {Q₀' : QuadForm (𝓞 F) n'}
    (hpd : IsTotallyPosDef ((blockForm T₀ Q₀').map (algebraMap (𝓞 F) F))) :
    IsTotallyPosDef (Q₀'.map (algebraMap (𝓞 F) F)) := by
  rw [map_blockForm] at hpd
  exact isTotallyPosDef_of_blockForm_right hpd

/-- **Siegel's formula for forms by forms, conditional on $\tau = 2$ in rank $n'$ only** ($N = r + n'$, $r \ge 1$, $n' \ge 3$; the mass
formula in rank $N \ge 4$ is `massFormula_all_ranks_totallyReal`). -/
@[kb "siegel1935" "Hauptsatz (forms by forms) [unverified]"]
theorem siegelFormsAt_block_of_input (hτ : ComplementTauTwo F n') (T₀ : QuadForm (𝓞 F) r) (Q₀' : QuadForm (𝓞 F) n')
    (hr : 1 ≤ r) (hn' : 3 ≤ n') (hpd : IsTotallyPosDef ((blockForm T₀ Q₀').map (algebraMap (𝓞 F) F))) :
    SiegelFormsAt (blockForm T₀ Q₀') T₀ :=
  siegelFormsAt_block T₀ Q₀' hr hn' hpd (hτ.tau_eq_two Q₀' (isTotallyPosDef_of_blockForm_right₀ hpd))
    (Measure.Weil.massFormula_all_ranks_totallyReal (by omega) _ hpd)

/-- **$\tau(SO) = 2$ in every rank $n' \ge 3$ over every totally real field** (`tamagawaNumberTwo_all_ranks_totallyReal` for $n' \ge 4$,
`ternaryTamagawaTwo_nf` for $n' = 3$). -/
theorem complementTauTwo_totallyReal (hn' : 3 ≤ n') : ComplementTauTwo F n' := by
  refine ⟨fun Q₀' hpd => ?_⟩
  rcases Nat.lt_or_ge n' 4 with h | h
  · obtain rfl : n' = 3 := by omega
    exact (QuadFormsKB.QuatOrder.ternaryTamagawaTwo_nf (F := F)).tau_eq_two Q₀'
      (nondegenerate_of_map hpd.nondegenerate) hpd (isIntegral_stdLat_map Q₀')
  · exact Measure.Weil.tamagawaNumberTwo_all_ranks_totallyReal h Q₀' hpd

/-- **Siegel's formula for representations of forms by forms over every totally real field** (unconditional): for $T_0$ of rank $r \ge 1$
and $Q_0'$ of rank $n' \ge 3$ over $\mathcal O_F$ with $T_0\perp Q_0'$ totally positive definite,
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(\mathcal O_F^{r+n'})}\frac{r_M(T_0)}{|O(M)|} = \mathrm{Mass}(\mathcal O_F^{r+n'})\cdot S(T_0\perp Q_0', T_0).$$ -/
@[kb "siegel1935" "Hauptsatz (forms by forms), N - r ≥ 3 [unverified]"]
theorem siegelFormsAt_block_totallyReal (T₀ : QuadForm (𝓞 F) r) (Q₀' : QuadForm (𝓞 F) n') (hr : 1 ≤ r) (hn' : 3 ≤ n')
    (hpd : IsTotallyPosDef ((blockForm T₀ Q₀').map (algebraMap (𝓞 F) F))) :
    SiegelFormsAt (blockForm T₀ Q₀') T₀ :=
  siegelFormsAt_block_of_input (complementTauTwo_totallyReal hn') T₀ Q₀' hr hn' hpd

end QuadFormsKB.Tamagawa.Frames
