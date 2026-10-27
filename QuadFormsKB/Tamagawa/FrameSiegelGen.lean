/-
# Siegel's formula for representations of forms by forms, general (non-split) $Q_0$

**Layer:** $F$ a totally real number field; $Q_0$ a totally positive definite form of rank $N = r + n'$ over $\mathcal O_F$ that is **not**
assumed to be an orthogonal sum, $T_0$ of rank $r \ge 1$, $n' \ge 3$; $L = \mathcal O_F^N$.

This generalizes `siegelFormsAt_block` (`FrameSiegelMain.lean`, $Q_0 = T_0\perp Q_0'$) to a general $Q_0$ admitting a frame adapted to
$T_0$ (`AdaptedFrameT`, `FrameAdapted.lean`): $g \in \mathrm{GL}_N(F)$ and $Q'$ over $\mathcal O_F$ with $Q_0\circ g = T_0\perp Q'$.

**Proves**
* `archVolSO_mul_sq_pow`, `archDensityForm_mul_sq_pow` (**homogeneity**): $\mathrm{vol}(SO_N, c^2D)\,c^{N+1} = \mathrm{vol}(SO_N, D)$ and
  $\beta_\infty(c^2D_Q, D_T)\,c^{r} = \beta_\infty(D_Q, D_T)$ for $c, D > 0$;
* `arch_frame_scaled`: $\mathrm{vol}(SO_N, D_Q)\,(2^rD_T)^{n'} = \mathrm{vol}(SO_{n'}, D')\,\beta_\infty(Q, T)\,c^{n'+1}$ when
  $D_TD' = c^2D_Q$ (with $c = |\det g|_\sigma$): `archVolSO_blockForm` transported along $g$;
* **`siegelFormsAt_of_frame`**: `SiegelFormsAt Q₀ T₀`, given an adapted frame, the local identity at every prime
  (a hypothesis here; with the factor $\|\det g\|_\mathfrak p^{n'+1}$ coming from the change of lattice $g^{-1}\mathcal O_{F,\mathfrak p}^N$),
  $\tau(SO(Q')) = 2$ and the mass formula for $Q_0$.
  *Proof* (Weil 1982, §4.5 [unverified]): as for `siegelFormsAt_block`, after the transport
  $\mathrm{repMass}_T(Q_0, L) = \mathrm{repMass}_T(T_0\perp Q', g^{-1}L)$ (`repMassT_compMat`): the type sum of the lattice $g^{-1}L$ is a
  product of local type sums (`typeSumT_eq_finprod_gen`), the local factors are $\beta_\mathfrak p(Q_0,T_0) = W_\mathfrak p E_\mathfrak p\alpha_\mathfrak p/
  (\alpha'_\mathfrak p G_\mathfrak p)$ with $E_\mathfrak p = \|\det H_{T}\|_\mathfrak p^{n'}$, $G_\mathfrak p = \|\det g\|_\mathfrak p^{n'+1}$, and the product formula
  turns $\prod E_\mathfrak p$, $\prod G_\mathfrak p$ into the archimedean factors, which `arch_frame_scaled` matches.

Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.FrameSiegelMain
import QuadFormsKB.Tamagawa.FrameAdapted
import QuadFormsKB.Tamagawa.FrameGlobalGen

open NumberField Matrix
open scoped Real

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Frames

open QuadFormsKB.Tamagawa Lattices LocalDensity IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {r n' : ℕ}

/-! ### Homogeneity of the archimedean factors -/

theorem rpow_sq_mul_pow {c : ℝ} (hc : 0 < c) (m : ℕ) {s : ℝ} (hs : 2 * s + m = 0) :
    (c ^ 2) ^ s * c ^ m = 1 := by
  rw [← Real.rpow_natCast c 2, ← Real.rpow_mul hc.le, ← Real.rpow_natCast c m, ← Real.rpow_add hc]
  have : ((2 : ℕ) : ℝ) * s + (m : ℝ) = 0 := by push_cast; linarith
  rw [this, Real.rpow_zero]

/-- **Homogeneity of $\mathrm{vol}(SO_N, \cdot)$:** $\mathrm{vol}(SO_N, c^2D)\,c^{N+1} = \mathrm{vol}(SO_N, D)$ for $c, D > 0$. -/
theorem archVolSO_mul_sq_pow (N : ℕ) {c D : ℝ} (hc : 0 < c) (hD : 0 < D) :
    archVolSO N (c ^ 2 * D) * c ^ (N + 1) = archVolSO N D := by
  unfold archVolSO
  have hc2 : (c ^ 2) ^ (-((N : ℝ) + 1) / 2) * c ^ (N + 1) = 1 :=
    rpow_sq_mul_pow hc (N + 1) (by push_cast; ring)
  rw [Real.mul_rpow (by positivity) hD.le]
  have key : ∀ a Y P : ℝ, a * ((c ^ 2) ^ (-((N : ℝ) + 1) / 2) * Y) * P * c ^ (N + 1) = a * Y * P :=
    fun a Y P => by linear_combination (a * Y * P) * hc2
  exact key _ _ _

/-- **Homogeneity of $\beta_\infty$ in $D_Q$:** $\beta_\infty(c^2D_Q, D_T)\,c^r = \beta_\infty(D_Q, D_T)$ for $c, D_Q > 0$. -/
theorem archDensityForm_mul_sq_pow (N r : ℕ) (DT : ℝ) {c D : ℝ} (hc : 0 < c) (hD : 0 < D) :
    archDensityForm N r (c ^ 2 * D) DT * c ^ r = archDensityForm N r D DT := by
  unfold archDensityForm
  have hc2 : (c ^ 2) ^ (-(r : ℝ) / 2) * c ^ r = 1 := rpow_sq_mul_pow hc r (by ring)
  rw [Real.mul_rpow (by positivity) hD.le]
  have key : ∀ a Y : ℝ, a * ((c ^ 2) ^ (-(r : ℝ) / 2) * Y) * c ^ r = a * Y :=
    fun a Y => by linear_combination (a * Y) * hc2
  exact key _ _

/-- **The archimedean identity for an adapted frame** ($D_T, D', D_Q, c > 0$, $D_TD' = c^2D_Q$):
$$\mathrm{vol}(SO_N, D_Q)\,(2^rD_T)^{n'} = \mathrm{vol}(SO_{n'}, D')\,\beta_\infty(D_Q, D_T)\,c^{n'+1}.$$ -/
theorem arch_frame_scaled (r n' : ℕ) {DQ DT D' c : ℝ} (hDQ : 0 < DQ) (hDT : 0 < DT) (hD' : 0 < D') (hc : 0 < c)
    (h : DT * D' = c ^ 2 * DQ) :
    archVolSO (r + n') DQ * (2 ^ r * DT) ^ n' =
      archVolSO n' D' * archDensityForm (r + n') r DQ DT * c ^ (n' + 1) := by
  have hb := archVolSO_blockForm r n' hDT hD'
  rw [h] at hb
  have h1 := archVolSO_mul_sq_pow (r + n') hc hDQ
  have h2 := archDensityForm_mul_sq_pow (r + n') r DT hc hDQ
  linear_combination (-((2 : ℝ) ^ r * DT) ^ n') * h1 + c ^ (r + n' + 1) * hb +
    (archVolSO n' D' * c ^ (n' + 1)) * h2

/-! ### The theorem -/

/-- **Siegel's formula for $T_0$ by the genus of a general $Q_0$**, $N - r \ge 3$, given a frame adapted to $T_0$, the local identity at
every prime (with the lattice $g^{-1}\mathcal O_{F,\mathfrak p}^N$), $\tau(SO(Q')) = 2$ and the mass formula for $Q_0$:
$$\sum_{\mathrm{cls}M\subseteq\mathrm{gen}L}\frac{r_M(T_0)}{|O(M)|} = \mathrm{Mass}(L)\,|d_F|^{-r(2N-r-1)/4}\prod_\sigma\beta_\sigma(Q_0,T_0)
  \prod_\mathfrak p\beta_\mathfrak p(Q_0,T_0).$$
The local identity `hloc` at $\mathfrak p$ reads $W_\mathfrak p\,\lambda(Q_0,Q_0)\,\|\det H_{T_0}\|^{n'} = \lambda(Q',Q')\,\lambda(Q_0,T_0)\,\|\det g\|^{n'+1}$
($\lambda$ = `localDensityForm`, $W_\mathfrak p$ the local type sum at $g^{-1}\mathfrak o_\mathfrak p^N$). -/
@[kb "siegel1935" "Hauptsatz (forms by forms), general Q [unverified]"]
theorem siegelFormsAt_of_frame (Q₀ : QuadForm (𝓞 F) (r + n')) (T₀ : QuadForm (𝓞 F) r) (hr : 1 ≤ r) (hn' : 3 ≤ n')
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F)))
    (fr : AdaptedFrameT (Q₀.map (algebraMap (𝓞 F) F)) (T₀.map (algebraMap (𝓞 F) F)))
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F), locFrameTypeSumG v (T₀.map (algebraMap (𝓞 F) F))
      (fr.Q'.map (algebraMap (𝓞 F) F))
      (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v)) *
        NF.localDensityForm v Q₀ Q₀ * ‖algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ n' =
      NF.localDensityForm v fr.Q' fr.Q' * NF.localDensityForm v Q₀ T₀ *
        ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (n' + 1))
    (hτ' : TamagawaNumberTwo fr.Q') (hmass : MassFormulaHolds Q₀) : SiegelFormsAt Q₀ T₀ := by
  classical
  -- positivity and nondegeneracy
  have hpdB : IsTotallyPosDef (blockForm (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F))) := by
    rw [← fr.compMat_eq]; exact isTotallyPosDef_compMat _ fr.g hpd
  have hpdQ := isTotallyPosDef_of_blockForm_right hpdB
  have hT : T₀.Nondegenerate := nondegenerate_of_map hpdT.nondegenerate
  have hQ' : fr.Q'.Nondegenerate := nondegenerate_of_map hpdQ.nondegenerate
  have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  have hpdb : IsTotallyPosDef ((blockForm T₀ fr.Q').map (algebraMap (𝓞 F) F)) := by
    rw [map_blockForm]; exact hpdB
  -- the transported lattice
  obtain ⟨L', hL'⟩ : ∃ L' : Lat F (r + n'), L' = Lat.image fr.g⁻¹ (stdLat F (r + n')) := ⟨_, rfl⟩
  have hLi : IsIntegral (blockForm (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F))) L'.1 := by
    rw [hL', ← fr.compMat_eq]; exact isIntegral_compMat _ fr.g (isIntegral_stdLat_map Q₀)
  have hlocL : ∀ v : HeightOneSpectrum (𝓞 F), loc v L'.1 =
      locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v) := by
    intro v
    rw [hL']
    show loc v (glImage fr.g⁻¹ intVec) = _
    rw [loc_glImage, loc_intVec, map_inv]
  have h1 : repMassT (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F (r + n')) (T₀.map (algebraMap (𝓞 F) F)) =
      repMassT (blockForm (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F))) L'
        (T₀.map (algebraMap (𝓞 F) F)) := by
    rw [hL', ← fr.compMat_eq]
    exact (repMassT_compMat _ fr.g hpd (isIntegral_stdLat_map Q₀) _).symm
  have hrep := repMassT_eq_mass_mul (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F)) L'
    hpdB hLi hpdT.nondegenerate hpdQ (isIntegral_stdLat_map fr.Q')
  have hsum := typeSumT_eq_finprod_gen T₀ hT fr.Q' L' hpdb hLi
  have hmass' : MassFormulaHolds fr.Q' :=
    (massFormulaHolds_iff_tamagawaNumberTwo fr.Q' hQ' (by omega) hpdQ (isIntegral_stdLat_map fr.Q')).mpr hτ'
  unfold MassFormulaHolds at hmass hmass'
  refine ⟨?_⟩
  rw [h1, hrep, hsum, hmass, hmass']
  -- the local data
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
  obtain ⟨γ, hγ⟩ : ∃ γ : HeightOneSpectrum (𝓞 F) → ℝ, ∀ v, γ v = NF.siegelDensity v Q₀ T₀ := ⟨_, fun _ => rfl⟩
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
    have h3 : γ v = NF.localDensityForm v Q₀ T₀ := by
      rw [hγ]; unfold NF.siegelDensity; rw [if_neg (by omega), one_mul]
    have hpos : 0 < α' v := by rw [hα']; exact siegelDensity_pos v fr.Q' hQ'
    have hGv := hGpos v
    rw [h3, h1]
    rw [h2] at hpos ⊢
    rw [eq_div_iff (mul_pos hpos hGv).ne']
    linear_combination (-1 / 2 : ℝ) * hid
  -- finite supports
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
  have hGp : HasProd G (∏ᶠ v, G v) := by
    have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hGfin).hasProd
    rwa [tprod_eq_finprod hGfin] at this
  have hEpv : ∏ᶠ v, E v = ((∏ σ : F →ₐ[ℚ] ℂ, ‖σ x‖)⁻¹) ^ n' := by
    rw [← finprod_norm_pow_eq x hx n']
    exact finprod_congr hE
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
  -- the archimedean side
  have hnx : ∀ σ : F →ₐ[ℚ] ℂ, ‖σ x‖ = 2 ^ r * detGram T₀ σ := by
    intro σ
    unfold detGram
    rw [← hxdef, map_div₀, norm_div, map_pow, map_ofNat, norm_pow, Complex.norm_ofNat]
    field_simp
  -- `det H` of the block form is `(det g)^2 det H_{Q₀}`
  have hdet : algebraMap (𝓞 F) F (blockForm T₀ fr.Q').hessian.det =
      d ^ 2 * algebraMap (𝓞 F) F Q₀.hessian.det := by
    have hH := congrArg QuadForm.hessian fr.compMat_eq
    rw [QuadForm.hessian_compMat, ← map_blockForm, QuadForm.hessian_map, QuadForm.hessian_map] at hH
    have h2 := congrArg Matrix.det hH
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← hddef,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h2
    rw [← h2]; ring
  have hgram : ∀ σ : F →ₐ[ℚ] ℂ, detGram T₀ σ * detGram fr.Q' σ = ‖σ d‖ ^ 2 * detGram Q₀ σ := by
    intro σ
    rw [← detGram_blockForm]
    unfold detGram
    rw [hdet, mul_div_assoc, map_mul, norm_mul, map_pow, norm_pow]
  have hcpos : ∀ σ : F →ₐ[ℚ] ℂ, 0 < ‖σ d‖ := fun σ => norm_pos_iff.mpr ((map_ne_zero σ).mpr hd0)
  have harch : ∀ σ : F →ₐ[ℚ] ℂ, archVolSO (r + n') (detGram Q₀ σ) * ‖σ x‖ ^ n' =
      archVolSO n' (detGram fr.Q' σ) * archDensityForm (r + n') r (detGram Q₀ σ) (detGram T₀ σ) *
        ‖σ d‖ ^ (n' + 1) := by
    intro σ
    rw [hnx]
    exact arch_frame_scaled r n' (detGram_pos_frames Q₀ hQ σ) (detGram_pos_frames T₀ hT σ)
      (detGram_pos_frames fr.Q' hQ' σ) (hcpos σ) (hgram σ)
  have hprod : (∏ σ : F →ₐ[ℚ] ℂ, archVolSO (r + n') (detGram Q₀ σ)) * (∏ σ : F →ₐ[ℚ] ℂ, ‖σ x‖ ^ n') =
      (∏ σ : F →ₐ[ℚ] ℂ, archVolSO n' (detGram fr.Q' σ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archDensityForm (r + n') r (detGram Q₀ σ) (detGram T₀ σ)) *
        ∏ σ : F →ₐ[ℚ] ℂ, ‖σ d‖ ^ (n' + 1) := by
    calc _ = ∏ σ : F →ₐ[ℚ] ℂ, (archVolSO (r + n') (detGram Q₀ σ) * ‖σ x‖ ^ n') :=
          (Finset.prod_mul_distrib).symm
      _ = ∏ σ : F →ₐ[ℚ] ℂ, (archVolSO n' (detGram fr.Q' σ) *
            archDensityForm (r + n') r (detGram Q₀ σ) (detGram T₀ σ) * ‖σ d‖ ^ (n' + 1)) :=
          Finset.prod_congr rfl fun σ _ => harch σ
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hnxpos : ∀ σ : F →ₐ[ℚ] ℂ, 0 < ‖σ x‖ := fun σ => norm_pos_iff.mpr ((map_ne_zero σ).mpr hx)
  have hPn : 0 < ∏ σ : F →ₐ[ℚ] ℂ, ‖σ x‖ := Finset.prod_pos fun σ _ => hnxpos σ
  have hPd : 0 < ∏ σ : F →ₐ[ℚ] ℂ, ‖σ d‖ := Finset.prod_pos fun σ _ => hcpos σ
  have hVpos : 0 < ∏ σ : F →ₐ[ℚ] ℂ, archVolSO (r + n') (detGram Q₀ σ) :=
    Finset.prod_pos fun σ _ => QuadFormsKB.Tamagawa.ArchSOMeasure.archVolSO_pos _
      (detGram_pos_frames _ hQ σ)
  have hV'pos : 0 < ∏ σ : F →ₐ[ℚ] ℂ, archVolSO n' (detGram fr.Q' σ) :=
    Finset.prod_pos fun σ _ => QuadFormsKB.Tamagawa.ArchSOMeasure.archVolSO_pos _
      (detGram_pos_frames _ hQ' σ)
  have hV : (∏ σ : F →ₐ[ℚ] ℂ, archVolSO (r + n') (detGram Q₀ σ)) =
      (∏ σ : F →ₐ[ℚ] ℂ, archVolSO n' (detGram fr.Q' σ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archDensityForm (r + n') r (detGram Q₀ σ) (detGram T₀ σ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, ‖σ d‖) ^ (n' + 1) * ((∏ σ : F →ₐ[ℚ] ℂ, ‖σ x‖)⁻¹) ^ n' := by
    rw [Finset.prod_pow, Finset.prod_pow] at hprod
    have hne : (∏ σ : F →ₐ[ℚ] ℂ, ‖σ x‖) ^ n' ≠ 0 := by positivity
    rw [inv_pow, ← div_eq_mul_inv, eq_div_iff hne]
    exact hprod
  -- assemble
  have hε : epsNR (r + n') r = 1 := by unfold epsNR; rw [if_neg (by omega)]
  have hAeq : (∏' v : HeightOneSpectrum (𝓞 F), NF.siegelDensity v Q₀ Q₀) = ∏' v, α v := by rw [hαfun]
  have hA'eq : (∏' v : HeightOneSpectrum (𝓞 F), NF.siegelDensity v fr.Q' fr.Q') = ∏' v, α' v := by
    rw [hα'fun]
  have hγt : (∏' v : HeightOneSpectrum (𝓞 F), NF.siegelDensity v Q₀ T₀) = ∏' v, γ v := by
    rw [show (fun v => NF.siegelDensity v Q₀ T₀) = γ from (funext hγ).symm]
  have hWeq : (∏ᶠ v : HeightOneSpectrum (𝓞 F), locFrameTypeSumG v (T₀.map (algebraMap (𝓞 F) F))
      (fr.Q'.map (algebraMap (𝓞 F) F)) (loc v L'.1)) = ∏ᶠ v, W v :=
    finprod_congr fun v => by rw [hW, hlocL]
  unfold siegelProductT tamagawaK
  rw [show epsCodimOne (r + n') r = 1 from if_neg (by omega), one_mul]
  rw [hWeq, hAeq, hA'eq, hγt, hγp.tprod_eq, hEpv, hGpv, hε]
  simp only [one_mul]
  set δ := |(NumberField.discr F : ℝ)| with hδdef
  have hδ : 0 < δ := abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F)
  have hδe : δ ^ (-(((r + n' : ℕ) : ℝ) * (((r + n' : ℕ) : ℝ) - 1) / 4)) =
      δ ^ (-((n' : ℝ) * ((n' : ℝ) - 1) / 4)) *
        δ ^ (-((r : ℝ) * (2 * ((r + n' : ℕ) : ℝ) - r - 1)) / 4) := by
    rw [← Real.rpow_add hδ]; congr 1; push_cast; ring
  rw [hδe, hV]
  set V' := ∏ σ : F →ₐ[ℚ] ℂ, archVolSO n' (detGram fr.Q' σ)
  set R := ∏ σ : F →ₐ[ℚ] ℂ, archDensityForm (r + n') r (detGram Q₀ σ) (detGram T₀ σ)
  set Pg := ∏ σ : F →ₐ[ℚ] ℂ, ‖σ d‖ with hPgdef
  set Ep := ((∏ σ : F →ₐ[ℚ] ℂ, ‖σ x‖)⁻¹) ^ n' with hEpdef
  set Wt := ∏ᶠ v, W v
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
  have hPg : (Pg⁻¹) ^ (n' + 1) ≠ 0 := by positivity
  field_simp
  have hPg' : Pg ^ (n' + 1) ≠ 0 := by positivity
  rw [one_div, inv_pow, mul_assoc, mul_inv_cancel₀ hPg', mul_one]

end QuadFormsKB.Tamagawa.Frames
