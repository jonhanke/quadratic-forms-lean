/-
# Siegel's formula for representations of forms by forms in ranks $N \le 2$

**Layer:** $F$ a totally real number field; $Q_0$ a totally positive definite form of rank $N$ and $T_0$ a totally positive definite form of
rank $r \le N$ over $\mathcal O_F$; $L = \mathcal O_F^N$. In ranks $N \le 2$ the plain statement `SiegelFormsAt` (or `SiegelFormsAtReg`
with exponent $1$) is not the right one:

* for $N = 2$ the factors $\beta_\mathfrak p(Q_0, T_0)$ diverge as an Euler product, but the correction is the one of the **binary
  mass formula** (`tamagawaKReg`: exponent $-1$, character $\chi_{Q_0}$ = `chiP · Q₀`, and not the character $\chi$ of the complement);
* for $N = r = 1$ the Tamagawa measure is $\tau(SO_1) = 1$ while the mass of the genus is $\tfrac12$, so the $\varepsilon = \tfrac12$ of
  Siegel's formula appears once more than in `siegelProductT`: the formula is $\mathrm{repMass} = \mathrm{Mass}\cdot 2S$
  (the plain formula is false, `not_siegelFormulaAt_rankOne_int`).

**Defines**
* `siegelProductTRegWith χ e Q₀ T₀` $= S^{\chi,e}(Q, T)$: `siegelProductT` with $\prod_\mathfrak p\alpha_\mathfrak p(Q,T)$ replaced by
  $\mathrm{regProd}(\chi, e, \alpha_\bullet(Q,T)) = L_F(1,\chi)^e\prod_\mathfrak p\alpha_\mathfrak p(Q,T)(1-\chi(\mathfrak p)/N\mathfrak p)^e$;
  `siegelProductTReg` is the case $(\chi, e) = $ (`chiForms Q₀ T₀`, $1$) (`siegelProductTReg_eq_with`).

**Proves** (all unconditional, over every totally real $F$; Siegel 1935, Hauptsatz [unverified])
* **`siegelFormsBinaryOne_totallyReal`** ($N = 2$, $r = 1$): from the binary theorem `siegelFormulaAt2_nf`; Siegel's $\varepsilon = \tfrac12$
  is the global factor `epsCodimOne`;
* **`siegelFormsBinaryTwo_totallyReal`** ($N = r = 2$): the $n' = 0$ frame argument (`siegelFormsAt_full_aux`) with the regularized binary
  mass formula $\mathrm{Mass}(Q_0) = \mu^{\mathrm{reg}}_{\mathrm{Tam}}(Q_0)^{-1}$ (`tauSOReg_eq`, $\tau^{\mathrm{reg}}(SO_2) = 2$) instead of
  `MassFormulaHolds`;
* **`siegelFormsRankOne_totallyReal`** ($N = r = 1$): the same with $\mathrm{Mass}(Q_0) = \tfrac12$ (`mass_rankOne`) and
  $\mu_{\mathrm{Tam}}(K_{SO_1}) = 1$ (`tamagawaK_rankOne_eq_one`);
* in all three, if $Q_0$ does not represent $T_0$ over $F$ both sides vanish (`FrameHM.lean`).

Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.FrameSiegelSmall
import QuadFormsKB.Tamagawa.FrameSiegelReg
import QuadFormsKB.Tamagawa.FrameLocalGen
import QuadFormsKB.Tamagawa.FrameHM
import QuadFormsKB.Tamagawa.SiegelBinaryNF
import QuadFormsKB.Tamagawa.SiegelRankOne
import QuadFormsKB.Tamagawa.BinaryRegChange

open NumberField Matrix
open scoped Real

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Frames

open QuadFormsKB.Tamagawa Lattices LocalDensity IsDedekindDomain QuadFormsKB.RegProd NFEuler
  QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] {N r : ℕ}

/-- **Siegel's product for $T$ by $Q$ with a general regularization** (Siegel 1935, Hauptsatz [unverified]): `siegelProductT` with the
`tprod` $\prod_\mathfrak p\alpha_\mathfrak p(Q,T)$ replaced by $\mathrm{regProd}(\chi, e, \alpha_\bullet(Q,T))
= L_F(1,\chi)^e\prod_\mathfrak p\alpha_\mathfrak p(Q,T)(1-\chi(\mathfrak p)/N\mathfrak p)^e$:
$$S^{\chi,e}(Q,T) = \varepsilon'\,|d_F|^{-r(2N-r-1)/4}\prod_\sigma\varepsilon\,\beta_\sigma(Q,T)\cdot
  L_F(1,\chi)^e\prod_\mathfrak p\alpha_\mathfrak p(Q,T)\bigl(1-\chi(\mathfrak p)/N\mathfrak p\bigr)^e.$$
Here $\varepsilon = $ `epsNR N r` ($\tfrac12$ at every place if $r = N$) and $\varepsilon' = $ `epsCodimOne N r` ($\tfrac12$ once if $r = N - 1$).
`siegelProductTReg` is the case $\chi = $ `chiForms Q₀ T₀`, $e = 1$ (complement rank $2$); the binary mass formula uses
$\chi = $ `chiP · Q₀`, $e = -1$ (rank $N = 2$, $r \in \{1, 2\}$). -/
@[kb "siegel1935" "Hauptsatz (local side, forms by forms, general regularization) [unverified]"]
def siegelProductTRegWith (χ : HeightOneSpectrum (𝓞 F) → ℝ) (e : ℤ) (Q₀ : QuadForm (𝓞 F) N)
    (T₀ : QuadForm (𝓞 F) r) : ℝ :=
  epsCodimOne N r * |(discr F : ℝ)| ^ (-((r : ℝ) * (2 * N - r - 1)) / 4) *
    (∏ σ : F →ₐ[ℚ] ℂ, epsNR N r * archDensityForm N r (detGram Q₀ σ) (detGram T₀ σ)) *
    regProd χ e (fun v => NF.siegelDensity v Q₀ T₀)

/-- `siegelProductTReg` is `siegelProductTRegWith (chiForms Q₀ T₀) 1`. -/
theorem siegelProductTReg_eq_with (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r) :
    siegelProductTReg Q₀ T₀ = siegelProductTRegWith (chiForms Q₀ T₀) 1 Q₀ T₀ := rfl

variable [IsTotallyReal F]

/-! ### The full-rank frame argument ($n' = 0$) without a mass formula -/

/-- $D_T\cdot D' = c^2D_Q$ for $n' = 0$ ($D' = 1$): the determinants of $T_0 = Q_0\circ g$. -/
private theorem detGram_frame_zero (Q₀ : QuadForm (𝓞 F) (r + 0)) (T₀ : QuadForm (𝓞 F) r)
    (fr : AdaptedFrameT (Q₀.map (algebraMap (𝓞 F) F)) (T₀.map (algebraMap (𝓞 F) F))) (σ : F →ₐ[ℚ] ℂ) :
    detGram T₀ σ * detGram fr.Q' σ = ‖σ fr.g.val.det‖ ^ 2 * detGram Q₀ σ := by
  have hdet : algebraMap (𝓞 F) F (blockForm T₀ fr.Q').hessian.det =
      fr.g.val.det ^ 2 * algebraMap (𝓞 F) F Q₀.hessian.det := by
    have hH := congrArg QuadForm.hessian fr.compMat_eq
    rw [QuadForm.hessian_compMat, ← map_blockForm, QuadForm.hessian_map, QuadForm.hessian_map] at hH
    have h2 := congrArg Matrix.det hH
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h2
    rw [← h2]; ring
  rw [← detGram_blockForm]
  unfold detGram
  rw [hdet]
  simp only [map_div₀, map_mul, map_pow, norm_div, norm_mul, norm_pow]
  ring

/-- **The $n' = 0$ frame argument with all the local and archimedean data** (no mass formula): for $Q_0$, $T_0$ totally positive
definite of the same rank $r$ and a frame $Q_0\circ g = T_0$, there are local factors $W_\mathfrak p$ (finite support, the local type
sums) and $G_\mathfrak p = \|\det g\|_\mathfrak p > 0$ (with $\prod_\mathfrak p G_\mathfrak p = P_g^{-1}$, $P_g = \prod_\sigma|\sigma\det g|$) such that
`repMassT` $= \prod_\mathfrak p W_\mathfrak p$, $\alpha_\mathfrak p(Q_0,T_0) = W_\mathfrak p\,\alpha_\mathfrak p(Q_0,Q_0)/G_\mathfrak p$ and
$\prod_\sigma\mathrm{vol}(SO_r, D_Q) = \prod_\sigma\tfrac12\beta_\sigma(Q_0,T_0)\cdot P_g$. -/
private theorem zero_core {r : ℕ} (Q₀ : QuadForm (𝓞 F) (r + 0)) (T₀ : QuadForm (𝓞 F) r)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F)))
    (fr : AdaptedFrameT (Q₀.map (algebraMap (𝓞 F) F)) (T₀.map (algebraMap (𝓞 F) F))) :
    ∃ (W G : HeightOneSpectrum (𝓞 F) → ℝ) (Pg : ℝ), 0 < Pg ∧ (∀ v, 0 < G v) ∧
      HasProd W (∏ᶠ v, W v) ∧ HasProd G Pg⁻¹ ∧
      (∀ v, NF.siegelDensity v Q₀ T₀ = W v * NF.siegelDensity v Q₀ Q₀ / G v) ∧
      repMassT (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F (r + 0)) (T₀.map (algebraMap (𝓞 F) F)) = ∏ᶠ v, W v ∧
      (∏ σ : F →ₐ[ℚ] ℂ, archVolSO (r + 0) (detGram Q₀ σ)) =
        (∏ σ : F →ₐ[ℚ] ℂ, (1 / 2 * archDensityForm (r + 0) r (detGram Q₀ σ) (detGram T₀ σ))) * Pg := by
  classical
  have hpdB : IsTotallyPosDef (blockForm (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F))) := by
    rw [← fr.compMat_eq]; exact isTotallyPosDef_compMat _ fr.g hpd
  have hpdQ := isTotallyPosDef_of_blockForm_right hpdB
  have hT : T₀.Nondegenerate := nondegenerate_of_map hpdT.nondegenerate
  have hQ' : fr.Q'.Nondegenerate := nondegenerate_of_map hpdQ.nondegenerate
  have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  have hpdb : IsTotallyPosDef ((blockForm T₀ fr.Q').map (algebraMap (𝓞 F) F)) := by
    rw [map_blockForm]; exact hpdB
  -- the transported lattice
  obtain ⟨L', hL'⟩ : ∃ L' : Lat F (r + 0), L' = Lat.image fr.g⁻¹ (stdLat F (r + 0)) := ⟨_, rfl⟩
  have hLi : IsIntegral (blockForm (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F))) L'.1 := by
    rw [hL', ← fr.compMat_eq]; exact isIntegral_compMat _ fr.g (isIntegral_stdLat_map Q₀)
  have hlocL : ∀ v : HeightOneSpectrum (𝓞 F), loc v L'.1 =
      locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v) := by
    intro v
    rw [hL']
    show loc v (glImage fr.g⁻¹ intVec) = _
    rw [loc_glImage, loc_intVec, map_inv]
  have h1 : repMassT (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F (r + 0)) (T₀.map (algebraMap (𝓞 F) F)) =
      repMassT (blockForm (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F))) L'
        (T₀.map (algebraMap (𝓞 F) F)) := by
    rw [hL', ← fr.compMat_eq]
    exact (repMassT_compMat _ fr.g hpd (isIntegral_stdLat_map Q₀) _).symm
  have hrep := repMassT_eq_mass_mul (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F)) L'
    hpdB hLi hpdT.nondegenerate hpdQ (isIntegral_stdLat_map fr.Q')
  have hsum := typeSumT_eq_finprod_gen T₀ hT fr.Q' L' hpdb hLi
  -- the zero-variable complement
  have hmass0 : mass (fr.Q'.map (algebraMap (𝓞 F) F)) (stdLat F 0) = 1 := mass_rank_zero _ _
  have hlam : ∀ v : HeightOneSpectrum (𝓞 F), NF.localDensityForm v fr.Q' fr.Q' = 1 :=
    fun v => localDensityForm_rank_zero v _
  have hD'1 : ∀ σ : F →ₐ[ℚ] ℂ, detGram fr.Q' σ = 1 := fun σ => detGram_rank_zero _ σ
  -- the local data
  obtain ⟨d, hddef⟩ : ∃ d : F, d = fr.g.val.det := ⟨_, rfl⟩
  have hd0 : d ≠ 0 := by
    rw [hddef]; exact (Matrix.isUnits_det_units fr.g).ne_zero
  obtain ⟨W, hW⟩ : ∃ W : HeightOneSpectrum (𝓞 F) → ℝ, ∀ v, W v =
      locFrameTypeSumG v (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F))
        (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : HeightOneSpectrum (𝓞 F) → ℝ, ∀ v,
      G v = ‖algebraMap F (v.adicCompletion F) d‖ ^ (0 + 1) := ⟨_, fun _ => rfl⟩
  have hGpos : ∀ v, 0 < G v := fun v => by
    rw [hG]
    exact pow_pos (norm_pos_iff.mpr ((map_ne_zero _).mpr hd0)) _
  have hγeq : ∀ v, NF.siegelDensity v Q₀ T₀ = W v * NF.siegelDensity v Q₀ Q₀ / G v := by
    intro v
    have hid := frameLocalIdentityGen v Q₀ hQ T₀ hT fr
    have hE1 : ‖algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ 0 = 1 := pow_zero _
    rw [hE1, hlam v, ← hddef, ← hG v, ← hW v] at hid
    have h1 : NF.siegelDensity v Q₀ Q₀ = 1 / 2 * NF.localDensityForm v Q₀ Q₀ := by
      unfold NF.siegelDensity; rw [if_pos rfl]
    have h3 : NF.siegelDensity v Q₀ T₀ = 1 / 2 * NF.localDensityForm v Q₀ T₀ := by
      unfold NF.siegelDensity; rw [if_pos (by omega)]
    have hGv := hGpos v
    rw [h3, h1, eq_div_iff hGv.ne']
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
  have hGfin : Function.HasFiniteMulSupport G :=
    (finite_valuation_ne_one hd0).subset fun v hv => by
      by_contra h
      simp only [Set.mem_setOf_eq, not_not] at h
      apply hv
      rw [hG, norm_algebraMap_eq_one h, one_pow]
  have hWp : HasProd W (∏ᶠ v, W v) := by
    have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hWfin).hasProd
    rwa [tprod_eq_finprod hWfin] at this
  have hGp : HasProd G (∏ᶠ v, G v) := by
    have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hGfin).hasProd
    rwa [tprod_eq_finprod hGfin] at this
  have hGpv : ∏ᶠ v, G v = (∏ σ : F →ₐ[ℚ] ℂ, ‖σ d‖)⁻¹ := by
    calc ∏ᶠ v, G v = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (v.adicCompletion F) d‖ ^ (0 + 1) :=
          finprod_congr hG
      _ = ((∏ σ : F →ₐ[ℚ] ℂ, ‖σ d‖)⁻¹) ^ (0 + 1) := finprod_norm_pow_eq d hd0 _
      _ = _ := by rw [zero_add, pow_one]
  have hcpos : ∀ σ : F →ₐ[ℚ] ℂ, 0 < ‖σ d‖ := fun σ => norm_pos_iff.mpr ((map_ne_zero σ).mpr hd0)
  have hPd : 0 < ∏ σ : F →ₐ[ℚ] ℂ, ‖σ d‖ := Finset.prod_pos fun σ _ => hcpos σ
  -- the archimedean side
  have hgram : ∀ σ : F →ₐ[ℚ] ℂ, detGram T₀ σ * detGram fr.Q' σ = ‖σ d‖ ^ 2 * detGram Q₀ σ := by
    intro σ
    rw [hddef]; exact detGram_frame_zero Q₀ T₀ fr σ
  have harch : ∀ σ : F →ₐ[ℚ] ℂ, archVolSO (r + 0) (detGram Q₀ σ) =
      1 / 2 * archDensityForm (r + 0) r (detGram Q₀ σ) (detGram T₀ σ) * ‖σ d‖ := by
    intro σ
    have hDQ := detGram_pos_frames Q₀ hQ σ
    have hDT := detGram_pos_frames T₀ hT σ
    have hD' := detGram_pos_frames fr.Q' hQ' σ
    have hc := hcpos σ
    have A := archVolSO_blockForm r 0 hDT hD'
    rw [hgram σ, archVolSO_scale (r + 0) hc hDQ, archDensityForm_scale (r + 0) r hc hDQ, hD'1 σ,
      archVolSO_zero_one, pow_zero, mul_one] at A
    have hck : ‖σ d‖ ^ (r + 0 + 1) = ‖σ d‖ ^ r * ‖σ d‖ := by ring
    rw [hck] at A
    have h1 : ‖σ d‖ ^ r ≠ 0 := by positivity
    field_simp at A
    field_simp
    linarith
  refine ⟨W, G, ∏ σ : F →ₐ[ℚ] ℂ, ‖σ d‖, hPd, hGpos, hWp, ?_, hγeq, ?_, ?_⟩
  · rw [← hGpv]; exact hGp
  · rw [h1, hrep, hsum, hmass0, one_mul]
    exact finprod_congr fun v => by rw [hlocL v, hW]
  · rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun σ _ => harch σ

/-! ### Rank one: $N = r = 1$ -/

/-- **Siegel's formula for a form by a form in rank one** ($N = r = 1$; Siegel 1935, Hauptsatz, $\varepsilon = \tfrac12$ for $r = N$
[unverified]): for $Q_0 = \langle a\rangle$, $T_0 = \langle b\rangle$ totally positive over $\mathcal O_F$,
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(T_0)}{|O(M)|} = \mathrm{Mass}(L)\cdot 2\,S(Q_0, T_0),\qquad
  S = \prod_\sigma\tfrac12\beta_\sigma(Q_0,T_0)\prod_\mathfrak p\tfrac12\beta_\mathfrak p(Q_0,T_0),$$
i.e. `repMassT = mass * (2 * siegelProductT Q₀ T₀)`. The plain formula `SiegelFormsAt Q₀ T₀` is **false** in rank one
(`not_siegelFormulaAt_rankOne_int`): there $\mathrm{Mass}(L) = \tfrac12$ (`mass_rankOne`, $O(L) = \{\pm1\}$) but the Tamagawa measure is
$\tau(SO_1) = 1$ (`tamagawaK_rankOne_eq_one`), so the factor $\tfrac12$ of Siegel's $\varepsilon$ must not be applied once more.
Both sides are $0$ unless $a x^2 = b$ is solvable over $F$ (then $b/a$ is a square).

*Proof.* If $Q_0$ does not represent $T_0$ over $F$, then `repMassT` $= 0$ and some local density vanishes (`FrameHM.lean`). Otherwise an
adapted frame $Q_0\circ g = T_0$ ($n' = 0$) gives `repMassT` $= \prod_\mathfrak p W_\mathfrak p$ and
$\alpha_\mathfrak p(Q_0,T_0) = W_\mathfrak p\,\alpha_\mathfrak p(Q_0,Q_0)/\|\det g\|_\mathfrak p$ (`frameLocalIdentityGen`); the archimedean factors
satisfy $\mathrm{vol}(SO_1, D_Q) = \tfrac12\beta_\sigma\,|\sigma\det g|$, and $\mu_{\mathrm{Tam}}(K_{SO_1}) = 1$ turns the product into
$S(Q_0,T_0) = \prod_\mathfrak p W_\mathfrak p$. -/
@[kb "siegel1935" "Hauptsatz (forms by forms), N = r = 1 (τ(SO₁) = 1, ε = 1/2 once more) [unverified]"]
theorem siegelFormsRankOne_totallyReal (Q₀ T₀ : QuadForm (𝓞 F) 1)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F))) :
    repMassT (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F 1) (T₀.map (algebraMap (𝓞 F) F)) =
      mass (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F 1) * (2 * siegelProductT Q₀ T₀) := by
  classical
  have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  by_cases h : ∃ X : Matrix (Fin 1) (Fin 1) F,
      (Q₀.map (algebraMap (𝓞 F) F)).compMat X = T₀.map (algebraMap (𝓞 F) F)
  · obtain ⟨X, hX⟩ := h
    obtain ⟨fr⟩ := exists_adaptedFrameT (n' := 0) (Q₀.map (algebraMap (𝓞 F) F))
      (T₀.map (algebraMap (𝓞 F) F)) hpdT.nondegenerate X hX
    obtain ⟨W, G, Pg, hPg, hGpos, hWp, hGp, hγ, hrep, harch⟩ := zero_core (r := 1) Q₀ T₀ hpd hpdT fr
    have hαfin : Function.HasFiniteMulSupport fun v => NF.siegelDensity v Q₀ Q₀ :=
      (finite_badPrimes Q₀ hQ).subset fun v hv => by
        by_contra h
        exact hv (RankOne.siegelDensity_rankOne_good Q₀ hQ v h)
    have hαp : HasProd (fun v => NF.siegelDensity v Q₀ Q₀) (∏ᶠ v, NF.siegelDensity v Q₀ Q₀) := by
      have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hαfin).hasProd
      rwa [tprod_eq_finprod hαfin] at this
    have hγp : HasProd (fun v => NF.siegelDensity v Q₀ T₀)
        ((∏ᶠ v, W v) * (∏ᶠ v, NF.siegelDensity v Q₀ Q₀) / Pg⁻¹) := by
      rw [show (fun v => NF.siegelDensity v Q₀ T₀) = fun v => W v * NF.siegelDensity v Q₀ Q₀ / G v from funext hγ]
      exact (hWp.mul hαp).div₀ hGp (inv_pos.mpr hPg).ne'
    have hK : tamagawaK Q₀ = 1 := TauSOOne.tamagawaK_rankOne_eq_one Q₀ hQ
    have hmass : mass (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F 1) = 1 / 2 := by
      refine RankOne.mass_rankOne ?_ _
      intro h0
      apply hpd.nondegenerate
      show (Q₀.map (algebraMap (𝓞 F) F)).hessian.det = 0
      rw [Matrix.det_unique, Fin.default_eq_zero, RankOne.hessian_rankOne, h0, mul_zero]
    have hε : epsNR 1 1 = 1 / 2 := by unfold epsNR; rw [if_pos rfl]
    have hε' : epsCodimOne 1 1 = 1 := by unfold epsCodimOne; rw [if_neg (by omega)]
    have hexp : (-(((1 : ℕ) : ℝ) * (2 * ((1 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) - 1)) / 4) = 0 := by norm_num
    unfold tamagawaK at hK
    rw [hrep, hmass]
    unfold siegelProductT
    rw [hε, hε', hexp, Real.rpow_zero, hγp.tprod_eq]
    have hV : (∏ σ : F →ₐ[ℚ] ℂ, archVolSO 1 (detGram Q₀ σ)) =
        (∏ σ : F →ₐ[ℚ] ℂ, (1 / 2 * archDensityForm 1 1 (detGram Q₀ σ) (detGram T₀ σ))) * Pg := harch
    rw [tprod_eq_finprod hαfin] at hK
    simp only [Nat.cast_one, sub_self, mul_zero, zero_div, neg_zero, Real.rpow_zero, one_mul] at hK
    rw [hV] at hK
    generalize (∏ σ : F →ₐ[ℚ] ℂ, (1 / 2 * archDensityForm 1 1 (detGram Q₀ σ) (detGram T₀ σ))) = R at hK ⊢
    generalize (∏ᶠ v, W v) = Wt
    rw [div_inv_eq_mul]
    linear_combination (-Wt) * hK
  · rw [repMassT_eq_zero_of_not_rep _ _ _ h]
    have h0 := tprod_siegelDensity_eq_zero_of_not_rep Q₀ T₀ le_rfl hpd hpdT h
    unfold siegelProductT
    rw [h0]
    ring

/-! ### Binary forms by binary forms: $N = r = 2$ -/

/-- **Siegel's formula for a binary form by a binary form** ($N = r = 2$; Siegel 1935, Hauptsatz, $\varepsilon = \tfrac12$ for $r = N$
[unverified]): for $Q_0$, $T_0$ totally positive definite binary forms over $\mathcal O_F$,
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(T_0)}{|O(M)|} = \mathrm{Mass}(L)\cdot|d_F|^{-1/2}\prod_\sigma\tfrac12\beta_\sigma(Q_0,T_0)\cdot
  L_F(1,\chi_{Q_0})^{-1}\prod_\mathfrak p\tfrac12\beta_\mathfrak p(Q_0,T_0)\bigl(1-\chi_{Q_0}(\mathfrak p)/N\mathfrak p\bigr)^{-1},$$
i.e. `repMassT = mass * siegelProductTRegWith (chiP · Q₀) (-1) Q₀ T₀` with the character $\chi_{Q_0}$ = `chiP · Q₀` of the *binary*
form $Q_0$ (the character of the regularized mass formula `tamagawaKReg`), exponent $-1$. For $T_0 = Q_0$ it is the
regularized binary mass formula.

*Proof.* If $Q_0$ does not represent $T_0$ over $F$ both sides vanish (`FrameHM.lean`; a zero factor in the `regProd`). Otherwise an adapted
frame $Q_0\circ g = T_0$ ($n' = 0$) gives `repMassT` $= \prod_\mathfrak p W_\mathfrak p$ and the local identity
$\alpha_\mathfrak p(Q_0,T_0) = W_\mathfrak p\,\alpha_\mathfrak p(Q_0,Q_0)/\|\det g\|_\mathfrak p$ (`frameLocalIdentityGen`), so the corrected factors
$\alpha_\mathfrak p(Q_0,T_0)(1-\chi/N\mathfrak p)^{-1} = W_\mathfrak p\,[\alpha_\mathfrak p(Q_0,Q_0)(1-\chi/N\mathfrak p)^{-1}]/\|\det g\|_\mathfrak p$ have a convergent product (the
bracket has finite support, `hasFiniteMulSupport_siegelDensity_binary_reg`) and the $L$-values cancel against those of
$\mu^{\mathrm{reg}}_{\mathrm{Tam}}(K_{SO}(Q_0))$; the mass formula is $\mathrm{Mass}(Q_0) = \mu^{\mathrm{reg}}_{\mathrm{Tam}}(Q_0)^{-1}$
(`tauSOReg_eq`, $\tau^{\mathrm{reg}}(SO_2) = 2$, `binaryTamagawaTwoReg_nf`). -/
@[kb "siegel1935" "Hauptsatz (forms by forms), N = r = 2 (regularized binary mass formula) [unverified]"]
theorem siegelFormsBinaryTwo_totallyReal (Q₀ T₀ : QuadForm (𝓞 F) 2)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F))) :
    repMassT (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F 2) (T₀.map (algebraMap (𝓞 F) F)) =
      mass (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F 2) *
        siegelProductTRegWith (fun v => chiP v Q₀) (-1) Q₀ T₀ := by
  classical
  have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  by_cases h : ∃ X : Matrix (Fin 2) (Fin 2) F,
      (Q₀.map (algebraMap (𝓞 F) F)).compMat X = T₀.map (algebraMap (𝓞 F) F)
  · obtain ⟨X, hX⟩ := h
    obtain ⟨fr⟩ := exists_adaptedFrameT (n' := 0) (Q₀.map (algebraMap (𝓞 F) F))
      (T₀.map (algebraMap (𝓞 F) F)) hpdT.nondegenerate X hX
    obtain ⟨W, G, Pg, hPg, hGpos, hWp, hGp, hγ, hrep, harch⟩ := zero_core (r := 2) Q₀ T₀ hpd hpdT fr
    set χ : HeightOneSpectrum (𝓞 F) → ℝ := fun v => chiP v Q₀ with hχdef
    have hχ : ∀ v, |χ v| ≤ 1 := fun v => abs_chiP_le Q₀ v
    have hlam : ∀ v, 0 < 1 - χ v / (normP v : ℝ) := fun v => one_sub_div_pos (hχ v) v
    -- the corrected binary factors of `Q₀` have finite support
    obtain ⟨g, hg⟩ : ∃ g : HeightOneSpectrum (𝓞 F) → ℝ, ∀ v,
        g v = NF.siegelDensity v Q₀ Q₀ * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ) := ⟨_, fun _ => rfl⟩
    have hgfin : Function.HasFiniteMulSupport g := by
      have := hasFiniteMulSupport_siegelDensity_binary_reg hQ ∅ (χ := χ) fun _ _ => rfl
      rwa [show g = fun v => NF.siegelDensity v Q₀ Q₀ * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ) from funext hg]
    have hgp : HasProd g (∏ᶠ v, g v) := by
      have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hgfin).hasProd
      rwa [tprod_eq_finprod hgfin] at this
    have hγreg : HasProd (fun v => NF.siegelDensity v Q₀ T₀ * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ))
        ((∏ᶠ v, W v) * (∏ᶠ v, g v) / Pg⁻¹) := by
      refine ((hWp.mul hgp).div₀ hGp (inv_pos.mpr hPg).ne').congr_fun fun v => ?_
      rw [hγ v, hg v]
      ring
    have hregγ : regProd χ (-1) (fun v => NF.siegelDensity v Q₀ T₀) =
        (LOne χ)⁻¹ * ((∏ᶠ v, W v) * (∏ᶠ v, g v) / Pg⁻¹) := by
      show LOne χ ^ (-1 : ℤ) * ∏' v, NF.siegelDensity v Q₀ T₀ * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ) = _
      rw [hγreg.tprod_eq, _root_.zpow_neg_one]
    have hregα : regProd χ (-1) (fun v => NF.siegelDensity v Q₀ Q₀) = (LOne χ)⁻¹ * ∏ᶠ v, g v := by
      show LOne χ ^ (-1 : ℤ) * ∏' v, NF.siegelDensity v Q₀ Q₀ * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ) = _
      rw [show (fun v => NF.siegelDensity v Q₀ Q₀ * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ)) = g from
        funext fun v => (hg v).symm, hgp.tprod_eq, _root_.zpow_neg_one]
    -- the regularized binary mass formula
    have hτ := (binaryTamagawaTwoReg_nf (F := F)).tau_eq_two Q₀ hpd
    have h2 := tauSOReg_eq Q₀ hQ hpd
    rw [hτ] at h2
    have hmK : tamagawaKReg Q₀ * mass (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F 2) = 1 := by
      change tamagawaKReg Q₀ * mass (formF Q₀) (stdLat F 2) = 1
      linarith
    have hε : epsNR 2 2 = 1 / 2 := by unfold epsNR; rw [if_pos rfl]
    have hε' : epsCodimOne 2 2 = 1 := by unfold epsCodimOne; rw [if_neg (by omega)]
    have hexp : (-(((2 : ℕ) : ℝ) * (2 * ((2 : ℕ) : ℝ) - ((2 : ℕ) : ℝ) - 1)) / 4) = -((2 : ℝ) * (2 - 1) / 4) := by
      norm_num
    have hV : (∏ σ : F →ₐ[ℚ] ℂ, archVolSO 2 (detGram Q₀ σ)) =
        (∏ σ : F →ₐ[ℚ] ℂ, (1 / 2 * archDensityForm 2 2 (detGram Q₀ σ) (detGram T₀ σ))) * Pg := harch
    unfold tamagawaKReg at hmK
    rw [hregα, hV] at hmK
    rw [hrep]
    unfold siegelProductTRegWith
    rw [hε, hε', hexp, hregγ]
    generalize (∏ σ : F →ₐ[ℚ] ℂ, (1 / 2 * archDensityForm 2 2 (detGram Q₀ σ) (detGram T₀ σ))) = R at hmK ⊢
    generalize (∏ᶠ v, W v) = Wt
    rw [div_inv_eq_mul]
    linear_combination (-Wt) * hmK
  · rw [repMassT_eq_zero_of_not_rep _ _ _ h]
    obtain ⟨v, hv⟩ := exists_local_not_rep Q₀ T₀ hpd hpdT h
    have h0 := localDensityForm_eq_zero_of_not_rep v Q₀ T₀ (nondegenerate_of_map hpdT.nondegenerate) (by norm_num) hv
    have hz : (∏' v : HeightOneSpectrum (𝓞 F), NF.siegelDensity v Q₀ T₀ *
        (1 - chiP v Q₀ / (normP v : ℝ)) ^ (-1 : ℤ)) = 0 :=
      tprod_of_exists_eq_zero ⟨v, by unfold NF.siegelDensity; rw [h0]; simp⟩
    unfold siegelProductTRegWith regProd
    rw [hz]
    ring

/-! ### Binary form, one represented number: $N = 2$, $r = 1$ -/

/-- **Siegel's formula for a unary form by a binary form** ($N = 2$, $r = 1$; Siegel 1935, Hauptsatz, $\varepsilon = \tfrac12$ for
$r = N - 1$ [unverified]): for $Q_0$ a totally positive definite binary form and $T_0 = \langle m\rangle$ totally positive definite over
$\mathcal O_F$,
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(T_0)}{|O(M)|} = \mathrm{Mass}(L)\cdot\tfrac12\,|d_F|^{-1/2}\prod_\sigma\beta_\sigma(Q_0,m)\cdot
  L_F(1,\chi_{Q_0})^{-1}\prod_\mathfrak p\beta_\mathfrak p(Q_0,m)\bigl(1-\chi_{Q_0}(\mathfrak p)/N\mathfrak p\bigr)^{-1},$$
i.e. `repMassT = mass * siegelProductTRegWith (chiP · Q₀) (-1) Q₀ T₀` ($\varepsilon' = \tfrac12$ is the global factor `epsCodimOne`). This is
the binary theorem `siegelFormulaAt2_nf` for the number $m$ (`repMassT_unary`, `archDensityForm_one`, `NF.localDensityForm_unary`). -/
@[kb "siegel1935" "Hauptsatz (forms by forms), N = 2, r = 1 (binary theorem) [unverified]"]
theorem siegelFormsBinaryOne_totallyReal (Q₀ : QuadForm (𝓞 F) 2) (T₀ : QuadForm (𝓞 F) 1)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F))) :
    repMassT (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F 2) (T₀.map (algebraMap (𝓞 F) F)) =
      mass (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F 2) *
        siegelProductTRegWith (fun v => chiP v Q₀) (-1) Q₀ T₀ := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m : 𝓞 F, T₀ = DVR.unary m := ⟨_, SiegelRankOne.eq_unary T₀⟩
  have hdet : (DVR.unary m).hessian.det = 2 * m := by
    simp [QuadForm.hessian, DVR.unary, QuadForm.diag, Matrix.det_unique, Matrix.diagonal_apply]
    ring
  have hm_map : (DVR.unary m).map (algebraMap (𝓞 F) F) = DVR.unary (algebraMap (𝓞 F) F m) := by
    ext i j
    simp [QuadForm.map, DVR.unary, QuadForm.diag, Matrix.diagonal_apply]
  have hg : ∀ σ : F →ₐ[ℚ] ℂ, detGram (DVR.unary m) σ = ‖σ (algebraMap (𝓞 F) F m)‖ := by
    intro σ
    unfold detGram
    rw [hdet]
    congr 1
    simp only [map_mul, map_ofNat, pow_one]
    rw [mul_div_cancel_left₀ _ (two_ne_zero)]
  -- `m` is totally positive
  have hmpos : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m) := by
    intro w
    have h2 := realEmb_det_hessian_pos (Q₀ := DVR.unary m) hpdT w
    rw [hdet, map_mul, map_mul, map_ofNat, map_ofNat] at h2
    linarith
  have h1 : ∀ v : HeightOneSpectrum (𝓞 F),
      NF.siegelDensity v Q₀ (DVR.unary m) = NF.localDensity v Q₀ m := by
    intro v
    unfold NF.siegelDensity
    rw [if_neg (by omega), one_mul, NF.localDensityForm_unary]
  have hε' : epsCodimOne 2 1 = 1 / 2 := by unfold epsCodimOne; rw [if_pos rfl]
  have hε : epsNR 2 1 = 1 := by unfold epsNR; rw [if_neg (by omega)]
  have hexp : (-(((1 : ℕ) : ℝ) * (2 * ((2 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) - 1)) / 4) = -((2 : ℝ) - 1) / 2 := by
    norm_num
  have key := (siegelFormulaAt2_nf Q₀ hpd hmpos).repMass_eq
  rw [hm_map, repMassT_unary]
  refine key.trans ?_
  unfold siegelProduct2Reg siegelProductWith siegelProductTRegWith
  simp only [h1, hg, hε, hε', hexp, archDensityForm_one, one_mul]
  ring

end QuadFormsKB.Tamagawa.Frames
