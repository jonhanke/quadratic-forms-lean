/-
# Siegel's formula for representations of forms by forms, $N - r = 2$: the regularized product

**Layer:** $F$ a totally real number field; $Q_0$ of rank $N = r + 2$ and $T_0$ of rank $r \ge 1$ over $\mathcal O_F$, both totally positive
definite; $L = \mathcal O_F^{N}$. For complement rank $n' = 2$ the plain product $\prod_\mathfrak p\beta_\mathfrak p(Q,T)$ converges only
conditionally (at good $\mathfrak p$, $\beta_\mathfrak p(Q,T) = \alpha_\mathfrak p(Q)/\alpha_\mathfrak p(Q')$ and $\alpha_\mathfrak p(Q') = 1 - \chi'(\mathfrak p)/N\mathfrak p$
for the binary complement $Q'$), so Mathlib's `tprod` is junk. As in rank 3 (`SiegelRank3.lean`) the product is regularized.

**Defines**
* `deltaForms Q₀ T₀` $= -\det H_{Q_0}\det H_{T_0}$ and `chiForms Q₀ T₀` $= \chi$, the quadratic character $(\delta/\mathfrak p)$ of
  $\delta = -\det H_Q\det H_T$ (it is the character of the binary complement off a finite set, since $\det H_T\det H' = (\det g)^2\det H_Q$);
* `siegelProductTReg Q₀ T₀` $= |d_F|^{-r(2N-r-1)/4}\prod_\sigma\beta_\sigma(Q,T)\cdot L_F(1,\chi)\prod_\mathfrak p\beta_\mathfrak p(Q,T)\,(1-\chi(\mathfrak p)/N\mathfrak p)$
  (`siegelProductT` with the `tprod` replaced by `regProd χ 1`);
* `SiegelFormsAtReg Q₀ T₀`: $\sum_{\mathrm{cls}M\subseteq\mathrm{gen}L}r_M(T)/|O(M)| = \mathrm{Mass}(L)\cdot S^{\mathrm{reg}}(Q,T)$.

**Proves**
* character facts: $\delta$ is totally negative, hence not a square (`not_isSquare_deltaForms`); $L_F(1,\chi)$ exists and is positive
  (`lOne_chiForms_pos`); $\chi' = \chi$ off a finite set for the complement $Q'$ of an adapted frame (`chiP_frame_eq_chiForms`);
* the archimedean fibration for an adapted frame (`arch_forms_frame`: $\det H_T\det H' = (\det g)^2\det H_Q$ and the homogeneity of
  `archVolSO`, `archDensityForm`);
* **`siegelFormsAtReg_of_frame`**: `SiegelFormsAtReg Q₀ T₀` from an adapted frame, the local identity at every prime (a hypothesis here),
  $\tau^{\mathrm{reg}}(SO(Q')) = 2$ and the mass formula for $Q_0$; **`siegelFormsAtReg_of_frame_totallyReal`** discharges the last two
  over every totally real field;
* `multipliable_siegelDensity_forms_reg` (absolute convergence of $\beta_\mathfrak p(1-\chi/N\mathfrak p)$) and
  **`hasProd_normOrder_siegelDensity_forms`** (the natural-order reading, given `NaturalOrderEulerOne χ`).

Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.FrameSiegelMain
import QuadFormsKB.Tamagawa.FrameAdapted
import QuadFormsKB.Tamagawa.FrameGlobalGen
import QuadFormsKB.Tamagawa.SiegelRank3Frame
import QuadFormsKB.Tamagawa.BinaryTauNF

open NumberField Matrix
open scoped Real

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Frames

open QuadFormsKB.Tamagawa Lattices LocalDensity IsDedekindDomain QuadFormsKB.RegProd NFEuler
  QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] {N r : ℕ}

/-! ### Definitions -/

/-- **$\delta = -\det H_{Q_0}\cdot\det H_{T_0}$**, the element whose residue symbol is `chiForms` at the good primes. -/
def deltaForms (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r) : 𝓞 F :=
  -(Q₀.hessian.det * T₀.hessian.det)

open scoped Classical in
/-- **The character of Siegel's formula for forms by forms with complement rank $2$:** $\chi(\mathfrak p) = (\delta/\mathfrak p)$ with
$\delta = -\det H_{Q_0}\det H_{T_0}$ at $\mathfrak p \nmid 2\delta$, and $0$ otherwise. Off a finite set it is the
character `chiP` of the
binary complement of any adapted frame (`chiP_frame_eq_chiForms`), since $\det H_T\det H' = (\det g)^2\det H_Q$. -/
def chiForms (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  if (2 : 𝓞 F) ∉ v.asIdeal ∧ deltaForms Q₀ T₀ ∉ v.asIdeal then (Siegel.charNF v (deltaForms Q₀ T₀) : ℝ) else 0

/-- **Siegel's product for $T$ by $Q$, regularized** (complement rank $2$; Siegel 1935, Hauptsatz; Hanke's natural-order reading
[unverified]): `siegelProductT` with the `tprod` $\prod_\mathfrak p\beta_\mathfrak p$ replaced by
$L_F(1,\chi)\prod_\mathfrak p\beta_\mathfrak p(Q,T)\,(1-\chi(\mathfrak p)/N\mathfrak p)$ (`regProd χ 1`, $\chi$ = `chiForms`):
$$S^{\mathrm{reg}}(Q,T) = \varepsilon'\,|d_F|^{-r(2N-r-1)/4}\prod_\sigma\varepsilon\,\beta_\sigma(Q,T)\cdot
  L_F(1,\chi)\prod_\mathfrak p\alpha_\mathfrak p(Q,T)\,\bigl(1-\chi(\mathfrak p)/N\mathfrak p\bigr).$$ -/
@[kb "siegel1935" "Hauptsatz (local side, forms by forms, complement of rank 2, regularized) [unverified]"]
def siegelProductTReg (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r) : ℝ :=
  epsCodimOne N r * |(discr F : ℝ)| ^ (-((r : ℝ) * (2 * N - r - 1)) / 4) *
    (∏ σ : F →ₐ[ℚ] ℂ, epsNR N r * archDensityForm N r (detGram Q₀ σ) (detGram T₀ σ)) *
    regProd (chiForms Q₀ T₀) 1 (fun v => NF.siegelDensity v Q₀ T₀)

/-- **Siegel's formula for representations of $T$ by the genus of $Q$, regularized product** ($N - r = 2$): with $L = \mathcal O_F^N$,
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(T)}{|O(M)|} = \mathrm{Mass}(L)\cdot S^{\mathrm{reg}}(Q, T).$$

Field:
- `repMass_eq`: the displayed identity.

A statement, not an input: it is proved from an adapted frame in `siegelFormsAtReg_of_frame`. -/
@[kb "siegel1935" "Hauptsatz (complement of rank 2, regularized product) [unverified]"]
structure SiegelFormsAtReg (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r) : Prop where
  repMass_eq : repMassT (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F N) (T₀.map (algebraMap (𝓞 F) F)) =
    mass (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F N) * siegelProductTReg Q₀ T₀

/-! ### The character `chiForms` -/

theorem abs_chiForms_le (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r) (v : HeightOneSpectrum (𝓞 F)) :
    |chiForms Q₀ T₀ v| ≤ 1 := by
  unfold chiForms
  split_ifs
  · exact abs_charNF_le v _
  · simp

theorem deltaForms_ne_zero {Q₀ : QuadForm (𝓞 F) N} {T₀ : QuadForm (𝓞 F) r} (hQ : Q₀.Nondegenerate)
    (hT : T₀.Nondegenerate) : deltaForms Q₀ T₀ ≠ 0 :=
  neg_ne_zero.2 (mul_ne_zero hQ hT)

/-- **$\delta$ is not a square in $F$** for $Q_0$, $T_0$ totally positive definite ($\delta$ is totally negative). -/
theorem not_isSquare_deltaForms [IsTotallyReal F] {Q₀ : QuadForm (𝓞 F) N} {T₀ : QuadForm (𝓞 F) r}
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F))) :
    ¬ IsSquare (algebraMap (𝓞 F) F (deltaForms Q₀ T₀)) := by
  rintro ⟨s, hs⟩
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := congrArg (realEmb F w) hs
  have h1 := realEmb_det_hessian_pos (Q₀ := Q₀) hpd w
  have h2 := realEmb_det_hessian_pos (Q₀ := T₀) hpdT w
  simp only [deltaForms, map_neg, map_mul] at h
  nlinarith [mul_self_nonneg (realEmb F w s), mul_pos h1 h2]

/-- **$F(\sqrt\delta)$:** for $\delta \in \mathcal O_F$ not a square in $F$, a quadratic extension $E$ with $s^2 = \delta$ and
$\sigma s = -s$ for its nontrivial automorphism $\sigma$. -/
theorem exists_sqrtExt_of_not_isSquare [IsTotallyReal F] {δ : 𝓞 F} (hd : ¬ IsSquare (algebraMap (𝓞 F) F δ)) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra F E) (_ : Algebra.IsQuadraticExtension F E) (s : E),
      s ^ 2 = algebraMap F E (algebraMap (𝓞 F) F δ) ∧ Binary.Rel.conj F E s = -s := by
  obtain ⟨E, _, _, _, s, hs, hspan⟩ := Lam.exists_quadExt _ hd
  obtain ⟨hQ, -⟩ := HN.quadData _ hd s hs hspan
  refine ⟨E, inferInstance, inferInstance, inferInstance, hQ, s, hs, ?_⟩
  have hsq : (Binary.Rel.conj F E s - s) * (Binary.Rel.conj F E s + s) = 0 := by
    have : (Binary.Rel.conj F E s) ^ 2 = s ^ 2 := by
      rw [← map_pow, hs, AlgEquiv.commutes]
    linear_combination this
  rcases mul_eq_zero.mp hsq with h | h
  · exfalso
    apply Binary.Rel.conj_ne_one F E
    ext y
    obtain ⟨b₀, b₁, rfl⟩ := hspan y
    rw [sub_eq_zero] at h
    simp [h]
  · linear_combination h

theorem isAlmostRelChar_chiForms {Q₀ : QuadForm (𝓞 F) N} {T₀ : QuadForm (𝓞 F) r} (hQ : Q₀.Nondegenerate)
    (hT : T₀.Nondegenerate) {E : Type} [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
    {s : E} (hs : s ^ 2 = algebraMap F E (algebraMap (𝓞 F) F (deltaForms Q₀ T₀)))
    (hsc : Binary.Rel.conj F E s = -s) : IsAlmostRelChar (chiForms Q₀ T₀) E :=
  isAlmostRelChar_of_sqrt (deltaForms_ne_zero hQ hT) hs hsc ∅ fun v _ h2 hδ => by
    unfold chiForms
    rw [if_pos ⟨h2, hδ⟩]

/-- **$L_F(1,\chi)$ exists and is positive** for `chiForms Q₀ T₀`, $Q_0$ and $T_0$ totally positive definite ($\chi$ is the character of
$F(\sqrt\delta)/F$ off a finite set; no hypothesis). -/
@[kb "neukirch1999" "Ch. VII §5, Cor. 5.11 (L(1, χ_{E/F}) = ρ_E/ρ_F ≠ 0) [unverified]"]
theorem lOne_chiForms_pos [IsTotallyReal F] {Q₀ : QuadForm (𝓞 F) N} {T₀ : QuadForm (𝓞 F) r}
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F))) :
    0 < LOne (chiForms Q₀ T₀) ∧ HasLOne (chiForms Q₀ T₀) (LOne (chiForms Q₀ T₀)) := by
  obtain ⟨E, _, _, _, _, s, hs, hsc⟩ := exists_sqrtExt_of_not_isSquare (not_isSquare_deltaForms hpd hpdT)
  have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  have hT : T₀.Nondegenerate := nondegenerate_of_map hpdT.nondegenerate
  exact exists_hasLOne_of_almost_relChar (Algebra.IsQuadraticExtension.finrank_eq_two F E)
    (fun v => abs_chiForms_le Q₀ T₀ v) (isAlmostRelChar_chiForms hQ hT hs hsc)

/-! ### Frames: the determinant relation and the complement's character -/

private theorem det_hess_map {n : ℕ} (Q : QuadForm (𝓞 F) n) :
    (Q.map (algebraMap (𝓞 F) F)).hessian.det = algebraMap (𝓞 F) F Q.hessian.det := by
  have h : (Q.map (algebraMap (𝓞 F) F)).hessian = Q.hessian.map (algebraMap (𝓞 F) F) := by
    ext i j; simp [QuadForm.hessian, QuadForm.map]
  rw [h, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

/-- **The determinant relation of an adapted frame:** $\det H_{Q_0}\,(\det g)^2 = \det H_{T_0}\det H'$. -/
theorem det_frame_forms (Q₀ : QuadForm (𝓞 F) (r + 2)) (T₀ : QuadForm (𝓞 F) r)
    (fr : AdaptedFrameT (Q₀.map (algebraMap (𝓞 F) F)) (T₀.map (algebraMap (𝓞 F) F))) :
    algebraMap (𝓞 F) F Q₀.hessian.det * fr.g.val.det ^ 2 =
      algebraMap (𝓞 F) F T₀.hessian.det * algebraMap (𝓞 F) F fr.Q'.hessian.det := by
  have h1 := congrArg (fun S : QuadForm F (r + 2) => S.hessian.det) fr.compMat_eq
  simp only [QuadForm.hessian_compMat, det_mul, det_transpose, det_hessian_blockForm, det_hess_map] at h1
  linear_combination h1

theorem isTotallyPosDef_blockForm_frame {n' : ℕ} {Q : QuadForm F (r + n')} {T : QuadForm F r}
    (fr : AdaptedFrameT Q T) (hpd : IsTotallyPosDef Q) :
    IsTotallyPosDef (blockForm T (fr.Q'.map (algebraMap (𝓞 F) F))) := by
  have := isTotallyPosDef_compMat Q fr.g hpd
  rwa [fr.compMat_eq] at this

/-- **$\chi' = \chi$ off a finite set:** the character `chiP` of the complement $Q'$ of an adapted frame agrees with
`chiForms Q₀ T₀`
at almost all primes ($-\det H' = \theta^2$ with $\theta = s\det g/\det H_T$, $s^2 = \delta$). -/
theorem chiP_frame_eq_chiForms [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) (r + 2)) (T₀ : QuadForm (𝓞 F) r)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F)))
    (fr : AdaptedFrameT (Q₀.map (algebraMap (𝓞 F) F)) (T₀.map (algebraMap (𝓞 F) F))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, chiP v fr.Q' = chiForms Q₀ T₀ v := by
  classical
  obtain ⟨E, _, _, _, _, s, hs, hsc⟩ := exists_sqrtExt_of_not_isSquare (not_isSquare_deltaForms hpd hpdT)
  have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  have hT : T₀.Nondegenerate := nondegenerate_of_map hpdT.nondegenerate
  have hpdQ' := isTotallyPosDef_of_blockForm_right (isTotallyPosDef_blockForm_frame fr hpd)
  have hQ' : fr.Q'.Nondegenerate := nondegenerate_of_map hpdQ'.nondegenerate
  have hb : algebraMap (𝓞 F) F T₀.hessian.det ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hT
  have hS₁ : IsAlmostRelChar (fun v => chiP v fr.Q') E := by
    obtain ⟨u, hu⟩ : ∃ u : F, u = (algebraMap (𝓞 F) F T₀.hessian.det)⁻¹ := ⟨_, rfl⟩
    have hbu : algebraMap (𝓞 F) F T₀.hessian.det * u = 1 := by rw [hu]; exact mul_inv_cancel₀ hb
    refine isAlmostRelChar_of_sqrt (neg_ne_zero.2 hQ') (θ := s * algebraMap F E (fr.g.val.det * u)) ?_ ?_ ∅
      fun v _ h2 hδ => ?_
    · have hrel := det_frame_forms Q₀ T₀ fr
      rw [mul_pow, hs, ← map_pow, ← map_mul]
      congr 1
      simp only [deltaForms, map_mul, map_pow, map_neg]
      linear_combination (-(algebraMap (𝓞 F) F T₀.hessian.det) * u ^ 2) * hrel
        + (-(algebraMap (𝓞 F) F fr.Q'.hessian.det) * (1 + algebraMap (𝓞 F) F T₀.hessian.det * u)) * hbu
    · rw [map_mul, hsc, AlgEquiv.commutes]; ring
    · exact chiP_binary_eq_charNF v fr.Q' h2 fun h => hδ (v.asIdeal.neg_mem_iff.2 h)
  obtain ⟨S₁, hS₁⟩ := hS₁
  obtain ⟨S₂, hS₂⟩ := isAlmostRelChar_chiForms hQ hT hs hsc
  refine ⟨S₁ ∪ S₂, fun v hv => ?_⟩
  rw [Finset.mem_union, not_or] at hv
  exact (hS₁ v hv.1).trans (hS₂ v hv.2).symm

/-! ### The archimedean fibration for an adapted frame -/

theorem rpow_sq_mul_scale {c D : ℝ} (hc : 0 < c) (hD : 0 < D) (e : ℝ) (k : ℕ) (hk : 2 * e = -(k : ℝ)) :
    (c ^ 2 * D) ^ e = (c ^ k)⁻¹ * D ^ e := by
  have h : (c ^ 2) ^ e = (c ^ k)⁻¹ := by
    rw [← Real.rpow_two, ← Real.rpow_mul hc.le, hk, Real.rpow_neg hc.le, Real.rpow_natCast]
  rw [Real.mul_rpow (by positivity) hD.le, h]

/-- $\mathrm{vol}(SO_n, c^2D) = c^{-(n+1)}\,\mathrm{vol}(SO_n, D)$. -/
theorem archVolSO_scale (n : ℕ) {c D : ℝ} (hc : 0 < c) (hD : 0 < D) :
    archVolSO n (c ^ 2 * D) = (c ^ (n + 1))⁻¹ * archVolSO n D := by
  unfold archVolSO
  rw [rpow_sq_mul_scale hc hD (-((n : ℝ) + 1) / 2) (n + 1) (by push_cast; ring)]
  ring

/-- $\beta_\infty(c^2D_Q, D_T) = c^{-r}\beta_\infty(D_Q, D_T)$. -/
theorem archDensityForm_scale (N r : ℕ) {c D : ℝ} (hc : 0 < c) (hD : 0 < D) (DT : ℝ) :
    archDensityForm N r (c ^ 2 * D) DT = (c ^ r)⁻¹ * archDensityForm N r D DT := by
  unfold archDensityForm
  rw [rpow_sq_mul_scale hc hD (-(r : ℝ) / 2) r (by ring)]
  ring

/-- **The archimedean fibration for an adapted frame** at one embedding $\sigma$: with $c = |\sigma\det g|$ and $x = \det H_{T_0}$,
$$\mathrm{vol}(SO_N, D_Q)\,|\sigma x|^{2} = \mathrm{vol}(SO_2, D')\,\beta_\sigma(Q,T)\,c^{2+1}.$$ -/
theorem arch_forms_frame [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) (r + 2)) (T₀ : QuadForm (𝓞 F) r) (hQ : Q₀.Nondegenerate)
    (hT : T₀.Nondegenerate)
    (fr : AdaptedFrameT (Q₀.map (algebraMap (𝓞 F) F)) (T₀.map (algebraMap (𝓞 F) F)))
    (hQ' : fr.Q'.Nondegenerate) (σ : F →ₐ[ℚ] ℂ) :
    archVolSO (r + 2) (detGram Q₀ σ) * ‖σ (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ 2 =
      archVolSO 2 (detGram fr.Q' σ) * archDensityForm (r + 2) r (detGram Q₀ σ) (detGram T₀ σ) *
        ‖σ fr.g.val.det‖ ^ (2 + 1) := by
  have hdet : fr.g.val.det ≠ 0 := (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero
  have hDQ := detGram_pos_frames Q₀ hQ σ
  have hDT := detGram_pos_frames T₀ hT σ
  have hD' := detGram_pos_frames fr.Q' hQ' σ
  have hc : 0 < ‖σ fr.g.val.det‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr hdet)
  have hnx : ‖σ (algebraMap (𝓞 F) F T₀.hessian.det)‖ = 2 ^ r * detGram T₀ σ := by
    unfold detGram
    rw [map_div₀, norm_div, map_pow, map_ofNat, norm_pow, Complex.norm_ofNat]
    field_simp
  have hrel : detGram T₀ σ * detGram fr.Q' σ = ‖σ fr.g.val.det‖ ^ 2 * detGram Q₀ σ := by
    have hrel := det_frame_forms Q₀ T₀ fr
    have e : algebraMap (𝓞 F) F T₀.hessian.det / 2 ^ r * (algebraMap (𝓞 F) F fr.Q'.hessian.det / 2 ^ 2) =
        fr.g.val.det ^ 2 * (algebraMap (𝓞 F) F Q₀.hessian.det / 2 ^ (r + 2)) := by
      rw [pow_add, div_mul_div_comm, mul_div_assoc', mul_comm (fr.g.val.det ^ 2), hrel]
    unfold detGram
    rw [← norm_mul, ← map_mul, e, map_mul, norm_mul, map_pow, norm_pow]
  have A := archVolSO_blockForm r 2 hDT hD'
  rw [hrel, archVolSO_scale (r + 2) hc hDQ, archDensityForm_scale (r + 2) r hc hDQ] at A
  have hck : ‖σ fr.g.val.det‖ ^ (r + 2 + 1) = ‖σ fr.g.val.det‖ ^ r * ‖σ fr.g.val.det‖ ^ (2 + 1) := by ring
  rw [hck] at A
  rw [hnx]
  have h1 : ‖σ fr.g.val.det‖ ^ r ≠ 0 := by positivity
  have h3 : ‖σ fr.g.val.det‖ ^ (2 + 1) ≠ 0 := by positivity
  calc archVolSO (r + 2) (detGram Q₀ σ) * (2 ^ r * detGram T₀ σ) ^ 2
      = (‖σ fr.g.val.det‖ ^ r * ‖σ fr.g.val.det‖ ^ (2 + 1)) *
          (((‖σ fr.g.val.det‖ ^ r * ‖σ fr.g.val.det‖ ^ (2 + 1)))⁻¹ * archVolSO (r + 2) (detGram Q₀ σ) *
            (2 ^ r * detGram T₀ σ) ^ 2) := by field_simp
    _ = (‖σ fr.g.val.det‖ ^ r * ‖σ fr.g.val.det‖ ^ (2 + 1)) *
          (archVolSO 2 (detGram fr.Q' σ) * ((‖σ fr.g.val.det‖ ^ r)⁻¹ *
            archDensityForm (r + 2) r (detGram Q₀ σ) (detGram T₀ σ))) := by rw [A]
    _ = _ := by field_simp

/-! ### The core: the regularized local product -/

/-- **The core of the assembly:** under the local identity at every prime, the regularized factors
$\beta_\mathfrak p(Q,T)(1-\chi(\mathfrak p)/N\mathfrak p)$ have the absolutely convergent product $W\cdot E\cdot A/(G_f\cdot G)$, and the corrected
binary product is $L_F(1,\chi)^{-1}G_f$ with $G_f > 0$. -/
private theorem reg_core [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) (r + 2)) (T₀ : QuadForm (𝓞 F) r) (hr : 1 ≤ r)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F)))
    (fr : AdaptedFrameT (Q₀.map (algebraMap (𝓞 F) F)) (T₀.map (algebraMap (𝓞 F) F)))
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      locFrameTypeSumG v (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F))
          (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v)) *
        NF.localDensityForm v Q₀ Q₀ *
          ‖algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ 2 =
      NF.localDensityForm v fr.Q' fr.Q' * NF.localDensityForm v Q₀ T₀ *
        ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (2 + 1)) :
    ∃ Gf : ℝ, 0 < Gf ∧
      HasProd (fun v => NF.siegelDensity v Q₀ T₀ * (1 - chiForms Q₀ T₀ v / (normP v : ℝ)) ^ (1 : ℤ))
        ((∏ᶠ v : HeightOneSpectrum (𝓞 F),
            locFrameTypeSumG v (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F))
              (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v))) *
          ((∏ σ : F →ₐ[ℚ] ℂ, ‖σ (algebraMap (𝓞 F) F T₀.hessian.det)‖)⁻¹) ^ 2 *
          (∏' v : HeightOneSpectrum (𝓞 F), NF.siegelDensity v Q₀ Q₀) /
          (Gf * ((∏ σ : F →ₐ[ℚ] ℂ, ‖σ fr.g.val.det‖)⁻¹) ^ (2 + 1))) ∧
      regProd (fun v => chiP v fr.Q') (-1) (fun v => NF.siegelDensity v fr.Q' fr.Q') =
        (LOne (chiForms Q₀ T₀))⁻¹ * Gf := by
  classical
  have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  have hT : T₀.Nondegenerate := nondegenerate_of_map hpdT.nondegenerate
  have hpdB := isTotallyPosDef_blockForm_frame fr hpd
  have hpdQ' := isTotallyPosDef_of_blockForm_right hpdB
  have hQ' : fr.Q'.Nondegenerate := nondegenerate_of_map hpdQ'.nondegenerate
  have hx : algebraMap (𝓞 F) F T₀.hessian.det ≠ 0 :=
    (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hT
  have hdet : fr.g.val.det ≠ 0 := (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero
  -- the lattice `g⁻¹ 𝓞^N` and its localizations
  obtain ⟨L', hL'⟩ : ∃ L' : Lat F (r + 2), L' = Lat.image fr.g⁻¹ (stdLat F (r + 2)) := ⟨_, rfl⟩
  have hLoc : ∀ v : HeightOneSpectrum (𝓞 F), loc v L'.1 =
      locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v) := by
    intro v
    rw [hL']
    show loc v (glImage fr.g⁻¹ intVec) = _
    rw [loc_glImage, loc_intVec, map_inv]
  obtain ⟨W, hW⟩ : ∃ W : HeightOneSpectrum (𝓞 F) → ℝ, ∀ v, W v =
      locFrameTypeSumG v (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F))
        (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : HeightOneSpectrum (𝓞 F) → ℝ, ∀ v,
      E v = ‖algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ 2 := ⟨_, fun _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : HeightOneSpectrum (𝓞 F) → ℝ, ∀ v,
      G v = ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (2 + 1) := ⟨_, fun _ => rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : HeightOneSpectrum (𝓞 F) → ℝ, ∀ v, α v = NF.siegelDensity v Q₀ Q₀ := ⟨_, fun _ => rfl⟩
  obtain ⟨α', hα'⟩ : ∃ α' : HeightOneSpectrum (𝓞 F) → ℝ, ∀ v, α' v = NF.siegelDensity v fr.Q' fr.Q' :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : HeightOneSpectrum (𝓞 F) → ℝ, ∀ v, γ v = NF.siegelDensity v Q₀ T₀ := ⟨_, fun _ => rfl⟩
  have hαfun : α = fun v => NF.siegelDensity v Q₀ Q₀ := funext hα
  have hα'fun : α' = fun v => NF.siegelDensity v fr.Q' fr.Q' := funext hα'
  have hGpos : ∀ v, 0 < G v := fun v => by
    rw [hG]
    exact pow_pos (norm_pos_iff.mpr ((map_ne_zero _).mpr hdet)) _
  have hαpos : ∀ v, 0 < α v := fun v => by rw [hα]; exact siegelDensity_pos v Q₀ hQ
  have hα'pos : ∀ v, 0 < α' v := fun v => by rw [hα']; exact siegelDensity_pos v fr.Q' hQ'
  have hγeq : ∀ v, γ v = W v * E v * α v / (α' v * G v) := by
    intro v
    have hid := hloc v
    rw [← hW v, ← hE v, ← hG v] at hid
    have h1 : α v = 1 / 2 * NF.localDensityForm v Q₀ Q₀ := by
      rw [hα]; unfold NF.siegelDensity; rw [if_pos rfl]
    have h2 : α' v = 1 / 2 * NF.localDensityForm v fr.Q' fr.Q' := by
      rw [hα']; unfold NF.siegelDensity; rw [if_pos rfl]
    have h3 : γ v = NF.localDensityForm v Q₀ T₀ := by
      rw [hγ]; unfold NF.siegelDensity; rw [if_neg (by omega), one_mul]
    rw [eq_div_iff (mul_pos (hα'pos v) (hGpos v)).ne', h3, h1, h2]
    linear_combination (-1 / 2 : ℝ) * hid
  -- finite supports
  have hWfin : Function.HasFiniteMulSupport W := by
    refine (frameBadSetG T₀ hT L').finite_toSet.subset fun v hv => ?_
    by_contra hvS
    obtain ⟨hv0, hL⟩ := not_mem_frameBadSetG T₀ hT L' (by simpa using hvS)
    apply hv
    show W v = 1
    rw [hW v, ← hLoc v]
    exact locFrameTypeSumG_eq_one_of_good T₀ hT fr.Q' hQ' L' hL hv0
  have hEfin : Function.HasFiniteMulSupport E :=
    (finite_valuation_ne_one hx).subset fun v hv => by
      by_contra h
      simp only [Set.mem_setOf_eq, not_not] at h
      apply hv
      rw [hE, norm_algebraMap_eq_one h, one_pow]
  have hGfin : Function.HasFiniteMulSupport G :=
    (finite_valuation_ne_one hdet).subset fun v hv => by
      by_contra h
      simp only [Set.mem_setOf_eq, not_not] at h
      apply hv
      rw [hG, norm_algebraMap_eq_one h, one_pow]
  have hαm : Multipliable α := by
    rw [hαfun]; exact multipliable_siegelDensity (N := r + 2) (by omega) (by omega) _ hQ
  have hWp : HasProd W (∏ᶠ v, W v) := by
    have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hWfin).hasProd
    rwa [tprod_eq_finprod hWfin] at this
  have hEp : HasProd E (∏ᶠ v, E v) := by
    have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hEfin).hasProd
    rwa [tprod_eq_finprod hEfin] at this
  have hGp : HasProd G (∏ᶠ v, G v) := by
    have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hGfin).hasProd
    rwa [tprod_eq_finprod hGfin] at this
  have hEpv : ∏ᶠ v, E v = ((∏ σ : F →ₐ[ℚ] ℂ, ‖σ (algebraMap (𝓞 F) F T₀.hessian.det)‖)⁻¹) ^ 2 := by
    rw [← finprod_norm_pow_eq _ hx 2]
    exact finprod_congr hE
  have hGpv : ∏ᶠ v, G v = ((∏ σ : F →ₐ[ℚ] ℂ, ‖σ fr.g.val.det‖)⁻¹) ^ (2 + 1) := by
    rw [← finprod_norm_pow_eq _ hdet (2 + 1)]
    exact finprod_congr hG
  have hGprod : 0 < ∏ᶠ v, G v := by
    rw [finprod_eq_prod_of_mulSupport_subset G (s := hGfin.toFinset) fun v hv => (Set.Finite.mem_toFinset _).mpr hv]
    exact Finset.prod_pos fun v _ => hGpos v
  -- the character and the regularized products
  obtain ⟨hL0, hL⟩ := lOne_chiForms_pos hpd hpdT
  obtain ⟨S, hS⟩ := chiP_frame_eq_chiForms Q₀ T₀ hpd hpdT fr
  have hχ : ∀ v, |chiForms Q₀ T₀ v| ≤ 1 := fun v => abs_chiForms_le Q₀ T₀ v
  have hlam : ∀ v, 0 < 1 - chiForms Q₀ T₀ v / (normP v : ℝ) := fun v => one_sub_div_pos (hχ v) v
  obtain ⟨g, hg⟩ : ∃ g : HeightOneSpectrum (𝓞 F) → ℝ, ∀ v,
      g v = α' v * (1 - chiForms Q₀ T₀ v / (normP v : ℝ)) ^ (-1 : ℤ) := ⟨_, fun _ => rfl⟩
  have hgfin : Function.HasFiniteMulSupport g := by
    have := hasFiniteMulSupport_siegelDensity_binary_reg hQ' S hS
    rwa [show g = fun v => NF.siegelDensity v fr.Q' fr.Q' *
      (1 - chiForms Q₀ T₀ v / (normP v : ℝ)) ^ (-1 : ℤ) from funext fun v => by rw [hg, hα']]
  have hgpos : ∀ v, 0 < g v := fun v => by rw [hg]; exact mul_pos (hα'pos v) (zpow_pos (hlam v) _)
  have hgp : HasProd g (∏ᶠ v, g v) := by
    have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hgfin).hasProd
    rwa [tprod_eq_finprod hgfin] at this
  have hgprod : 0 < ∏ᶠ v, g v := by
    rw [finprod_eq_prod_of_mulSupport_subset g (s := hgfin.toFinset) fun v hv => (Set.Finite.mem_toFinset _).mpr hv]
    exact Finset.prod_pos fun v _ => hgpos v
  refine ⟨∏ᶠ v, g v, hgprod, ?_, ?_⟩
  · have hP : HasProd (fun v => W v * E v * α v / (g v * G v))
        ((∏ᶠ v, W v) * (∏ᶠ v, E v) * (∏' v, α v) / ((∏ᶠ v, g v) * ∏ᶠ v, G v)) :=
      ((hWp.mul hEp).mul hαm.hasProd).div₀ (hgp.mul hGp) (mul_pos hgprod hGprod).ne'
    rw [hEpv, hGpv] at hP
    rw [show (∏' v, α v) = ∏' v, NF.siegelDensity v Q₀ Q₀ by rw [hαfun]] at hP
    have hW' : (∏ᶠ v, W v) = ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        locFrameTypeSumG v (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F))
          (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v)) :=
      finprod_congr hW
    rw [hW'] at hP
    refine hP.congr_fun fun v => ?_
    have h1 := hγeq v
    rw [hγ v] at h1
    have h2 := hα'pos v
    have h3 := hαpos v
    have h4 := hGpos v
    have h5 := (hlam v).ne'
    rw [h1, hg v, zpow_one, _root_.zpow_neg_one]
    field_simp
  · rw [regProd_congr_finite (fun v => abs_chiP_le fr.Q' v) hχ S hS hL (-1) (fun v => NF.siegelDensity v fr.Q' fr.Q')
      (by
        have := multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hgfin
        rwa [show g = fun v => NF.siegelDensity v fr.Q' fr.Q' *
          (1 - chiForms Q₀ T₀ v / (normP v : ℝ)) ^ (-1 : ℤ) from funext fun v => by rw [hg, hα']] at this)]
    show LOne (chiForms Q₀ T₀) ^ (-1 : ℤ) * ∏' v, NF.siegelDensity v fr.Q' fr.Q' *
      (1 - chiForms Q₀ T₀ v / (normP v : ℝ)) ^ (-1 : ℤ) = _
    rw [show (fun v => NF.siegelDensity v fr.Q' fr.Q' * (1 - chiForms Q₀ T₀ v / (normP v : ℝ)) ^ (-1 : ℤ)) = g from
      funext fun v => by rw [hg, hα'], hgp.tprod_eq, _root_.zpow_neg_one]

/-! ### The assembly -/

/-- **Siegel's formula for forms by forms with complement of rank $2$ (regularized product), from an adapted frame** (Weil 1982,
§3.4–3.5, §4.5 [unverified]). For $Q_0$ of rank $r + 2$ and $T_0$ of rank $r \ge 1$ totally positive definite over $\mathcal O_F$, an adapted
frame $Q_0\circ g = T_0\perp Q'$, the local identity at every prime (`hloc`:
$W_\mathfrak p\cdot\beta_\mathfrak p(Q,Q)\cdot\|\det H_T\|_\mathfrak p^2 = \beta_\mathfrak p(Q',Q')\,\beta_\mathfrak p(Q,T)\,\|\det g\|_\mathfrak p^{2+1}$, with
$W_\mathfrak p$ the local type sum at $g_\mathfrak p^{-1}\mathfrak o_\mathfrak p^{N}$), $\tau^{\mathrm{reg}}(SO(Q')) = 2$ and the mass formula for $Q_0$:
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(\mathcal O_F^N)}\frac{r_M(T_0)}{|O(M)|} = \mathrm{Mass}(\mathcal O_F^N)\cdot S^{\mathrm{reg}}(Q_0, T_0).$$
*Proof.* Transport along $g$ (`repMassT_compMat`), `repMassT_eq_mass_mul` and `typeSumT_eq_finprod_gen` for the lattice $g^{-1}\mathcal O_F^N$,
$\mathrm{Mass}(Q') = 1/\mu^{\mathrm{reg}}_{\mathrm{Tam}}(Q')$ from $\tau^{\mathrm{reg}} = 2$, the local identity (so $\beta_\mathfrak p(1-\chi/N\mathfrak p) = W E\alpha/(g\,G)$ with
$g = \alpha'(1-\chi/N\mathfrak p)^{-1}$ of finite support), the product formula for $\det H_T$ and $\det g$, and the archimedean fibration. -/
@[kb "siegel1935" "Hauptsatz (forms by forms, complement of rank 2, regularized) [unverified]"]
theorem siegelFormsAtReg_of_frame [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) (r + 2)) (T₀ : QuadForm (𝓞 F) r)
    (hr : 1 ≤ r) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F)))
    (fr : AdaptedFrameT (Q₀.map (algebraMap (𝓞 F) F)) (T₀.map (algebraMap (𝓞 F) F)))
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      locFrameTypeSumG v (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F))
          (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v)) *
        NF.localDensityForm v Q₀ Q₀ *
          ‖algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ 2 =
      NF.localDensityForm v fr.Q' fr.Q' * NF.localDensityForm v Q₀ T₀ *
        ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (2 + 1))
    (hτ' : tauSOReg fr.Q' = 2) (hmass : MassFormulaHolds Q₀) : SiegelFormsAtReg Q₀ T₀ := by
  classical
  obtain ⟨Gf, hGf, hβp, hreg2⟩ := reg_core Q₀ T₀ hr hpd hpdT fr hloc
  have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  have hT : T₀.Nondegenerate := nondegenerate_of_map hpdT.nondegenerate
  have hpdB := isTotallyPosDef_blockForm_frame fr hpd
  have hpdB' : IsTotallyPosDef ((blockForm T₀ fr.Q').map (algebraMap (𝓞 F) F)) := by
    rw [map_blockForm]; exact hpdB
  have hpdQ' := isTotallyPosDef_of_blockForm_right hpdB
  have hQ' : fr.Q'.Nondegenerate := nondegenerate_of_map hpdQ'.nondegenerate
  have hx : algebraMap (𝓞 F) F T₀.hessian.det ≠ 0 :=
    (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hT
  have hdet : fr.g.val.det ≠ 0 := (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero
  -- transport along `g`
  have hLi0 : IsIntegral (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F (r + 2)).1 := isIntegral_stdLat_map Q₀
  have hLi' : IsIntegral (blockForm (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F)))
      (Lat.image fr.g⁻¹ (stdLat F (r + 2))).1 := by
    have := isIntegral_compMat (Q₀.map (algebraMap (𝓞 F) F)) fr.g hLi0
    rwa [fr.compMat_eq] at this
  have htr := repMassT_compMat (Q₀.map (algebraMap (𝓞 F) F)) fr.g hpd hLi0 (T₀.map (algebraMap (𝓞 F) F))
  rw [fr.compMat_eq] at htr
  have hrep := repMassT_eq_mass_mul (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F))
    (Lat.image fr.g⁻¹ (stdLat F (r + 2))) hpdB hLi' hpdT.nondegenerate hpdQ' (isIntegral_stdLat_map fr.Q')
  have hsum := typeSumT_eq_finprod_gen T₀ hT fr.Q' (Lat.image fr.g⁻¹ (stdLat F (r + 2))) hpdB' hLi'
  have hLoc : ∀ v : HeightOneSpectrum (𝓞 F), loc v (Lat.image fr.g⁻¹ (stdLat F (r + 2))).1 =
      locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v) := by
    intro v
    show loc v (glImage fr.g⁻¹ intVec) = _
    rw [loc_glImage, loc_intVec, map_inv]
  have hWf : (∏ᶠ v : HeightOneSpectrum (𝓞 F), locFrameTypeSumG v (T₀.map (algebraMap (𝓞 F) F))
      (fr.Q'.map (algebraMap (𝓞 F) F)) (loc v (Lat.image fr.g⁻¹ (stdLat F (r + 2))).1)) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), locFrameTypeSumG v (T₀.map (algebraMap (𝓞 F) F))
        (fr.Q'.map (algebraMap (𝓞 F) F))
        (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v)) :=
    finprod_congr fun v => by rw [hLoc v]
  -- masses
  have hmassQ' : mass (fr.Q'.map (algebraMap (𝓞 F) F)) (stdLat F 2) = (tamagawaKReg fr.Q')⁻¹ := by
    have h := tauSOReg_eq fr.Q' hQ' hpdQ'
    rw [hτ'] at h
    have h1 : tamagawaKReg fr.Q' * mass (fr.Q'.map (algebraMap (𝓞 F) F)) (stdLat F 2) = 1 := by linarith
    exact eq_inv_of_mul_eq_one_right h1
  have hmass' := hmass
  unfold MassFormulaHolds at hmass'
  refine ⟨?_⟩
  rw [← htr, hrep, hsum, hWf, hmassQ', hmass']
  -- the regularized product
  obtain ⟨hL0, hL⟩ := lOne_chiForms_pos hpd hpdT
  have hreg1 : regProd (chiForms Q₀ T₀) 1 (fun v => NF.siegelDensity v Q₀ T₀) = LOne (chiForms Q₀ T₀) *
      ((∏ᶠ v : HeightOneSpectrum (𝓞 F), locFrameTypeSumG v (T₀.map (algebraMap (𝓞 F) F))
            (fr.Q'.map (algebraMap (𝓞 F) F))
            (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v))) *
          ((∏ σ : F →ₐ[ℚ] ℂ, ‖σ (algebraMap (𝓞 F) F T₀.hessian.det)‖)⁻¹) ^ 2 *
          (∏' v : HeightOneSpectrum (𝓞 F), NF.siegelDensity v Q₀ Q₀) /
          (Gf * ((∏ σ : F →ₐ[ℚ] ℂ, ‖σ fr.g.val.det‖)⁻¹) ^ (2 + 1))) := by
    show LOne (chiForms Q₀ T₀) ^ (1 : ℤ) * ∏' v, NF.siegelDensity v Q₀ T₀ *
      (1 - chiForms Q₀ T₀ v / (normP v : ℝ)) ^ (1 : ℤ) = _
    rw [hβp.tprod_eq, zpow_one]
  -- the archimedean products
  have key : (∏ σ : F →ₐ[ℚ] ℂ, archVolSO (r + 2) (detGram Q₀ σ)) *
      (∏ σ : F →ₐ[ℚ] ℂ, ‖σ (algebraMap (𝓞 F) F T₀.hessian.det)‖) ^ 2 =
      (∏ σ : F →ₐ[ℚ] ℂ, archVolSO 2 (detGram fr.Q' σ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archDensityForm (r + 2) r (detGram Q₀ σ) (detGram T₀ σ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, ‖σ fr.g.val.det‖) ^ (2 + 1) := by
    rw [← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun σ _ => arch_forms_frame Q₀ T₀ hQ hT fr hQ' σ
  have hnxpos : ∀ σ : F →ₐ[ℚ] ℂ, 0 < ‖σ (algebraMap (𝓞 F) F T₀.hessian.det)‖ :=
    fun σ => norm_pos_iff.mpr ((map_ne_zero σ).mpr hx)
  have hngpos : ∀ σ : F →ₐ[ℚ] ℂ, 0 < ‖σ fr.g.val.det‖ := fun σ => norm_pos_iff.mpr ((map_ne_zero σ).mpr hdet)
  have hPx : 0 < ∏ σ : F →ₐ[ℚ] ℂ, ‖σ (algebraMap (𝓞 F) F T₀.hessian.det)‖ := Finset.prod_pos fun σ _ => hnxpos σ
  have hPg : 0 < ∏ σ : F →ₐ[ℚ] ℂ, ‖σ fr.g.val.det‖ := Finset.prod_pos fun σ _ => hngpos σ
  have hV'pos : 0 < ∏ σ : F →ₐ[ℚ] ℂ, archVolSO 2 (detGram fr.Q' σ) :=
    Finset.prod_pos fun σ _ => QuadFormsKB.Tamagawa.ArchSOMeasure.archVolSO_pos _ (detGram_pos_frames _ hQ' σ)
  have hVpos : 0 < ∏ σ : F →ₐ[ℚ] ℂ, archVolSO (r + 2) (detGram Q₀ σ) :=
    Finset.prod_pos fun σ _ => QuadFormsKB.Tamagawa.ArchSOMeasure.archVolSO_pos _ (detGram_pos_frames _ hQ σ)
  have hRne : (∏ σ : F →ₐ[ℚ] ℂ, archDensityForm (r + 2) r (detGram Q₀ σ) (detGram T₀ σ)) ≠ 0 := by
    intro h
    have := mul_pos hVpos (pow_pos hPx 2)
    rw [key, h] at this
    simp at this
  have hV : (∏ σ : F →ₐ[ℚ] ℂ, archVolSO (r + 2) (detGram Q₀ σ)) =
      (∏ σ : F →ₐ[ℚ] ℂ, archVolSO 2 (detGram fr.Q' σ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archDensityForm (r + 2) r (detGram Q₀ σ) (detGram T₀ σ)) *
        ((∏ σ : F →ₐ[ℚ] ℂ, ‖σ (algebraMap (𝓞 F) F T₀.hessian.det)‖)⁻¹) ^ 2 /
        ((∏ σ : F →ₐ[ℚ] ℂ, ‖σ fr.g.val.det‖)⁻¹) ^ (2 + 1) := by
    have hne : (∏ σ : F →ₐ[ℚ] ℂ, ‖σ (algebraMap (𝓞 F) F T₀.hessian.det)‖) ^ 2 ≠ 0 := by positivity
    have : (∏ σ : F →ₐ[ℚ] ℂ, archVolSO (r + 2) (detGram Q₀ σ)) =
        (∏ σ : F →ₐ[ℚ] ℂ, archVolSO 2 (detGram fr.Q' σ)) *
          (∏ σ : F →ₐ[ℚ] ℂ, archDensityForm (r + 2) r (detGram Q₀ σ) (detGram T₀ σ)) *
          (∏ σ : F →ₐ[ℚ] ℂ, ‖σ fr.g.val.det‖) ^ (2 + 1) /
          (∏ σ : F →ₐ[ℚ] ℂ, ‖σ (algebraMap (𝓞 F) F T₀.hessian.det)‖) ^ 2 := by
      rw [eq_div_iff hne]; exact key
    have hPx1 := hPx.ne'
    have hPg1 := hPg.ne'
    rw [this]
    simp only [inv_pow]
    field_simp
  -- assemble
  have hA : 0 < ∏' v : HeightOneSpectrum (𝓞 F), NF.siegelDensity v Q₀ Q₀ :=
    tprod_siegelDensity_pos (N := r + 2) (by omega) Q₀ hQ
  have hreg2' := hreg2
  unfold siegelProductTReg tamagawaK tamagawaKReg
  rw [hreg1, hreg2', show epsCodimOne (r + 2) r = 1 from if_neg (by omega),
    show epsNR (r + 2) r = 1 from if_neg (by omega)]
  simp only [one_mul]
  set δ := |(NumberField.discr F : ℝ)| with hδdef
  have hδ : 0 < δ := abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F)
  have hδe : δ ^ (-(((r + 2 : ℕ) : ℝ) * (((r + 2 : ℕ) : ℝ) - 1) / 4)) =
      δ ^ (-((2 : ℝ) * (2 - 1) / 4)) * δ ^ (-((r : ℝ) * (2 * ((r + 2 : ℕ) : ℝ) - r - 1)) / 4) := by
    rw [← Real.rpow_add hδ]; congr 1; push_cast; ring
  rw [hδe, hV]
  have h1 := Real.rpow_pos_of_pos hδ (-((2 : ℝ) * (2 - 1) / 4))
  have h2 := Real.rpow_pos_of_pos hδ (-((r : ℝ) * (2 * ((r + 2 : ℕ) : ℝ) - r - 1)) / 4)
  have hPx2 : 0 < ((∏ σ : F →ₐ[ℚ] ℂ, ‖σ (algebraMap (𝓞 F) F T₀.hessian.det)‖)⁻¹) ^ 2 := by positivity
  have hPg3 : 0 < ((∏ σ : F →ₐ[ℚ] ℂ, ‖σ fr.g.val.det‖)⁻¹) ^ (2 + 1) := by positivity
  have h1' := h1.ne'
  have h2' := h2.ne'
  have hPx1 := hPx.ne'
  have hPg1 := hPg.ne'
  have hA1 := hA.ne'
  have hL1 := hL0.ne'
  have hGf1 := hGf.ne'
  have hV1 := hV'pos.ne'
  have hR1 := hRne
  have hx1 := hPx2.ne'
  have hg1 := hPg3.ne'
  field_simp

/-- **Siegel's formula for forms by forms with complement of rank $2$ over every totally real field**, from an adapted frame and the
local identity: $\tau^{\mathrm{reg}}(SO(Q')) = 2$ is `binaryTamagawaTwoReg_nf` and the mass formula in rank $r + 2 \ge 3$ is
`massFormula_all_ranks_totallyReal` ($r \ge 2$) resp. `massFormula` with `tamagawaNumberTwo_ternary_nf` ($r = 1$). -/
@[kb "siegel1935" "Hauptsatz (forms by forms, complement of rank 2, regularized) [unverified]"]
theorem siegelFormsAtReg_of_frame_totallyReal [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) (r + 2)) (T₀ : QuadForm (𝓞 F) r)
    (hr : 1 ≤ r) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F)))
    (fr : AdaptedFrameT (Q₀.map (algebraMap (𝓞 F) F)) (T₀.map (algebraMap (𝓞 F) F)))
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      locFrameTypeSumG v (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F))
          (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v)) *
        NF.localDensityForm v Q₀ Q₀ *
          ‖algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ 2 =
      NF.localDensityForm v fr.Q' fr.Q' * NF.localDensityForm v Q₀ T₀ *
        ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (2 + 1)) :
    SiegelFormsAtReg Q₀ T₀ := by
  have hpdQ' := isTotallyPosDef_of_blockForm_right (isTotallyPosDef_blockForm_frame fr hpd)
  refine siegelFormsAtReg_of_frame Q₀ T₀ hr hpd hpdT fr hloc
    ((binaryTamagawaTwoReg_nf (F := F)).tau_eq_two fr.Q' hpdQ') ?_
  rcases Nat.lt_or_ge r 2 with h | h
  · obtain rfl : r = 1 := by omega
    have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
    exact massFormula Q₀ hQ (by norm_num) hpd (isIntegral_stdLat_map Q₀) (tamagawaNumberTwo_ternary_nf Q₀ hpd)
  · exact Measure.Weil.massFormula_all_ranks_totallyReal (by omega) Q₀ hpd

/-! ### The natural-order reading -/

/-- **Absolute convergence of the regularized factors:** under the hypotheses of the assembly (an adapted frame and the local
identity), $\prod_\mathfrak p\beta_\mathfrak p(Q,T)\,(1-\chi(\mathfrak p)/N\mathfrak p)$ converges unconditionally. -/
theorem multipliable_siegelDensity_forms_reg [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) (r + 2)) (T₀ : QuadForm (𝓞 F) r)
    (hr : 1 ≤ r) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F)))
    (fr : AdaptedFrameT (Q₀.map (algebraMap (𝓞 F) F)) (T₀.map (algebraMap (𝓞 F) F)))
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      locFrameTypeSumG v (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F))
          (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v)) *
        NF.localDensityForm v Q₀ Q₀ *
          ‖algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ 2 =
      NF.localDensityForm v fr.Q' fr.Q' * NF.localDensityForm v Q₀ T₀ *
        ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (2 + 1)) :
    Multipliable fun v : HeightOneSpectrum (𝓞 F) =>
      NF.siegelDensity v Q₀ T₀ * (1 - chiForms Q₀ T₀ v / (normP v : ℝ)) := by
  obtain ⟨Gf, -, h, -⟩ := reg_core Q₀ T₀ hr hpd hpdT fr hloc
  simp only [zpow_one] at h
  exact h.multipliable

/-- **The natural-order product of $\beta_\mathfrak p(Q,T)$ is the regularized product** (Hanke's reading of $\prod_\mathfrak p$ for complement
rank $2$), given the named input `NaturalOrderEulerOne (chiForms Q₀ T₀)` (the prime ideal theorem for $\chi$) and the data of the assembly. -/
@[kb "hanke2004" "(5.3), p. 368 (natural order = L(1, χ) × absolutely convergent product), forms by forms"]
theorem hasProd_normOrder_siegelDensity_forms [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) (r + 2))
    (T₀ : QuadForm (𝓞 F) r) (hr : 1 ≤ r) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F)))
    (fr : AdaptedFrameT (Q₀.map (algebraMap (𝓞 F) F)) (T₀.map (algebraMap (𝓞 F) F)))
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      locFrameTypeSumG v (T₀.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F))
          (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v)) *
        NF.localDensityForm v Q₀ Q₀ *
          ‖algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ 2 =
      NF.localDensityForm v fr.Q' fr.Q' * NF.localDensityForm v Q₀ T₀ *
        ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (2 + 1))
    (hN : NaturalOrderEulerOne (chiForms Q₀ T₀)) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) => NF.siegelDensity v Q₀ T₀)
      (regProd (chiForms Q₀ T₀) 1 fun v => NF.siegelDensity v Q₀ T₀) (normOrder F) := by
  obtain ⟨Gf, -, h, -⟩ := reg_core Q₀ T₀ hr hpd hpdT fr hloc
  simp only [zpow_one] at h
  exact hasProd_normOrder_regProd hN (abs_chiForms_le Q₀ T₀) h

end QuadFormsKB.Tamagawa.Frames
