/-
# Invariance of the Siegel Eisenstein series of degree $r$ under $\mathrm{SL}_r(\mathcal O_F)$
**Layer:** local at each finite place $v$ of a totally real number field $F$ (dyadic places included), then global.

**Setting.** As in `EisensteinBigCell.lean`: $Q = \sum_{i<n}b_ix_i^2$ with $b_i \in \mathcal O_F$ totally positive, $n = 2m$ (0-based
indices), $\Phi_v = \mathbf 1_{L_v^r}$ at every finite place, $Z = (Z_w)_w \in \mathbb H_r^d$, the archimedean section `archSecR` of weight
$m$, and $E(g_Z, s, \Phi) = \sum_{\gamma\in P(F)\backslash\mathrm{Sp}_{2r}(F)}f_\infty(\gamma g_Z, s)f_f(\gamma, s)$ (`eisTermR`, `eisensteinR`).
For $U \in \mathrm{GL}_r(F)$, $U\cdot Z$ is $(\sigma_w(U)Z_w\sigma_w(U)^{\mathsf T})_w$ (`actU`), and $m(U) = \operatorname{diag}(U, {}^tU^{-1})$.

**Results.**
* `denW_actU`, `denR_actU`: $\sigma_w(C)\,(U\cdot Z)_w + \sigma_w(D) = \big(\sigma_w(CU)Z_w + \sigma_w(D\,{}^tU^{-1})\big)\sigma_w(U)^{\mathsf T}$, so
  $j(\gamma, U\cdot Z) = j(\gamma m(U), Z)\prod_w\sigma_w(\det U)$;
* `archSecR_actU`: for $\det U = 1$, $f_\infty(\gamma g_{U\cdot Z}, s) = f_\infty(\gamma m(U)g_Z, s)$, every $s$;
* `fixesOne_spM_det_one`: $\omega_v(m(A))\mathbf 1_{L_v^r} = \mathbf 1_{L_v^r}$ for $A \in \mathrm{SL}_r(\mathcal O_v)$ at **every** finite place
  ($\chi_V(1) = 1$, $|1|_v = 1$; no goodness needed);
* `finSecR_mul_spM_sZero`: $f_f(\gamma m(U), s_0) = f_f(\gamma, s_0)$ for $U \in \mathrm{SL}_r(\mathcal O_F)$;
* **`eisensteinR_actU`**: $E(g_{U\cdot Z}, s_0, \Phi) = E(g_Z, s_0, \Phi)$ for $U \in \mathrm{SL}_r(\mathcal O_F)$, by the bijection
  $P(F)\gamma \mapsto P(F)\gamma m(U)$ of $P(F)\backslash\mathrm{Sp}_{2r}(F)$ (`pquotMulRight`). No convergence is needed (both sides are the
  same `tsum` after reindexing).

Restricting to $\det U = 1$ avoids the character $\chi_V(\det U)$ (for a unit $\det U$, $\prod_v\chi_{V,v}(\det U) = 1$ is Hilbert
reciprocity); $\mathrm{SL}_r(\mathcal O_F)$ suffices for the degenerate Fourier coefficients (`SingularRadical.lean`). For $r = 1$ the
statement is empty ($\mathrm{SL}_1 = 1$).

Sources: Kudla, *Some extensions of the Siegel–Weil formula* (2008), §1 (left $\mathrm{Sp}_{2r}(F)$-invariance of $E$) [unverified];
Freitag, *Siegelsche Modulfunktionen* (1983), Ch. I (invariance of Siegel modular forms under $Z \mapsto UZ{}^tU$) [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.EisensteinBigCell
import QuadFormsKB.SiegelWeil.Forms.FourierPhi

open Matrix NumberField IsDedekindDomain Filter
open QuadFormsKB.HilbertModular QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData QuadFormsKB.WeilRep.Genus QuadFormsKB.Analysis

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

/-! ### Local: $m(A)$, $A \in \mathrm{SL}_r(\mathcal O_v)$, fixes the lattice function at every finite place -/

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {m r : ℕ}

local notation "Fv" => v.adicCompletion F

variable (a : Fin (2 * m) → (v.adicCompletion F)ˣ)

/-- $\omega_v(m(A))\mathbf 1_{L_v^r} = \mathbf 1_{L_v^r}$ for $A$, $A^{-1}$ with entries in $\mathcal O_v$ and $\det A = 1$, at every finite place. -/
lemma fixesOne_spM_det_one (A : GL (Fin r) Fv)
    (hA : ∀ i j, Valued.v ((A : Matrix (Fin r) (Fin r) Fv) i j) ≤ 1)
    (hA' : ∀ i j, Valued.v (((A⁻¹ : GL (Fin r) Fv) : Matrix (Fin r) (Fin r) Fv) i j) ≤ 1)
    (hdet : (A : Matrix (Fin r) (Fin r) Fv).det = 1) :
    FixesOne v a (spM A) := by
  unfold FixesOne
  apply Subtype.ext
  rw [weilRepSpV_spM, endM_apply, coe_oneSG]
  funext X
  have hmap : Matrix.GeneralLinearGroup.map (RingHom.id Fv) A = A := by ext; rfl
  simp only [opMg, hmap]
  rw [hdet, chiV_one (isModel_V v), md_one (isModel_V v), Complex.ofReal_one, one_pow, one_mul, one_mul,
    oneVG_eq_indicator, oneVG_eq_indicator]
  have hiff : (∀ i l, Valued.v ((X * (A : Matrix (Fin r) (Fin r) Fv)) i l) ≤ 1) ↔ ∀ i l, Valued.v (X i l) ≤ 1 := by
    have hint : ∀ (Y : PtG m r Fv) (M : Matrix (Fin r) (Fin r) Fv), (∀ i j, Valued.v (M i j) ≤ 1) →
        (∀ i l, Valued.v (Y i l) ≤ 1) → ∀ i l, Valued.v ((Y * M) i l) ≤ 1 := by
      intro Y M hM hY i l
      rw [mul_apply]
      exact Valuation.map_sum_le _ fun j _ => by rw [map_mul]; exact mul_le_one' (hY i j) (hM j l)
    refine ⟨fun h => ?_, hint X _ hA⟩
    have := hint _ _ hA' h
    rwa [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at this
  simp only [hiff]

end Local

/-! ### Global -/

section Global

variable {F : Type} [Field F] [NumberField F] {m r : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

/-- $\mathrm{SL}_r(\mathcal O_F)$: $U \in \mathrm{GL}_r(F)$ with $U$, $U^{-1}$ integral and $\det U = 1$. -/
def IsSLInt (U : GL (Fin r) F) : Prop :=
  IsIntegralMat (U : Matrix (Fin r) (Fin r) F) ∧ IsIntegralMat ((U⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) ∧
    (U : Matrix (Fin r) (Fin r) F).det = 1

lemma valued_map_le_one_of_isIntegralMat (v : HeightOneSpectrum (𝓞 F)) {M : Matrix (Fin r) (Fin r) F}
    (hM : IsIntegralMat M) (i j : Fin r) : Valued.v (algebraMap F (v.adicCompletion F) (M i j)) ≤ 1 := by
  obtain ⟨o, ho⟩ := hM i j
  rw [← ho]
  exact valued_algebraMap_int v o

/-- **$f_f(\gamma m(U), s_0) = f_f(\gamma, s_0)$** for $U \in \mathrm{SL}_r(\mathcal O_F)$ and the lattice function at every place. -/
theorem finSecR_mul_spM_sZero (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (γ : Sp r F) {U : GL (Fin r) F}
    (hU : IsSLInt U) :
    finSecR (unitsOfInt b hb) (fun v => oneSG v m r) (γ * spM U) (sZero m r) =
      finSecR (unitsOfInt b hb) (fun v => oneSG v m r) γ (sZero m r) := by
  rw [finSecR_sZero, finSecR_sZero]
  congr 1; funext v
  rw [map_mul, locSp_spM, secRV_eq, secRV_eq, map_mul, Module.End.mul_apply]
  have h1 : FixesOne v (aV (unitsOfInt b hb) v)
      (spM (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) U)) := by
    apply fixesOne_spM_det_one
    · intro i j
      exact valued_map_le_one_of_isIntegralMat v hU.1 i j
    · intro i j
      have : (((Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) U)⁻¹ : GL (Fin r) _) :
          Matrix (Fin r) (Fin r) _) i j = algebraMap F (v.adicCompletion F)
            (((U⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j) := by
        rw [← map_inv]; rfl
      rw [this]
      exact valued_map_le_one_of_isIntegralMat v hU.2.1 i j
    · rw [det_map_GL, hU.2.2, map_one]
  rw [h1]

variable [IsTotallyReal F]

/-- $\sigma_w(C)(U\cdot Z)_w + \sigma_w(D) = \mathrm{denW}(\gamma m(U), Z)_w\,\sigma_w(U)^{\mathsf T}$. -/
lemma denW_actU (γ : Sp r F) (U : GL (Fin r) F) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (w : InfinitePlace F) :
    denW γ (actU (U : Matrix (Fin r) (Fin r) F) Z) w =
      denW (γ * spM U) Z w * (embC w (U : Matrix (Fin r) (Fin r) F))ᵀ := by
  have e : ((γ * spM U : Sp r F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) =
      fromBlocks (blockA γ) (blockB γ) (blockC γ) (blockD γ) *
        fromBlocks (U : Matrix (Fin r) (Fin r) F) 0 0 (((U⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F))ᵀ := by
    rw [← spM_coe, ← eq_fromBlocks]; rfl
  have hC : blockC (γ * spM U) = blockC γ * (U : Matrix (Fin r) (Fin r) F) := by
    show ((γ * spM U : Sp r F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F).toBlocks₂₁ = _
    rw [e, fromBlocks_multiply, toBlocks_fromBlocks₂₁, Matrix.mul_zero, add_zero]
  have hD : blockD (γ * spM U) = blockD γ * (((U⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F))ᵀ := by
    show ((γ * spM U : Sp r F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F).toBlocks₂₂ = _
    rw [e, fromBlocks_multiply, toBlocks_fromBlocks₂₂, Matrix.mul_zero, zero_add]
  have hUU : ((U⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)ᵀ * (U : Matrix (Fin r) (Fin r) F)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
  have hUUe : (embC w ((U⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F))ᵀ * (embC w (U : Matrix (Fin r) (Fin r) F))ᵀ = 1 := by
    rw [embC, embC, ← Matrix.transpose_map, ← Matrix.transpose_map, ← map_mul_emb, hUU]
    exact Matrix.map_one _ (by simp) (by simp)
  rw [denW, denW, hC, hD, map_mul_emb, map_mul_emb, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc]
  have hT : ((((U⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F))ᵀ.map (fun x => (realEmb F w x : ℂ))) *
      (embC w (U : Matrix (Fin r) (Fin r) F))ᵀ = 1 := by
    rw [Matrix.transpose_map]; exact hUUe
  rw [Matrix.mul_assoc ((blockD γ).map _), hT, Matrix.mul_one]
  simp only [actU, embC, Matrix.mul_assoc]

/-- $j(\gamma, U\cdot Z) = j(\gamma m(U), Z)\prod_w\sigma_w(\det U)$. -/
lemma denR_actU (γ : Sp r F) (U : GL (Fin r) F) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) :
    denR γ (actU (U : Matrix (Fin r) (Fin r) F) Z) =
      denR (γ * spM U) Z * ∏ w, (realEmb F w (U : Matrix (Fin r) (Fin r) F).det : ℂ) := by
  unfold denR
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [denW_actU, det_mul, det_transpose]
  congr 1
  have := RingHom.map_det ((Complex.ofRealHom).comp (realEmb F w)) (U : Matrix (Fin r) (Fin r) F)
  simpa [RingHom.mapMatrix_apply, Function.comp_def] using this.symm

/-- $\operatorname{Im}(U\cdot Z)_w = \sigma_w(U)\operatorname{Im}(Z_w)\sigma_w(U)^{\mathsf T}$, so its determinant is unchanged when $\det U = 1$. -/
lemma det_im_actU (U : Matrix (Fin r) (Fin r) F) (hU : U.det = 1) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ)
    (w : InfinitePlace F) : ((actU U Z w).map Complex.im).det = ((Z w).map Complex.im).det := by
  set A : Matrix (Fin r) (Fin r) ℝ := U.map (realEmb F w)
  have hA : embC w U = A.map (fun x => (x : ℂ)) := rfl
  have him : (actU U Z w).map Complex.im = A * (Z w).map Complex.im * Aᵀ := by
    ext i j
    simp only [actU, hA, Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, Complex.im_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul, Complex.im_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [Complex.mul_im]
  have hdA : A.det = 1 := by
    rw [show A.det = realEmb F w U.det from (RingHom.map_det _ _).symm, hU, map_one]
  rw [him, det_mul, det_mul, det_transpose, hdA, one_mul, mul_one]

/-- **The archimedean section at $U\cdot Z$**: $f_\infty(\gamma g_{U\cdot Z}, s) = f_\infty(\gamma m(U)g_Z, s)$ for $\det U = 1$, every $s$. -/
theorem archSecR_actU (γ : Sp r F) {U : GL (Fin r) F} (hU : (U : Matrix (Fin r) (Fin r) F).det = 1)
    (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (s : ℂ) :
    archSecR m (actU (U : Matrix (Fin r) (Fin r) F) Z) s γ = archSecR m Z s (γ * spM U) := by
  unfold archSecR
  rw [denR_actU, hU]
  simp only [map_one, Complex.ofReal_one, Finset.prod_const_one, mul_one, det_im_actU _ hU]

/-! ### Right multiplication on $P(F)\backslash\mathrm{Sp}_{2r}(F)$ -/

/-- Right multiplication by $g$ on $P(F)\backslash\mathrm{Sp}_{2r}(F)$, $P(F)\gamma \mapsto P(F)\gamma g$. -/
def pquotMulRight (g : Sp r F) : PQuot r F ≃ PQuot r F :=
  Quotient.congr (Equiv.mulRight g) fun a b => by
    simp only [QuotientGroup.rightRel_apply, Equiv.coe_mulRight, _root_.mul_inv_rev, mul_assoc, mul_inv_cancel_left]

lemma pquotMulRight_mk (g γ : Sp r F) :
    pquotMulRight g (Quotient.mk _ γ : PQuot r F) = Quotient.mk _ (γ * g) := rfl

/-- **The terms of $E(g_{U\cdot Z}, s_0)$ are those of $E(g_Z, s_0)$ permuted** by $P(F)\gamma \mapsto P(F)\gamma m(U)$. -/
lemma eisTermR_actU (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    {U : GL (Fin r) F} (hU : IsSLInt U) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) (q : PQuot r F) :
    eisTermR b hb hbpos (actU (U : Matrix (Fin r) (Fin r) F) Z) q = eisTermR b hb hbpos Z (pquotMulRight (spM U) q) := by
  induction q using Quotient.inductionOn with
  | h γ =>
    rw [pquotMulRight_mk]
    show globalSecR _ _ _ _ γ = globalSecR _ _ _ _ (γ * spM U)
    unfold globalSecR
    rw [archSecR_actU γ hU.2.2, finSecR_mul_spM_sZero b hb γ hU]

/-- **$E(g_{U\cdot Z}, s_0, \Phi) = E(g_Z, s_0, \Phi)$ for $U \in \mathrm{SL}_r(\mathcal O_F)$** (left $\mathrm{Sp}_{2r}(F)$-invariance of $E$ applied to
$m(U)$, which fixes the lattice function at every finite place). -/
@[kb "freitag1983" "Ch. I (Siegel modular forms are invariant under $Z \\mapsto UZ{}^tU$, $U \\in \\mathrm{SL}_r$) [unverified]; kudla2008 §1 [unverified]"]
theorem eisensteinR_actU (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i)))
    {U : GL (Fin r) F} (hU : IsSLInt U) (Z : InfinitePlace F → Matrix (Fin r) (Fin r) ℂ) :
    eisensteinR (unitsOfInt b hb) (fun v => oneSG v m r) (Filter.Eventually.of_forall fun _ => rfl)
        (isArchSectionR_archSecR b hb hbpos (actU (U : Matrix (Fin r) (Fin r) F) Z) (sZero m r)) =
      eisensteinR (unitsOfInt b hb) (fun v => oneSG v m r) (Filter.Eventually.of_forall fun _ => rfl)
        (isArchSectionR_archSecR b hb hbpos Z (sZero m r)) := by
  show ∑' q, eisTermR b hb hbpos (actU (U : Matrix (Fin r) (Fin r) F) Z) q = ∑' q, eisTermR b hb hbpos Z q
  simp only [eisTermR_actU b hb hbpos hU]
  exact (pquotMulRight (spM U)).tsum_eq (eisTermR b hb hbpos Z)

end Global

end QuadFormsKB.SiegelWeil.Forms
