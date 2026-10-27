/-
# Siegel's formula for representations of forms by forms: the statement and its consistency checks

**Layer:** $F$ a totally real number field; forms over $\mathcal O_F$, lattices in $F^N$ (`Lattices/`).

**Defines**
* (in `FrameArch.lean`) `epsNR N r`: $\tfrac12$ if $r = N$, else $1$, applied at every place; `epsCodimOne N r`: $\tfrac12$ if $r = N - 1$,
  else $1$, applied once (together: Siegel's $\varepsilon$, which is $\tfrac12$ for $r \ge N - 1$; Siegel 1935 [unverified]);
* `archDensityForm N r D_Q D_T` (**the archimedean density** $\beta_\sigma(Q, T)$ in the repository's coefficient coordinates):
  $$\beta_\infty(Q,T) = 2^{-r(r-1)/2}\prod_{i=0}^{r-1}\frac{\pi^{(N-i)/2}}{\Gamma(\frac{N-i}2)}\;D_T^{(N-r-1)/2}\,D_Q^{-r/2},$$
  $D_Q = \det(H_Q/2)$, $D_T = \det(H_T/2)$ (for $r = 1$ it is `archRepDensity`; the factor $2^{-r(r-1)/2}$ converts Siegel's Gram coordinates
  $a_{ij}$ to the coefficients $c_{ij} = 2a_{ij}$, $i<j$, of `repCountForm`);
* `siegelProductT Q₀ T₀` $= S(Q, T) = \varepsilon'\,|d_F|^{-r(2N-r-1)/4}\prod_\sigma\varepsilon\,\beta_\sigma(Q,T)\prod_\mathfrak p\alpha_\mathfrak p(Q, T)$,
  $\alpha_\mathfrak p = \varepsilon\beta_\mathfrak p$ = `NF.siegelDensity`;
* `SiegelFormsAt Q₀ T₀`: $\sum_{\mathrm{cls}M\subseteq\mathrm{gen}\,\mathcal O_F^N} r_M(T)/|O(M)| = \mathrm{Mass}(\mathcal O_F^N)\cdot S(Q, T)$.

*Convention.* Over $F \ne \mathbb Q$ Siegel's factor $\varepsilon = \tfrac12$ for $r = N$ is
applied at **every** place (each archimedean $\beta_\sigma$ and each $\beta_\mathfrak p$). This is what makes $T = Q$ the mass formula
(`siegelFormsAt_self_iff`); over $\mathbb Q$ it is Siegel's $\varepsilon\,\beta_\infty\prod_p\alpha_p$. For $r = N - 1$ Siegel's $\varepsilon = \tfrac12$ is one global
factor $\varepsilon'$ (`epsCodimOne`; from $\tau(SO_1) = 1$). For $r \le N - 2$ all factors are $1$. (For $N - r = 2$
and $N \le 2$
the product converges only conditionally and the regularized products of `FrameSiegelReg.lean`, `FrameSiegelLow.lean` are used;
`FrameSiegelAll.lean` collects every rank.)

**Proves**
* `siegelFormsAt_unary_iff`: for $T = \langle m\rangle$ it is the `SiegelFormulaAt Q₀ m` (consistency check $r = 1$);
* `siegelFormsAt_self_iff`: for $T = Q$ it is the mass formula `MassFormulaHolds Q₀` (consistency check $T = Q$), hence
  `siegelFormsAt_self` over every totally real field in rank $N \ge 4$.

Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.FrameRepMass
import QuadFormsKB.Tamagawa.FrameArch
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSiegelTotallyReal
import QuadFormsKB.Tamagawa.LatIndexCard

open NumberField Matrix
open scoped Real

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Frames

open QuadFormsKB.Tamagawa Lattices LocalDensity IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] {N r : ℕ}

/-- **Siegel's product for $T$ by $Q$** (Siegel 1935, Hauptsatz; over $F$: Siegel 1937 [unverified]):
$$S(Q, T) = \varepsilon'\,|d_F|^{-r(2N-r-1)/4}\prod_{\sigma}\varepsilon\,\beta_\sigma(Q, T)\prod_\mathfrak p\alpha_\mathfrak p(Q, T),$$
$\varepsilon = $ `epsNR N r` ($\tfrac12$ at every place if $r = N$), $\varepsilon' = $ `epsCodimOne N r` ($\tfrac12$ once if $r = N - 1$): together
they are Siegel's $\varepsilon$. -/
@[kb "siegel1935" "Hauptsatz (local side, forms by forms) [unverified]"]
def siegelProductT (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r) : ℝ :=
  epsCodimOne N r * |(discr F : ℝ)| ^ (-((r : ℝ) * (2 * N - r - 1)) / 4) *
    (∏ σ : F →ₐ[ℚ] ℂ, epsNR N r * archDensityForm N r (detGram Q₀ σ) (detGram T₀ σ)) *
    ∏' v : HeightOneSpectrum (𝓞 F), NF.siegelDensity v Q₀ T₀

/-- **Siegel's formula for representations of $T$ by the genus of $Q$** (Siegel 1935, Hauptsatz [unverified]; over $F$: Siegel 1937
[unverified]): with $L = \mathcal O_F^N$,
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(T)}{|O(M)|} = \mathrm{Mass}(L)\cdot S(Q, T).$$

Field:
- `repMass_eq`: the displayed identity.

A statement, not an input: it is proved here for $T = Q$ (the mass formula), for $r = 1$ (`SiegelFormulaAt`), in
`FrameSiegelMain.lean` for $Q = T\perp Q'$ with $N - r \ge 3$, and in `FrameSiegelUncond.lean` for every $Q$ when $N \ge 3$, $N - r \ne 2$
(every rank: `FrameSiegelAll.lean`). -/
@[kb "siegel1935" "Hauptsatz [unverified]"]
structure SiegelFormsAt (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r) : Prop where
  repMass_eq : repMassT (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F N) (T₀.map (algebraMap (𝓞 F) F)) =
    mass (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F N) * siegelProductT Q₀ T₀

/-! ### Consistency check $r = 1$: Siegel's formula for numbers -/

/-- $r_M(\langle m\rangle) = r_M(m)$: a frame of $\langle m\rangle$ is one vector of value $m$. -/
theorem repCountT_unary (Q : QuadForm F N) (M : Lat F N) (m : F) :
    repCountT Q M (DVR.unary m) = repCount Q M m := by
  unfold repCountT QuadFormsKB.Tamagawa.repCount
  refine Nat.card_congr ?_
  let e : Matrix (Fin N) (Fin 1) F ≃ (Fin N → F) :=
    { toFun := fun X l => X l 0
      invFun := fun x => Matrix.of fun l _ => x l
      left_inv := fun X => by ext l i; rw [Fin.fin_one_eq_zero i]; rfl
      right_inv := fun x => rfl }
  refine Equiv.subtypeEquiv e ?_
  intro X
  have hc : Q.compMat X = DVR.unary m ↔ Q.eval (fun l => X l 0) = m := by
    constructor
    · intro h
      have := congrArg (fun T : QuadForm F 1 => T.coeff 0 0) h
      simpa [QuadForm.compMat_coeff, DVR.unary, QuadForm.diag] using this
    · intro h
      apply QuadForm.ext_upper
      intro i j _
      rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
      simpa [QuadForm.compMat_coeff, DVR.unary, QuadForm.diag] using h
  rw [hc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1 0, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, h2⟩
    rw [Fin.fin_one_eq_zero j]; exact h1

theorem repMassT_unary (Q : QuadForm F N) (L : Lat F N) (m : F) :
    repMassT Q L (DVR.unary m) = repMass Q L m := by
  unfold repMassT repMass
  refine finsum_congr fun c => finsum_congr fun _ => ?_
  congr 2
  induction c using Quotient.inductionOn with
  | _ M => exact congrArg Nat.cast (repCountT_unary Q M m)

/-- For $N \ge 3$, $S(Q, \langle m\rangle)$ is the `siegelProduct Q₀ m`. -/
theorem siegelProductT_unary (Q₀ : QuadForm (𝓞 F) N) (hN : 3 ≤ N) (m : 𝓞 F) :
    siegelProductT Q₀ (DVR.unary m) = siegelProduct Q₀ m := by
  have hdet : (DVR.unary m).hessian.det = 2 * m := by
    simp [QuadForm.hessian, DVR.unary, QuadForm.diag, Matrix.det_unique, Matrix.diagonal_apply]
    ring
  have hg : ∀ σ : F →ₐ[ℚ] ℂ, detGram (DVR.unary m) σ = ‖σ (algebraMap (𝓞 F) F m)‖ := by
    intro σ
    unfold detGram
    rw [hdet]
    congr 1
    simp only [map_mul, map_ofNat, pow_one]
    rw [mul_div_cancel_left₀ _ (two_ne_zero)]
  have hε : epsNR N 1 = 1 := by
    unfold epsNR; rw [if_neg (by omega)]
  unfold siegelProductT siegelProduct
  rw [show epsCodimOne N 1 = 1 from if_neg (by omega), one_mul]
  have hne : ¬ (N = 1) := by omega
  have h1 : ∀ v : HeightOneSpectrum (𝓞 F),
      NF.siegelDensity v Q₀ (DVR.unary m) = NF.localDensity v Q₀ m := by
    intro v
    unfold NF.siegelDensity
    rw [if_neg hne, one_mul, NF.localDensityForm_unary]
  simp only [h1, hg, hε, one_mul, archDensityForm_one]
  congr 2
  push_cast
  ring_nf

/-- **Consistency check $r = 1$:** for $T = \langle m\rangle$ Siegel's formula for forms is the `SiegelFormulaAt Q₀ m`
(Siegel's formula
for the number $m$, proved over every totally real field in rank $N \ge 4$, `siegelFormulaAt_totallyReal`). -/
@[kb "siegel1935" "Hauptsatz, r = 1 [unverified]"]
theorem siegelFormsAt_unary_iff (Q₀ : QuadForm (𝓞 F) N) (hN : 3 ≤ N) (m : 𝓞 F) :
    SiegelFormsAt Q₀ (DVR.unary m) ↔ SiegelFormulaAt Q₀ m := by
  have hm : (DVR.unary m).map (algebraMap (𝓞 F) F) = DVR.unary (algebraMap (𝓞 F) F m) := by
    ext i j
    simp [QuadForm.map, DVR.unary, QuadForm.diag, Matrix.diagonal_apply]
  have hp := siegelProductT_unary Q₀ hN m
  constructor
  · intro h
    refine ⟨?_⟩
    have := h.repMass_eq
    rw [hm, repMassT_unary, hp] at this
    exact this
  · intro h
    refine ⟨?_⟩
    have := h.repMass_eq
    rw [hm, repMassT_unary, hp]
    exact this

/-! ### Consistency check $T = Q$: the mass formula -/

/-- $Q_0$ is integral on $\mathcal O_F^N$. -/
theorem isIntegral_stdLat_self (Q₀ : QuadForm (𝓞 F) N) :
    IsIntegral (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F N).1 := by
  intro x hx
  obtain ⟨y', rfl⟩ := mem_intVec_iff_exists.mp hx
  refine ⟨Q₀.eval y', ?_⟩
  show _ = (Q₀.map (algebraMap (𝓞 F) F)).evalIn F (intCoe y')
  rw [← eval_map_comp]

/-- **Lattices of the genus of $\mathcal O_F^N$ have index $1$:** $\mathrm{latIndex}(M) = 1$, because a local isometry
has $\|\det\| = 1$. -/
theorem latIndex_eq_one_of_sameGenus {Q : QuadForm F N} (hQ : Q.Nondegenerate) {M : Lat F N}
    (hM : SameGenus Q (stdLat F N).1 M.1) : SiegelSpace.latIndex M = 1 := by
  have hv : ∀ v : HeightOneSpectrum (𝓞 F), SiegelSpace.locIndex v M = 1 := by
    intro v
    obtain ⟨A, hA⟩ := SiegelSpace.exists_isLocModel' v M
    rw [SiegelSpace.locIndex_eq v hA.2]
    obtain ⟨g, hg, hgM⟩ := hM v
    set gA := Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) A with hgA
    have hstd : locAct v (gA⁻¹ * g) (std v) = std v := by
      have h1 : loc v (Lattices.latOf A) = locAct v gA (std v) := by
        rw [Lattices.latOf, loc_glImage, loc_intVec]
      have h2 : loc v (stdLat F N).1 = std v := loc_intVec v
      rw [h2] at hgM
      rw [locAct_mul, hgM, ← hA.2, h1, locAct_inv_locAct]
    obtain ⟨H, hH⟩ := exists_GL_o_of_locAct_std v _ hstd
    have e3 : ((H.val.det : v.adicCompletionIntegers F) : v.adicCompletion F) = (gA⁻¹ * g).val.det := by
      rw [← hH, show ((H.val.det : v.adicCompletionIntegers F) : v.adicCompletion F) =
        algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) H.val.det from rfl, RingHom.map_det]
      rfl
    have hU1 : ‖((H.val.det : v.adicCompletionIntegers F) : v.adicCompletion F)‖ = 1 :=
      norm_coe_unit v (H.isUnit.map Matrix.detMonoidHom)
    have hdet : g.val.det = gA.val.det * (gA⁻¹ * g).val.det := by
      rw [← det_mul, ← Units.val_mul, mul_inv_cancel_left]
    have hg1 : ‖g.val.det‖ = 1 := by
      rcases det_eq_one_or_neg_one Q hQ (⟨g, hg⟩ : orthGroup Q (v.adicCompletion F)) with h | h
      · simp only at h; rw [h, norm_one]
      · simp only at h; rw [h, norm_neg, norm_one]
    have hAd : algebraMap F (v.adicCompletion F) A.val.det = gA.val.det := by
      rw [RingHom.map_det]; rfl
    rw [hAd]
    have := congrArg norm hdet
    rw [norm_mul, ← e3, hU1, mul_one, hg1] at this
    exact this.symm
  unfold SiegelSpace.latIndex
  rw [finprod_congr hv, finprod_one]

/-- **A sublattice of the genus of $\mathcal O_F^N$ inside another lattice of the genus is equal to it** (indices
multiply, `latIndex_mul_relIndex`). -/
theorem eq_of_le_of_sameGenus {Q : QuadForm F N} (hQ : Q.Nondegenerate) {M' M : Lat F N}
    (h1 : SameGenus Q (stdLat F N).1 M'.1) (h2 : SameGenus Q (stdLat F N).1 M.1) (hle : M'.1 ≤ M.1) :
    M' = M := by
  have h := SiegelSpace.latIndex_mul_relIndex hle
  rw [latIndex_eq_one_of_sameGenus hQ h1, latIndex_eq_one_of_sameGenus hQ h2, mul_one] at h
  have h3 : M'.1.toAddSubgroup.relIndex M.1.toAddSubgroup = 1 := by exact_mod_cast h.symm
  rw [AddSubgroup.relIndex_eq_one] at h3
  exact Lattices.Lat.ext (le_antisymm hle h3)

/-- A frame of $Q$ itself ($N$ columns, $Q\circ X = Q$) is an isometry. -/
theorem exists_orth_of_compMat {Q : QuadForm F N} (hQ : Q.Nondegenerate) {X : Matrix (Fin N) (Fin N) F}
    (hX : Q.compMat X = Q) : ∃ γ : orthGroup Q F, ((γ : GL (Fin N) F).val) = X := by
  have hdet : X.det * X.det = 1 := by
    have h := congrArg QuadForm.hessian hX
    rw [QuadForm.hessian_compMat] at h
    have h' := congrArg Matrix.det h
    rw [det_mul, det_mul, det_transpose] at h'
    apply mul_right_cancel₀ hQ
    linear_combination h'
  have hu : IsUnit X.det := IsUnit.of_mul_eq_one _ hdet
  have heval : ∀ z, Q.eval (X *ᵥ z) = Q.eval z := fun z => by
    rw [← QuadForm.eval_compMat, hX]
  exact ⟨⟨Matrix.nonsingInvUnit X hu, mem_orthGroup_of_eval Q (ρ := Matrix.nonsingInvUnit X hu) heval⟩, rfl⟩

theorem glImage_le_of_cols {X : Matrix (Fin N) (Fin N) F} {γ : GL (Fin N) F} (hγ : γ.val = X) {M : Lat F N}
    (hc : ∀ j, (fun i => X i j) ∈ M.1) : glImage γ intVec ≤ M.1 := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_glImage.mp hx
  obtain ⟨c, rfl⟩ := eq_sum_of_mem_intVec hy
  rw [hγ, mulVec_sum]
  refine M.1.sum_mem fun i _ => ?_
  have : X *ᵥ (c i • (Pi.single i (1 : F) : Fin N → F)) = c i • (fun j => X j i) := by
    ext j
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, Algebra.smul_def]
    ring
  rw [this]
  exact M.1.smul_mem _ (hc i)

/-- **A frame of $Q$ in a lattice $M$ of the genus of $\mathcal O_F^N$ is an isometry $\mathcal O_F^N \to M$ (onto).** -/
theorem frame_isometry {Q : QuadForm F N} (hQ : Q.Nondegenerate) {M : Lat F N}
    (hM : SameGenus Q (stdLat F N).1 M.1) {X : Matrix (Fin N) (Fin N) F}
    (hc : ∀ j, (fun i => X i j) ∈ M.1) (hX : Q.compMat X = Q) :
    ∃ γ : orthGroup Q F, ((γ : GL (Fin N) F).val) = X ∧ glImage (γ : GL (Fin N) F) intVec = M.1 := by
  obtain ⟨γ, hγ⟩ := exists_orth_of_compMat hQ hX
  refine ⟨γ, hγ, ?_⟩
  have hle := glImage_le_of_cols hγ hc
  have hgen : Lat.image (γ : GL (Fin N) F) (stdLat F N) ∈ latGenus Q (stdLat F N) :=
    image_mem_latGenus Q (SameGenus.refl Q (stdLat F N).1) γ
  have := eq_of_le_of_sameGenus hQ hgen hM hle
  exact congrArg Subtype.val this

/-- **The frames of $Q$ in $\mathcal O_F^N$ are the automorphisms:** $r_{\mathcal O_F^N}(Q) = |O(\mathcal O_F^N)|$. -/
theorem repCountT_std_self {Q : QuadForm F N} (hQ : Q.Nondegenerate) :
    repCountT Q (stdLat F N) Q = Nat.card (autLat Q (stdLat F N).1) := by
  unfold repCountT
  have hM : SameGenus Q (stdLat F N).1 (stdLat F N).1 := SameGenus.refl Q _
  have hcols : ∀ g : autLat Q (stdLat F N).1, ∀ j,
      (fun i => ((g.1 : orthGroup Q F) : GL (Fin N) F).val i j) ∈ (stdLat F N).1 := by
    intro g j
    have h := mulVec_mem_glImage (γ := ((g.1 : orthGroup Q F) : GL (Fin N) F))
      (single_one_mem_intVec (F := F) j)
    rw [(mem_autLat Q).mp g.2] at h
    rw [mulVec_single_one] at h
    exact h
  have hcomp : ∀ g : autLat Q (stdLat F N).1,
      Q.compMat ((g.1 : orthGroup Q F) : GL (Fin N) F).val = Q := by
    intro g
    have := compMat_orth Q (g.1 : orthGroup Q F).2 (1 : Matrix (Fin N) (Fin N) F)
    rwa [Matrix.mul_one, QuadForm.compMat_one] at this
  symm
  refine Nat.card_eq_of_bijective
    (fun g => (⟨((g.1 : orthGroup Q F) : GL (Fin N) F).val, hcols g, hcomp g⟩ :
      {X : Matrix (Fin N) (Fin N) F // (∀ j, (fun i => X i j) ∈ (stdLat F N).1) ∧ Q.compMat X = Q})) ⟨?_, ?_⟩
  · intro g g' h
    have := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext (Units.ext this))
  · intro X
    obtain ⟨γ, hγ, hγ'⟩ := frame_isometry hQ hM X.2.1 X.2.2
    exact ⟨⟨γ, hγ'⟩, Subtype.ext hγ⟩

/-- **$\sum_{\mathrm{cls}M}r_M(Q)/|O(M)| = 1$** for $L = \mathcal O_F^N$: a frame of $Q$ in $M \in \mathrm{gen}(L)$ is an isometry $L \to M$, onto
because $M$ and $L$ have the same local volumes; so only the class of $L$ contributes, with $r_L(Q) = |O(L)|$. -/
theorem repMassT_self (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) :
    repMassT (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F N) (Q₀.map (algebraMap (𝓞 F) F)) = 1 := by
  classical
  set Q := Q₀.map (algebraMap (𝓞 F) F) with hQdef
  have hQ : Q.Nondegenerate := hpd.nondegenerate
  have hint : IsIntegral Q (stdLat F N).1 := isIntegral_stdLat_self Q₀
  have hfin := finite_autLat hpd (stdLat F N).2 hint
  have hpos : 0 < Nat.card (autLat Q (stdLat F N).1) := Nat.card_pos
  set c0 : LatClass Q := Quotient.mk (latSetoid Q) (stdLat F N) with hc0
  have hc0S : c0 ∈ genusClasses Q (stdLat F N) := ⟨stdLat F N, rfl, SameGenus.refl Q _⟩
  unfold repMassT
  rw [finsum_eq_single _ c0 ?_]
  · rw [finsum_eq_if, if_pos hc0S]
    have h1 : LatClass.repCountT Q c0 Q = Nat.card (autLat Q (stdLat F N).1) := repCountT_std_self hQ
    have h2 : LatClass.autCard Q c0 = Nat.card (autLat Q (stdLat F N).1) := rfl
    rw [h1, h2]
    have : (Nat.card (autLat Q (stdLat F N).1) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    field_simp
  · intro c hc
    by_cases hcS : c ∈ genusClasses Q (stdLat F N)
    · rw [finsum_eq_if, if_pos hcS]
      obtain ⟨M, rfl, hM⟩ := hcS
      have h0 : repCountT Q M Q = 0 := by
        unfold repCountT
        rw [Nat.card_eq_zero]
        left
        refine ⟨fun X => ?_⟩
        obtain ⟨γ, -, hγ⟩ := frame_isometry hQ hM X.2.1 X.2.2
        apply hc
        exact Quotient.sound (IsIsometric.symm Q ⟨γ, γ.2, hγ⟩)
      show ((repCountT Q M Q : ℕ) : ℝ) / _ = 0
      rw [h0]; simp
    · rw [finsum_eq_if, if_neg hcS]

/-- $S(Q, Q) = \mu_{\mathrm{Tam}}(K_{SO})$ (`tamagawaK`): $\varepsilon\,\beta_\sigma(Q,Q) = \mathrm{vol}(SO(V_\sigma))$ and $\alpha_\mathfrak p(Q,Q) = $
`siegelDensity`. -/
theorem siegelProductT_self (Q₀ : QuadForm (𝓞 F) N) (hN : 1 ≤ N) : siegelProductT Q₀ Q₀ = tamagawaK Q₀ := by
  have key : ∀ D : ℝ, 0 ≤ D → epsNR N N * archDensityForm N N D D = archVolSO N D := by
    intro D hD
    rcases hD.eq_or_lt with h0 | hpos
    · subst h0
      have h1 : (0 : ℝ) ^ (((N : ℝ) - N - 1) / 2) = 0 :=
        Real.zero_rpow (by have : ((N : ℝ) - N - 1) / 2 = -1 / 2 := by ring
                           rw [this]; norm_num)
      have h2 : (0 : ℝ) ^ (-((N : ℝ) + 1) / 2) = 0 :=
        Real.zero_rpow (by have : (0 : ℝ) < (N : ℝ) + 1 := by positivity
                           intro h; linarith)
      unfold archDensityForm archVolSO
      rw [h1, h2]; ring
    · exact archDensityForm_self N hN hpos
  unfold siegelProductT tamagawaK
  rw [show epsCodimOne N N = 1 from if_neg (by omega), one_mul]
  have hprod : (∏ σ : F →ₐ[ℚ] ℂ, epsNR N N * archDensityForm N N (detGram Q₀ σ) (detGram Q₀ σ)) =
      ∏ σ : F →ₐ[ℚ] ℂ, archVolSO N (detGram Q₀ σ) :=
    Finset.prod_congr rfl fun σ _ => key _ (norm_nonneg _)
  rw [hprod]
  congr 2
  ring_nf

/-- **Consistency check $T = Q$:** Siegel's formula for $T = Q$ is the mass formula $\mathrm{Mass}(L) = \mu_{\mathrm{Tam}}(K_{SO})^{-1}$. -/
@[kb "siegel1935" "Hauptsatz, T = S (the mass formula) [unverified]"]
theorem siegelFormsAt_self_iff (Q₀ : QuadForm (𝓞 F) N) (hN : 1 ≤ N)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) :
    SiegelFormsAt Q₀ Q₀ ↔ MassFormulaHolds Q₀ := by
  have h1 := repMassT_self Q₀ hpd
  have h2 := siegelProductT_self Q₀ hN
  have hmp := mass_pos hpd (stdLat F N) (isIntegral_stdLat_self Q₀)
  unfold MassFormulaHolds
  constructor
  · intro h
    have h3 := h.repMass_eq
    rw [h1, h2] at h3
    exact eq_inv_of_mul_eq_one_left h3.symm
  · intro h
    refine ⟨?_⟩
    rw [h1, h2]
    have hK : tamagawaK Q₀ ≠ 0 := by
      intro h0
      rw [h0, _root_.inv_zero] at h
      exact hmp.ne' h
    rw [show Lattices.mass (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F N) = (tamagawaK Q₀)⁻¹ from h]
    exact (inv_mul_cancel₀ hK).symm

/-- **Siegel's formula for $T = Q$ over every totally real field** in rank $N \ge 4$ (unconditional, from the mass formula
`massFormula_all_ranks_totallyReal`). -/
@[kb "siegel1935" "Hauptsatz, T = S [unverified]"]
theorem siegelFormsAt_self [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) N) (hN : 4 ≤ N)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) : SiegelFormsAt Q₀ Q₀ :=
  (siegelFormsAt_self_iff Q₀ (by omega) hpd).mpr
    (Measure.Weil.massFormula_all_ranks_totallyReal hN Q₀ hpd)

/-- **Siegel's formula for $T = \langle m\rangle$ over every totally real field** in rank $N \ge 4$, $m$ totally positive
(`siegelFormulaAt_totallyReal`). -/
@[kb "siegel1935" "Hauptsatz, r = 1 [unverified]"]
theorem siegelFormsAt_unary [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) N) (hN : 4 ≤ N)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) {m : 𝓞 F}
    (hm : ∀ v, 0 < QuadFormsKB.HilbertModular.realEmb F v (algebraMap (𝓞 F) F m)) :
    SiegelFormsAt Q₀ (DVR.unary m) :=
  (siegelFormsAt_unary_iff Q₀ (by omega) m).mpr (Measure.Weil.siegelFormulaAt_totallyReal hN Q₀ hpd hm)

end QuadFormsKB.Tamagawa.Frames
