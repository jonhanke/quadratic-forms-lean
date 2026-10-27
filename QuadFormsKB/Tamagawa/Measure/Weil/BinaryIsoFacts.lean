import QuadFormsKB.Tamagawa.Measure.Weil.BinaryIsoHyp
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryIsoSimilar
import QuadFormsKB.Tamagawa.Measure.Weil.TauTwoAnisotropic

/-!
# Isotropic binary forms: elementary facts

**Layer:** number fields. $F$ is a number field, $Q_0$ a binary quadratic form over $\mathcal O_F$, $Q = Q_0\otimes F$.

**Proves**
* `isotropicF_iff_not_anisotropicF`, `isotropicF_iff_isSquare`: $Q_0\otimes F$ is isotropic iff it is not anisotropic iff
  $-\det H_{Q_0}$ is a square in $F$;
* `isotropicF_hypForm`, `exists_isotropic_binary`: non-vacuity over every number field (the hyperbolic plane $x_0x_1$);
* **scaling** (only the line matters): `isIsoVec_smul`, `isoChar_smul` ($\chi_{ce} = \chi_e$ for $c\in F^\times$),
  `SOAdeleOne_smul`, `isoShellIco_smul`, `tauIso_smul`;
* **the other isotropic line**: `eigVal_mul_other_line` (at a place $K$: if $e, e'$ span different isotropic lines and
  $M\in SO(H)(K)$, then the eigenvalues satisfy $\chi_{e'}(M)\chi_e(M) = 1$, because $B(e,e')\ne0$ and $M$ preserves $B$),
  `isoChar_other_line` ($\chi_{e'} = \chi_e^{-1}$), `SOAdeleOne_other_line` (the same norm-one subgroup),
  `isoShellIco_other_line` (the shells are reflected, $t\mapsto -t$ in $\log\|\chi_e\|_{\mathbb A}$);
* `isoChar_hyp_other`: for the hyperbolic plane, the lines $F(1,0)$ and $F(0,1)$ give inverse characters.

Indices are 0-based: the "lines are different" hypothesis is $e_0e'_1 - e_1e'_0\ne0$.
-/

open MeasureTheory Measure Set Topology Matrix Filter
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa QuadFormsKB.QuadForm QuadFormsKB.Siegel QuadFormsKB.Tamagawa.ArchSOMeasure
  QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {F : Type} [Field F] [NumberField F]

/-! ### Isotropy and the discriminant -/

/-- **Isotropic means not anisotropic:** $Q_0\otimes F$ has a nonzero isotropic vector iff it is not anisotropic. -/
theorem isotropicF_iff_not_anisotropicF (Q₀ : QuadForm (𝓞 F) 2) : IsotropicF Q₀ ↔ ¬ AnisotropicF Q₀ := by
  constructor
  · rintro ⟨e, he0, he⟩ h
    exact he0 (h e he)
  · intro h
    by_contra h'
    apply h
    intro ξ hξ
    by_contra hne
    exact h' ⟨ξ, hne, hξ⟩

/-- **A binary form is isotropic iff $-\det H$ is a square:** $Q_0\otimes F$ is isotropic iff
$-\det H_{Q_0}$ is a square in $F$. -/
theorem isotropicF_iff_isSquare (Q₀ : QuadForm (𝓞 F) 2) :
    IsotropicF Q₀ ↔ IsSquare (algebraMap (𝓞 F) F (-Q₀.hessian.det)) := by
  rw [isotropicF_iff_not_anisotropicF, anisotropicF_iff_not_isSquare, not_not]

/-! ### Non-vacuity -/

/-- **The hyperbolic plane is isotropic** over every number field. -/
theorem isotropicF_hypForm : IsotropicF (hypForm F) := ⟨hypE F, isIsoVec_hypE⟩

variable (F) in
/-- **Non-vacuity:** over every number field there is a nondegenerate binary form over $\mathcal O_F$ that is isotropic
over $F$ (the hyperbolic plane $x_0x_1$). -/
theorem exists_isotropic_binary : ∃ Q₀ : QuadForm (𝓞 F) 2, Q₀.Nondegenerate ∧ IsotropicF Q₀ :=
  ⟨hypForm F, nondegenerate_hypForm, isotropicF_hypForm⟩

/-! ### Scaling the isotropic vector -/

section Scaling

variable {Q₀ : QuadForm (𝓞 F) 2} {e : Fin 2 → F} {c : F}

/-- **Scaling an isotropic vector:** $ce$ is isotropic for $c\in F^\times$. -/
theorem isIsoVec_smul (he : IsIsoVec Q₀ e) (hc : c ≠ 0) : IsIsoVec Q₀ (c • e) := by
  refine ⟨fun h => he.1 ?_, ?_⟩
  · have := congrArg (fun x => c⁻¹ • x) h
    simpa [smul_smul, inv_mul_cancel₀ hc] using this
  · have h := (qF_eq_zero_iff_hessian Q₀ e).mp he.2
    rw [qF_eq_zero_iff_hessian, mulVec_smul, dotProduct_smul, smul_dotProduct, h]
    simp

variable (hQ : Q₀.Nondegenerate)

/-- **Only the line matters:** $\chi_{ce} = \chi_e$ for $c\in F^\times$ (the eigenvalue of an element of $SO(V)(K)$ on a line
does not depend on the chosen generator). -/
theorem isoChar_smul (he : IsIsoVec Q₀ e) (hc : c ≠ 0) (g : SOAdele Q₀) :
    isoChar hQ (isIsoVec_smul he hc) g = isoChar hQ he g := by
  apply Units.ext
  rw [isoChar_val, isoChar_val]
  refine Prod.ext (Prod.ext (funext fun w => ?_) (funext fun w => ?_)) ?_
  · change eigVal _ (c • e) ((ArchSO.incl _ (g.1.1 w) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      eigVal _ e ((ArchSO.incl _ (g.1.1 w) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
    exact eigVal_smul_vec _ hc _
  · change eigVal _ (c • e) (ArchSOC.mat _ (g.1.2 w)) = eigVal _ e (ArchSOC.mat _ (g.1.2 w))
    exact eigVal_smul_vec _ hc _
  · ext v : 1
    change isoCharV hQ (isIsoVec_smul he hc) v (finComp g.2 v) = isoCharV hQ he v (finComp g.2 v)
    exact eigVal_smul_vec _ hc _

variable (Q₀)

/-- **The norm-one subgroup does not depend on the scaling of $e$.** -/
theorem SOAdeleOne_smul (he : IsIsoVec Q₀ e) (hc : c ≠ 0) :
    SOAdeleOne Q₀ hQ (isIsoVec_smul he hc) = SOAdeleOne Q₀ hQ he := by
  ext g
  simp only [SOAdeleOne, Subgroup.mem_comap, isoChar_smul hQ he hc]

/-- **The log-norm shells do not depend on the scaling of $e$.** -/
theorem isoShellIco_smul (he : IsIsoVec Q₀ e) (hc : c ≠ 0) (α β : ℝ) :
    isoShellIco Q₀ hQ (isIsoVec_smul he hc) α β = isoShellIco Q₀ hQ he α β := by
  ext g
  simp only [isoShellIco, Set.mem_preimage, isoChar_smul hQ he hc]

/-- **$\tau$ does not depend on the scaling of $e$.** -/
theorem tauIso_smul (he : IsIsoVec Q₀ e) (hc : c ≠ 0) :
    tauIso Q₀ hQ (isIsoVec_smul he hc) = tauIso Q₀ hQ he := by
  unfold tauIso isoShell
  rw [isoShellIco_smul Q₀ hQ he hc]

end Scaling

/-! ### The other isotropic line -/

section OtherLine

variable {Q₀ : QuadForm (𝓞 F) 2}

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- **Eigenvalues on the two isotropic lines are inverse:** let $K$ be a field of characteristic $0$ with an embedding
$\iota : F\to K$, and $e, e'$ isotropic vectors spanning different lines ($e_0e'_1 - e_1e'_0\ne0$). If
$M^{\mathsf T}HM = H$ and $\det M = 1$ ($H$ the Hessian of $Q\otimes K$), then $\chi_{e'}(M)\chi_e(M) = 1$.
*Proof.* The Gram identity gives $-B(e,e')^2 = \det H\,\det(e,e')^2\ne0$, so $B(e,e')\ne0$; $M$ preserves $B$ and
$B(Me,Me') = \chi_e(M)\chi_{e'}(M)B(e,e')$. -/
theorem eigVal_mul_other_line {K : Type*} [Field K] [CharZero K] (ι : F →+* K) (hQ : Q₀.Nondegenerate)
    {e e' : Fin 2 → F} (he : IsIsoVec Q₀ e) (he' : IsIsoVec Q₀ e') (hdet : e 0 * e' 1 - e 1 * e' 0 ≠ 0)
    {M : Matrix (Fin 2) (Fin 2) K} (hM : Mᵀ * (QF).hessian.map ι * M = (QF).hessian.map ι) (hM1 : M.det = 1) :
    eigVal ι e' M * eigVal ι e M = 1 := by
  have h1 := mulVec_eq_eigVal_smul ι hQ he hM hM1
  have h2 := mulVec_eq_eigVal_smul ι hQ he' hM hM1
  have hs := hessian_map_symm (Q₀ := Q₀) ι
  have hB : ∀ x y : Fin 2 → K, (M *ᵥ x) ⬝ᵥ ((QF).hessian.map ι *ᵥ (M *ᵥ y)) =
      x ⬝ᵥ ((QF).hessian.map ι *ᵥ y) := fun x y => by
    have h00 := congrFun (congrFun hM 0) 0
    have h01 := congrFun (congrFun hM 0) 1
    have h10 := congrFun (congrFun hM 1) 0
    have h11 := congrFun (congrFun hM 1) 1
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two] at h00 h01 h10 h11
    simp only [dotProduct, mulVec, Fin.sum_univ_two]
    linear_combination x 0 * y 0 * h00 + x 0 * y 1 * h01 + x 1 * y 0 * h10 + x 1 * y 1 * h11
  have hBxy := hB (ι ∘ e) (ι ∘ e')
  rw [h1, h2, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at hBxy
  -- B(e, e') ≠ 0
  have hg := gram_identity_two _ hs (ι ∘ e) (ι ∘ e')
  rw [iso_dotProduct_hessian ι he, iso_dotProduct_hessian ι he'] at hg
  have hd' : ι (e 0) * ι (e' 1) - ι (e 1) * ι (e' 0) ≠ 0 := by
    rw [← map_mul, ← map_mul, ← map_sub]
    exact (map_ne_zero ι).mpr hdet
  have hBne : (ι ∘ e) ⬝ᵥ ((QF).hessian.map ι *ᵥ (ι ∘ e')) ≠ 0 := by
    intro h0
    rw [h0] at hg
    have : ((QF).hessian.map ι).det * (ι (e 0) * ι (e' 1) - ι (e 1) * ι (e' 0)) ^ 2 = 0 := by
      have := hg; simp only [Function.comp_apply] at this; linear_combination -this
    rcases mul_eq_zero.mp this with h | h
    · exact det_hessian_map_ne_zero ι hQ h
    · exact hd' (pow_eq_zero_iff two_ne_zero |>.mp h)
  have : (eigVal ι e' M * eigVal ι e M - 1) * ((ι ∘ e) ⬝ᵥ ((QF).hessian.map ι *ᵥ (ι ∘ e'))) = 0 := by
    linear_combination hBxy
  have := (mul_eq_zero.mp this).resolve_right hBne
  linear_combination this

variable (hQ : Q₀.Nondegenerate) {e e' : Fin 2 → F} (he : IsIsoVec Q₀ e) (he' : IsIsoVec Q₀ e')
  (hdet : e 0 * e' 1 - e 1 * e' 0 ≠ 0)

include hdet in
/-- **The other isotropic line gives the inverse character:** if $e, e'$ are isotropic vectors spanning different lines
($e_0e'_1 - e_1e'_0\ne0$), then $\chi_{e'} = \chi_e^{-1}$ on $SO(V)(\mathbb A)$ (the isomorphism $SO(V)\cong\mathbb G_m$ is
determined by the choice of line up to inversion). -/
theorem isoChar_other_line (g : SOAdele Q₀) : isoChar hQ he' g = (isoChar hQ he g)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  apply Units.ext
  rw [Units.val_mul, isoChar_val, isoChar_val, Units.val_one]
  refine Prod.ext (Prod.ext (funext fun w => ?_) (funext fun w => ?_)) ?_
  · exact eigVal_mul_other_line _ hQ he he' hdet (hessian_of_mem_soReal w (g.1.1 w)).1
      (hessian_of_mem_soReal w (g.1.1 w)).2
  · exact eigVal_mul_other_line _ hQ he he' hdet (hessian_of_mem_soC w (g.1.2 w)).1
      (hessian_of_mem_soC w (g.1.2 w)).2
  · ext v : 1
    exact eigVal_mul_other_line _ hQ he he' hdet (hessian_of_mem_soSub v (finComp g.2 v)).1
      (hessian_of_mem_soSub v (finComp g.2 v)).2

include hdet in
/-- **The norm-one subgroup does not depend on the isotropic line:** $|\chi_{e'}| = |\chi_e|^{-1}$, so
$SO(V)(\mathbb A)^1$ is the same. -/
theorem SOAdeleOne_other_line : SOAdeleOne Q₀ hQ he' = SOAdeleOne Q₀ hQ he := by
  ext g
  simp only [SOAdeleOne, Subgroup.mem_comap, mem_ideleOne, isoChar_other_line hQ he he' hdet, ideleNorm_inv,
    inv_eq_one]

include hdet in
/-- **The shells for the other line are reflected:** $\{\alpha\le\log\|\chi_{e'}\|_{\mathbb A}<\beta\}
= \{-\beta<\log\|\chi_e\|_{\mathbb A}\le-\alpha\}$. -/
theorem isoShellIco_other_line (α β : ℝ) :
    isoShellIco Q₀ hQ he' α β = {g | -β < Real.log (ideleNorm F (isoChar hQ he g)) ∧
      Real.log (ideleNorm F (isoChar hQ he g)) ≤ -α} := by
  ext g
  simp only [isoShellIco, Set.mem_preimage, Set.mem_Ico, Set.mem_ofPred_eq, isoChar_other_line hQ he he' hdet,
    ideleNorm_inv, Real.log_inv]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

end OtherLine

/-! ### The hyperbolic plane -/

/-- **For the hyperbolic plane the two isotropic lines $F(1,0)$ and $F(0,1)$ give inverse characters.** -/
theorem isoChar_hyp_other (g : SOAdele (hypForm F)) :
    isoChar nondegenerate_hypForm (isIsoVec_hypE' (F := F)) g =
      (isoChar nondegenerate_hypForm (isIsoVec_hypE (F := F)) g)⁻¹ :=
  isoChar_other_line nondegenerate_hypForm isIsoVec_hypE isIsoVec_hypE' (by simp [hypE]) g

end QuadFormsKB.Tamagawa.Measure.Weil
