import QuadFormsKB.Tamagawa.Measure.Weil.BinaryIsoMain
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryIsoArch
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryIsoReduce

/-!
# τ(SO(V)) = 1 for every isotropic binary form over every number field

**Layer:** a number field $F$; $Q_0$ a nondegenerate binary form over $\mathcal O_F$ with $Q_0\otimes F$ isotropic.

**Proves**
* `map_tamIdeles_hypEquiv`: for the hyperbolic plane $H = x_0x_1$, $\Phi = $ `hypEquiv F` : $\mathbb A_F^\times\cong SO(H)(\mathbb A)$
  carries `tamIdeles F` to `muTam H lamV` (archimedean comparison `map_omegaInf_hypInfEquiv_muArchTamSO`, finite comparison
  `map_muFinUnits_hypFinEquiv`, the two constants $|d_F|^{\pm1/2}$ cancel);
* `isoComparison_hyp`: the comparison $SO(H)\cong\mathbb G_m$ holds for $(H, (1,0))$;
* transport of the comparison: `isoComparison_simForm_iff` (similarity, isotropic $Q_0$), `isoComparison_smul_iff`
  (scaling the isotropic vector), `isoComparison_of_eq` (equal forms and vectors);
* **`isoComparison_of_isotropic`** (every isotropic $(Q_0, e)$, through `exists_hyp_similarity`);
* **`tauOne_binary_isotropic_uncond`**: $\tau(SO(V)) = 1$; `covolume_isoShellIco` (every shell $\{\alpha\le\log|\chi_e|<\beta\}$
  has volume $\beta-\alpha$); `map_muTamIso_isoChar` ($(\chi_e)_*\mu^{\mathrm{iso}}_{\mathrm{Tam}} = \rho_F^{-1}$`tamIdeles F`);
  `tauIso_eq_muIdeleClass`.
-/

open MeasureTheory Measure Set Matrix Filter
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa QuadFormsKB.QuadForm

variable {F : Type} [Field F] [NumberField F]

/-! ### The hyperbolic plane -/

/-- **$\Phi_*$`tamIdeles` $=$ `muTam H lamV`** for the hyperbolic plane. -/
theorem map_tamIdeles_hypEquiv :
    (tamIdeles F).map (hypEquiv F) = muTam (hypForm F) nondegenerate_hypForm lamV := by
  have h1 : Measurable (hypInfEquiv F) := (hypInfEquiv F).continuous.measurable
  have h2 : Measurable (hypFinEquiv F) := (hypFinEquiv F).continuous.measurable
  have hf : ⇑(hypEquiv F) = Prod.map (hypInfEquiv F) (hypFinEquiv F) ∘ (idelesEquiv F) := rfl
  have hm : Measurable (hypEquiv F : (Adeles F)ˣ → SOAdele (hypForm F)) := (hypEquiv F).continuous.measurable
  have hm' : Measurable ((idelesEquiv F).symm : ((mixedEmbedding.mixedSpace F)ˣ × (FiniteAdeleRing (𝓞 F) F)ˣ) →
      (Adeles F)ˣ) := (idelesEquiv F).symm.continuous.measurable
  rw [tamIdeles, Measure.map_map hm hm', hf,
    Function.comp_assoc, show ⇑(idelesEquiv F) ∘ ⇑(idelesEquiv F).symm = id from
      funext (idelesEquiv F).apply_symm_apply, Function.comp_id,
    map_prodMap_prod h1 h2 _ _ _ _ map_omegaInf_hypInfEquiv_muArchTamSO map_muFinUnits_hypFinEquiv,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (show 0 < ohatVol F from inv_pos.mpr (Real.sqrt_pos.mpr
      (abs_pos.mpr (by exact_mod_cast discr_ne_zero F))))).ne' ENNReal.ofReal_ne_top, one_smul, muTam]

theorem isoChar_hyp_eq_symm :
    ⇑(isoChar nondegenerate_hypForm (isIsoVec_hypE (F := F))) = ⇑(hypEquiv F).symm := by
  funext g
  apply (hypEquiv F).injective
  rw [hypEquiv_isoChar, ContinuousMulEquiv.apply_symm_apply]

/-- **The comparison for the hyperbolic plane** and $e = (1,0)$. -/
theorem isoComparison_hyp : IsoComparison (nondegenerate_hypForm (F := F)) (isIsoVec_hypE (F := F)) where
  bijective := by rw [isoChar_hyp_eq_symm]; exact (hypEquiv F).symm.bijective
  measurable := by rw [isoChar_hyp_eq_symm]; exact (hypEquiv F).symm.continuous.measurable
  measurable_symm := by
    have : ⇑(MulEquiv.ofBijective (isoChar nondegenerate_hypForm (isIsoVec_hypE (F := F)))
        (by rw [isoChar_hyp_eq_symm]; exact (hypEquiv F).symm.bijective)).symm = ⇑(hypEquiv F) := by
      funext t
      set φ := MulEquiv.ofBijective (isoChar nondegenerate_hypForm (isIsoVec_hypE (F := F)))
        (by rw [isoChar_hyp_eq_symm]; exact (hypEquiv F).symm.bijective)
      apply φ.injective
      rw [MulEquiv.apply_symm_apply, MulEquiv.ofBijective_apply, isoChar_hypEquiv]
    rw [this]; exact (hypEquiv F).continuous.measurable
  gamma := by
    rw [← map_diagUnitsSub_hypEquiv, Subgroup.map_map]
    have : (isoChar nondegenerate_hypForm (isIsoVec_hypE (F := F))).comp (hypEquiv F).toMulEquiv.toMonoidHom =
        MonoidHom.id _ := MonoidHom.ext fun t => isoChar_hypEquiv t
    rw [this, Subgroup.map_id]
  map_muTam := by
    have hm : Measurable (hypEquiv F : (Adeles F)ˣ → SOAdele (hypForm F)) := (hypEquiv F).continuous.measurable
    have hi : Measurable (isoChar nondegenerate_hypForm (isIsoVec_hypE (F := F))) := by
      rw [isoChar_hyp_eq_symm]; exact (hypEquiv F).symm.continuous.measurable
    rw [← map_tamIdeles_hypEquiv, Measure.map_map hi hm]
    convert Measure.map_id
    funext t
    exact isoChar_hypEquiv t

/-! ### Transport of the comparison -/

section Transport

theorem ofBijective_symm_congr {G H : Type*} [Group G] [Group H] {χ χ' : G →* H} (h : χ = χ')
    (hb : Function.Bijective χ) (hb' : Function.Bijective χ') :
    ⇑(MulEquiv.ofBijective χ hb).symm = ⇑(MulEquiv.ofBijective χ' hb').symm := by
  subst h; rfl

/-- The comparison only depends on the character $\chi_e$. -/
theorem isoComparison_of_isoChar_eq {Q₀ : QuadForm (𝓞 F) 2} {hQ : Q₀.Nondegenerate} {e e' : Fin 2 → F}
    {he : IsIsoVec Q₀ e} {he' : IsIsoVec Q₀ e'} (heq : isoChar hQ he = isoChar hQ he')
    (h : IsoComparison hQ he) : IsoComparison hQ he' where
  bijective := heq ▸ h.bijective
  measurable := heq ▸ h.measurable
  measurable_symm := by
    rw [← ofBijective_symm_congr heq h.bijective]; exact h.measurable_symm
  gamma := heq ▸ h.gamma
  map_muTam := heq ▸ h.map_muTam

/-- **Scaling the isotropic vector** does not change the comparison. -/
theorem isoComparison_smul_iff {Q₀ : QuadForm (𝓞 F) 2} {hQ : Q₀.Nondegenerate} {e : Fin 2 → F}
    {he : IsIsoVec Q₀ e} {c : F} (hc : c ≠ 0) : IsoComparison hQ (isIsoVec_smul he hc) ↔ IsoComparison hQ he := by
  have heq : isoChar hQ (isIsoVec_smul he hc) = isoChar hQ he := MonoidHom.ext (isoChar_smul hQ he hc)
  exact ⟨isoComparison_of_isoChar_eq heq, isoComparison_of_isoChar_eq heq.symm⟩

/-- **Equal forms and vectors** have the same comparison. -/
theorem isoComparison_of_eq {Q Q' : QuadForm (𝓞 F) 2} {hQ : Q.Nondegenerate} {hQ' : Q'.Nondegenerate}
    {e e' : Fin 2 → F} {he : IsIsoVec Q e} {he' : IsIsoVec Q' e'} (h1 : Q = Q') (h2 : e = e')
    (h : IsoComparison hQ he) : IsoComparison hQ' he' := by
  subst h1; subst h2; exact h

variable {Q₀ : QuadForm (𝓞 F) 2} (hQ : Q₀.Nondegenerate) {e : Fin 2 → F} (he : IsIsoVec Q₀ e) {c : 𝓞 F}
  {G : Matrix (Fin 2) (Fin 2) (𝓞 F)} (hc : c ≠ 0) (hG : G.det ≠ 0)

theorem measurable_simConjAdele : Measurable (simConjAdele (Q₀ := Q₀) hc hG) :=
  (simConjInf hc hG).continuous.measurable.prodMap (simConjFin hc hG).continuous.measurable

theorem measurable_simConjAdele_symm : Measurable (simConjAdele (Q₀ := Q₀) hc hG).symm :=
  (simConjInf hc hG).symm.continuous.measurable.prodMap (simConjFin hc hG).symm.continuous.measurable

include hQ he in
/-- **The comparison is invariant under similarity** $Q_0\mapsto c\,(Q_0\circ G)$, $e\mapsto G^{-1}e$. -/
theorem isoComparison_simForm_iff :
    IsoComparison (nondegenerate_simForm hQ hc hG) (isIsoVec_simForm he hc hG) ↔ IsoComparison hQ he := by
  have hsq : IsSquare (algebraMap (𝓞 F) F (-Q₀.hessian.det)) := (isotropicF_iff_isSquare Q₀).mp ⟨e, he⟩
  set φ := simConjAdele (Q₀ := Q₀) hc hG
  set χ₀ := isoChar hQ he
  set χ₁ := isoChar (nondegenerate_simForm hQ hc hG) (isIsoVec_simForm he hc hG)
  have hcomp : ∀ g, χ₁ (φ g) = χ₀ g := isoChar_simConjAdele hQ he hc hG
  have hφm := measurable_simConjAdele (Q₀ := Q₀) hc hG
  have hφm' := measurable_simConjAdele_symm (Q₀ := Q₀) hc hG
  have hΓ := map_GammaSOAdele_simConjAdele (Q₀ := Q₀) hc hG
  have hμ := map_muTam_simConjAdele_lamV hQ hc hG hsq
  have hc0 : ⇑χ₀ = ⇑χ₁ ∘ ⇑φ := funext fun g => (hcomp g).symm
  have hc1 : ⇑χ₁ = ⇑χ₀ ∘ ⇑φ.symm := funext fun g => by
    rw [Function.comp_apply, ← hcomp, MulEquiv.apply_symm_apply]
  constructor
  · intro h
    have hb : Function.Bijective χ₀ := by rw [hc0]; exact h.bijective.comp φ.bijective
    refine ⟨hb, by rw [hc0]; exact h.measurable.comp hφm, ?_, ?_, ?_⟩
    · have : ⇑(MulEquiv.ofBijective χ₀ hb).symm = ⇑φ.symm ∘ ⇑(MulEquiv.ofBijective χ₁ h.bijective).symm := by
        funext t
        apply (MulEquiv.ofBijective χ₀ hb).injective
        rw [MulEquiv.apply_symm_apply, Function.comp_apply, MulEquiv.ofBijective_apply, ← hcomp,
          MulEquiv.apply_symm_apply, ← MulEquiv.ofBijective_apply χ₁ h.bijective, MulEquiv.apply_symm_apply]
      rw [this]; exact hφm'.comp h.measurable_symm
    · rw [← h.gamma, ← hΓ, Subgroup.map_map]
      congr 1
      exact MonoidHom.ext fun g => (hcomp g).symm
    · rw [← h.map_muTam, ← hμ, Measure.map_map h.measurable hφm, ← hc0]
  · intro h
    have hb : Function.Bijective χ₁ := by rw [hc1]; exact h.bijective.comp φ.symm.bijective
    refine ⟨hb, by rw [hc1]; exact h.measurable.comp hφm', ?_, ?_, ?_⟩
    · have : ⇑(MulEquiv.ofBijective χ₁ hb).symm = ⇑φ ∘ ⇑(MulEquiv.ofBijective χ₀ h.bijective).symm := by
        funext t
        apply (MulEquiv.ofBijective χ₁ hb).injective
        rw [MulEquiv.apply_symm_apply, Function.comp_apply, MulEquiv.ofBijective_apply, hcomp,
          ← MulEquiv.ofBijective_apply χ₀ h.bijective, MulEquiv.apply_symm_apply]
      rw [this]; exact hφm.comp h.measurable_symm
    · rw [← h.gamma, ← hΓ, Subgroup.map_map]
      congr 1
      exact MonoidHom.ext fun g => hcomp g
    · have hχ₁ : Measurable χ₁ := by rw [hc1]; exact h.measurable.comp hφm'
      calc (muTam (simForm Q₀ c G) (nondegenerate_simForm hQ hc hG) lamV).map χ₁
          = ((muTam Q₀ hQ lamV).map φ).map χ₁ := by rw [hμ]
        _ = (muTam Q₀ hQ lamV).map (χ₁ ∘ φ) := Measure.map_map hχ₁ hφm
        _ = (muTam Q₀ hQ lamV).map χ₀ := by rw [← hc0]
        _ = tamIdeles F := h.map_muTam

end Transport

/-! ### Every isotropic binary form -/

section Main

theorem det_one_ne_zero' : (1 : Matrix (Fin 2) (Fin 2) (𝓞 F)).det ≠ 0 := by simp

theorem glF_one_inv_mulVec (h : (1 : Matrix (Fin 2) (Fin 2) (𝓞 F)).det ≠ 0) (x : Fin 2 → F) :
    (((LatChange.glF (1 : Matrix (Fin 2) (Fin 2) (𝓞 F)) h)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ x = x := by
  have h1 : LatChange.glF (1 : Matrix (Fin 2) (Fin 2) (𝓞 F)) h = 1 := by
    apply Units.ext
    change (1 : Matrix (Fin 2) (Fin 2) (𝓞 F)).map (algebraMap (𝓞 F) F) = 1
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [h1, inv_one, Units.val_one, one_mulVec]

/-- **The comparison $SO(V)\cong\mathbb G_m$ holds for every isotropic binary form** over every number field: $\chi_e$
is a measurable group isomorphism $SO(V)(\mathbb A)\cong\mathbb A_F^\times$ (measurable inverse) carrying $SO(V)(F)$ onto
$F^\times$ and Weil's measure `muTam Q₀ hQ lamV` onto `tamIdeles F`. *Proof:* $Q_0$ is similar to a multiple of the
hyperbolic plane compatibly with the isotropic line (`exists_hyp_similarity`), the comparison holds for the hyperbolic
plane (`isoComparison_hyp`), and it is invariant under similarity, scaling of $e$ and equality of forms. -/
theorem isoComparison_of_isotropic {Q₀ : QuadForm (𝓞 F) 2} (hQ : Q₀.Nondegenerate) {e : Fin 2 → F}
    (he : IsIsoVec Q₀ e) : IsoComparison hQ he := by
  obtain ⟨d, hd, G, hG, b, hb, κ, hκ, hform, hvec⟩ := exists_hyp_similarity hQ he
  have hG1 := det_one_ne_zero' (F := F)
  have h1 := (isoComparison_simForm_iff nondegenerate_hypForm (isIsoVec_hypE (F := F)) hb hG1).mpr
    isoComparison_hyp
  have he₁ : IsIsoVec (simForm (hypForm F) b 1) (hypE F) :=
    glF_one_inv_mulVec hG1 (hypE F) ▸ isIsoVec_simForm (isIsoVec_hypE (F := F)) hb hG1
  have h2 : IsoComparison (nondegenerate_simForm nondegenerate_hypForm hb hG1) he₁ :=
    isoComparison_of_eq rfl (glF_one_inv_mulVec hG1 (hypE F)) h1
  have h3 := (isoComparison_smul_iff hκ).mpr h2
  have hde := isIsoVec_smul he hd
  have h4 : IsoComparison (nondegenerate_simForm hQ one_ne_zero hG) (isIsoVec_simForm hde one_ne_zero hG) :=
    isoComparison_of_eq hform.symm hvec.symm h3
  exact (isoComparison_smul_iff hd).mp ((isoComparison_simForm_iff hQ hde one_ne_zero hG).mp h4)

variable {Q₀ : QuadForm (𝓞 F) 2} (hQ : Q₀.Nondegenerate) {e : Fin 2 → F} (he : IsIsoVec Q₀ e)

/-- **$SO(V)\cong\mathbb G_m$ on adelic points**: $\chi_e$ is bijective. -/
theorem isoChar_bijective : Function.Bijective (isoChar hQ he) := (isoComparison_of_isotropic hQ he).bijective

/-- **$\chi_e(SO(V)(F)) = F^\times$.** -/
theorem map_GammaSOAdele_isoChar : (GammaSOAdele Q₀).map (isoChar hQ he) = diagUnitsSub F :=
  (isoComparison_of_isotropic hQ he).gamma

/-- **The measure comparison**: $(\chi_e)_*\mu^{\mathrm{iso}}_{\mathrm{Tam}} = \rho_F^{-1}\,$`tamIdeles F`, i.e. Weil's Tamagawa
measure of $SO(V)$ (convergence factors $\lambda_v = L_v(1,\mathbf 1)^{-1}$, global factor $\rho_F^{-1}$) is carried by
$SO(V)\cong\mathbb G_m$ to Weil's Tamagawa measure $\rho_F^{-1}\prod_v\lambda_v^{-1}\omega_v$ of $\mathbb G_m$. -/
@[kb "weil1982" "§2.3, Thm 2.3.1 (Tamagawa measures of isomorphic groups correspond) [unverified]"]
theorem map_muTamIso_isoChar :
    (muTamIso Q₀ hQ).map (isoChar hQ he) = ENNReal.ofReal (dedekindZeta_residue F)⁻¹ • tamIdeles F :=
  map_muTamIso_of_comparison (isoComparison_of_isotropic hQ he)

/-- **Every shell has the expected volume** (Weil's $\mu = \mu^1\times dt/t$ on $SO(V)(\mathbb A)$):
$\operatorname{covol}(SO(V)(F), \mu^{\mathrm{iso}}_{\mathrm{Tam}}|_{\{\alpha\le\log|\chi_e|<\beta\}}) = \beta-\alpha$. -/
@[kb "weil1982" "§3.2, proof of Thm 3.2.1, p. 43; §2.4 [unverified]"]
theorem covolume_isoShellIco (α β : ℝ) :
    covolume (GammaSOAdele Q₀) (SOAdele Q₀) ((muTamIso Q₀ hQ).restrict (isoShellIco Q₀ hQ he α β)) =
      ENNReal.ofReal (β - α) :=
  covolume_isoShellIco_of_comparison (isoComparison_of_isotropic hQ he) α β

/-- **τ is Weil's $\operatorname{vol}(\mathbb A_F^1/F^\times)$ for $\mathbb G_m$** (under $SO(V)\cong\mathbb G_m$):
$\tau = \rho_F^{-1}\cdot\mu^1(F^\times\backslash\mathbb A_F^1)$, where $\mu^1$ = `muIdeleClass F` is the quotient of `tamIdeles F` by
$dt/t$ and the factor $\rho_F^{-1}$ is the global factor of Weil's Tamagawa measure. -/
@[kb "weil1982" "§2.4 [unverified] (τ(G) = vol(G_𝔸¹/G_k)); §3.1 (τ(G_m) = 1) [unverified]"]
theorem tauIso_eq_muIdeleClass :
    tauIso Q₀ hQ he = ENNReal.ofReal (dedekindZeta_residue F)⁻¹ * muIdeleClass F univ := by
  rw [tauIso_of_comparison (isoComparison_of_isotropic hQ he), muIdeleClass_univ_eq_residue,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (dedekindZeta_residue_pos F).le),
    inv_mul_cancel₀ (dedekindZeta_residue_pos F).ne', ENNReal.ofReal_one]

variable (F) in
/-- **Target statement over $F$**: $\tau(SO(V)) = 1$ for every nondegenerate isotropic binary form over $\mathcal O_F$ and every
isotropic vector. -/
@[kb "weil1982" "§2.4, §3.1 [unverified] (τ(G_m) = 1); ono1963 [unverified]"]
def TauOneIsotropicAll : Prop :=
  ∀ (Q₀ : QuadForm (𝓞 F) 2) (hQ : Q₀.Nondegenerate), IsotropicF Q₀ → TauOneIsotropic Q₀ hQ

variable (F) in
/-- **Weil's/Ono's τ(SO(V)) = 1 for isotropic binary $V$, over every number field** (unconditional): for every
nondegenerate binary form $Q_0$ over $\mathcal O_F$ with $Q_0\otimes F$ isotropic and every isotropic vector $e$,
$$\tau(SO(V)) = \operatorname{vol}\bigl(SO(V)(F)\backslash SO(V)(\mathbb A)^1\bigr) = 1$$
for Weil's Tamagawa measure with the convergence factors $\lambda_v = 1-N(v)^{-1}$ of $\mathbb G_m$ and the global factor
$\rho_F^{-1}$ (`tauIso`, `muTamIso`). The value does not depend on the isotropic line (`isoChar_other_line`: the two lines
give inverse characters with the same kernel) nor on the vector on it (`tauIso_smul`). -/
@[kb "weil1982" "§2.4, §3.1 [unverified] (τ(G_m) = 1); ono1963 [unverified] (τ of tori)"]
theorem tauOne_binary_isotropic_uncond : TauOneIsotropicAll F := fun _ hQ _ _ he =>
  tauIso_of_comparison (isoComparison_of_isotropic hQ he)

/-- The isotropic case is not vacuous: over every number field there are nondegenerate isotropic binary forms (the
hyperbolic plane $x_0x_1$), and $\tau = 1$ for it. -/
theorem tauIso_hyp : tauIso (hypForm F) nondegenerate_hypForm (isIsoVec_hypE (F := F)) = 1 :=
  tauOne_binary_isotropic_uncond F _ _ isotropicF_hypForm _ _

end Main

end QuadFormsKB.Tamagawa.Measure.Weil
