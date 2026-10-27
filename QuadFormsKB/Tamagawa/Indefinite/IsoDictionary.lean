/-
# The classical–adelic dictionary for norm-one stabilizers

**Layer:** number fields, adeles. Setting of `IsoMeasures.lean` (isotropic rank-2 complement, $H = SO(Q'')$ commutative,
$K = SO(\hat L)$, classes $M_i$ with representatives $b_i$ = `dcRep`, $\Gamma_i$ = `unitGroup`). For an orbit $O$ of
integral finite-adelic frames (`FinOrbit`) with representative $b_O$ let $U_O = \iota_f^{-1}(b_O^{-1}Kb_O)$ (`isoU`).

**Proves** `tsum_repMeasureIso`:
$$\sum_i\rho^1(M_i, T_0) = \lambda\sum_O\ \sum_{c\in H(F)\backslash H(\mathbb A_f)/U_O}
  \operatorname{covol}\bigl(\Gamma_{U_O}\backslash H_\infty,\ \mu_\infty|_{\text{shell}}\bigr)\qquad(\texttt{isoCov}),$$
$\lambda$ = `isoFrameLam`. *Proof.* A representation $X = \gamma\Xi$ ($\gamma\in SO(V)(F)$, Witt) of $T_0$ by $M_i$ gives the
integral frame $b = b_i^{-1}\gamma_f$, its orbit $O$ (`isoPi`) and, writing $b = k\,b_O\,\iota_f(h)$, the double coset of $h$
(`isoPsi`); this is a bijection from the $\Gamma_i$-orbits over $O$ onto $H(F)\backslash H(\mathbb A_f)/U_O$
(`isoPsi_bijective`), and conjugation by $\gamma_\infty$ carries $\Gamma_{U_b}$ onto the stabilizer $\Gamma_{i,X}$ and the shell
measure onto `isoStabMeasure X` (`covolume_isoStabMeasure`), with $U_b = U_O$ (`orbitStab_eq_of_rel`).
-/
import QuadFormsKB.Tamagawa.Indefinite.IsoMeasures

open MeasureTheory Set Matrix MulAction
open scoped ENNReal Pointwise

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames

variable {F : Type} [Field F] [NumberField F]

variable {r : ℕ} (Q₀ : QuadForm (𝓞 F) (r + 2)) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r)
  (hT : T₀.Nondegenerate) (hiso : IsSquare (algebraMap (𝓞 F) F (deltaForms Q₀ T₀))) (Ξ : RatFrame Q₀ T₀)

local notation "𝔇" => isoTower Q₀ hQ T₀ hT Ξ
local notation "𝔢" => isIsoVec_isoVec Q₀ hQ T₀ hT hiso Ξ

theorem prodMap_fst' {A B C D : Type*} [Monoid A] [Monoid B] [Monoid C] [Monoid D] (f : A →* C) (g : B →* D)
    (x : A × B) : (MonoidHom.prodMap f g x).1 = f x.1 := rfl

theorem prodMap_snd' {A B C D : Type*} [Monoid A] [Monoid B] [Monoid C] [Monoid D] (f : A →* C) (g : B →* D)
    (x : A × B) : (MonoidHom.prodMap f g x).2 = g x.2 := rfl

/-! ### Definitions -/

/-- The norm-one covolume attached to a subgroup $U\le SO(Q'')(\mathbb A_f)$:
$\operatorname{covol}(\Gamma_U\backslash SO(Q'')(F_\infty), \mu_\infty|_{\text{shell}})$, $\Gamma_U = \{\gamma_\infty : \gamma\in SO(Q'')(F),
\gamma_f\in U\}$. -/
def isoCov (U : Subgroup (SOAf (𝔇).Q'')) : ℝ≥0∞ :=
  covolume (levelGroup (GammaSOAdele (𝔇).Q'') U 1) (GInfSO (𝔇).Q'')
    ((muArchTamSO (𝔇).Q'' (𝔇).hQ'').restrict (isoShellInf (𝔇).Q'' (𝔇).hQ'' 𝔢))

/-- The orbit stabilizer $U_O = \iota_f^{-1}(b_O^{-1}Kb_O)$ of an orbit of integral frames. -/
def isoU (O : FinOrbit Q₀ T₀ Ξ) : Subgroup (SOAf (𝔇).Q'') :=
  orbitStab (𝔇).ιFin (KSO Q₀) (finOrbitRep Q₀ T₀ Ξ O)

/-! ### Commutativity and the orbit stabilizers -/

include hiso in
theorem comap_conj_isoTower (U : Subgroup (SOAf (𝔇).Q'')) (a : SOAf (𝔇).Q'') :
    U.comap (MulAut.conj a).toMonoidHom = U := by
  ext h
  simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [mul_comm_SOAf_iso (𝔇).Q'' (𝔇).hQ'' 𝔢 a h, mul_assoc, mul_inv_cancel, mul_one]

include hiso in
/-- **Equivalent integral frames have the same orbit stabilizer** ($H$ is commutative). -/
theorem orbitStab_eq_of_rel (b b' : {b : SOAf Q₀ // b • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + 2) r})
    (h : (finOrbitSetoid Q₀ T₀ Ξ).r b b') :
    orbitStab (𝔇).ιFin (KSO Q₀) b'.1 = orbitStab (𝔇).ιFin (KSO Q₀) b.1 := by
  obtain ⟨k, hk, y, hy, hky⟩ := Set.mem_smul.1 h
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have hfix : ((k * b.1)⁻¹ * b'.1) • ratFT Q₀ T₀ Ξ = ratFT Q₀ T₀ Ξ := by
    rw [mul_smul, ← hky, ← mul_smul k, inv_smul_smul]
  obtain ⟨a, ha⟩ := (𝔇).stab_ιFin Q₀ hQ T₀ Ξ _ hfix
  have hb' : b'.1 = k * b.1 * (𝔇).ιFin a := by rw [ha]; group
  rw [hb', orbitStab_mul_mul _ _ _ _ hk, comap_conj_isoTower Q₀ hQ T₀ hT hiso Ξ]

/-! ### The classical stabilizers -/

include hiso in
/-- $\iota(\eta)$ fixes $\Xi$ as a rational frame, for $\eta\in SO(Q'')(F)$. -/
theorem iotaGamma_smul_ratFrame (η : SOAdele (𝔇).Q'') (hη : η ∈ GammaSOAdele (𝔇).Q'') :
    (⟨MonoidHom.prodMap (𝔇).ιInf (𝔇).ιFin η, (𝔇).gamma_mem η hη⟩ : GammaSOAdele Q₀) • Ξ = Ξ := by
  apply ratFrameA_injective Q₀ T₀
  rw [ratFrameA_smul]
  exact (𝔇).fix η

include hiso in
/-- **The stabilizer of $X = \gamma\,\Xi$ in $\Gamma_i$ is $\gamma_\infty\iota_\infty(\Gamma_{U_b})\gamma_\infty^{-1}$**, $b = b_i^{-1}\gamma_f$
(membership form). -/
theorem conj_mem_unitGroup_iff (i : DC Q₀) (γ : GammaSOAdele Q₀) (h : GInfSO (𝔇).Q'') :
    (γ : SOAdele Q₀).1 * (𝔇).ιInf h * (γ : SOAdele Q₀).1⁻¹ ∈ unitGroup Q₀ i ↔
      h ∈ levelGroup (GammaSOAdele (𝔇).Q'')
        (orbitStab (𝔇).ιFin (KSO Q₀) ((dcRep Q₀ i)⁻¹ * (γ : SOAdele Q₀).2)) 1 := by
  set b := (dcRep Q₀ i)⁻¹ * (γ : SOAdele Q₀).2 with hb
  constructor
  · rintro ⟨δ, ⟨hδΓ, hδK⟩, hδ1⟩
    have hδK' : (dcRep Q₀ i)⁻¹ * δ.2 * dcRep Q₀ i ∈ KSO Q₀ := hδK
    set ε : GammaSOAdele Q₀ := γ⁻¹ * ⟨δ, hδΓ⟩ * γ with hε
    have hε1 : (ε : SOAdele Q₀).1 = (𝔇).ιInf h := by
      have : (δ.1 : GInfSO Q₀) = (γ : SOAdele Q₀).1 * (𝔇).ιInf h * (γ : SOAdele Q₀).1⁻¹ := hδ1
      simp only [hε, Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.fst_inv, this]
      group
    have hεfix : ε • Ξ = Ξ := by
      apply ratAT_injective Q₀ T₀
      rw [ratAT_smul, hε1]
      exact (𝔇).ιInf_smul_ratAT Q₀ hQ T₀ Ξ h
    have hεA : (ε : SOAdele Q₀) • frameA (cols Ξ.1) = frameA (cols Ξ.1) := by
      have := congrArg (ratFrameA Q₀ T₀) hεfix
      rwa [ratFrameA_smul] at this
    obtain ⟨η, hηΓ, hηε⟩ := (𝔇).stabΓ ε ε.2 hεA
    have hη1 : η.1 = h := (𝔇).ιInf_injective Q₀ hQ T₀ Ξ (by
      rw [← hε1, ← hηε]; rfl)
    refine ⟨η, ⟨hηΓ, ?_⟩, hη1⟩
    show (1 : SOAf (𝔇).Q'')⁻¹ * η.2 * 1 ∈ orbitStab (𝔇).ιFin (KSO Q₀) b
    rw [inv_one, one_mul, mul_one, mem_orbitStab']
    have hε2 : (𝔇).ιFin η.2 = (γ : SOAdele Q₀).2⁻¹ * δ.2 * (γ : SOAdele Q₀).2 := by
      have : (𝔇).ιFin η.2 = (ε : SOAdele Q₀).2 := congrArg Prod.snd hηε
      rw [this]
      simp [hε, mul_assoc]
    rw [hε2, hb]
    have e : (dcRep Q₀ i)⁻¹ * (γ : SOAdele Q₀).2 * ((γ : SOAdele Q₀).2⁻¹ * δ.2 * (γ : SOAdele Q₀).2) *
        ((dcRep Q₀ i)⁻¹ * (γ : SOAdele Q₀).2)⁻¹ = (dcRep Q₀ i)⁻¹ * δ.2 * dcRep Q₀ i := by group
    rw [e]; exact hδK'
  · rintro ⟨η, ⟨hηΓ, hηU⟩, hη1⟩
    have hηU' : η.2 ∈ orbitStab (𝔇).ιFin (KSO Q₀) b := by
      have : (1 : SOAf (𝔇).Q'')⁻¹ * η.2 * 1 ∈ orbitStab (𝔇).ιFin (KSO Q₀) b := hηU
      rwa [inv_one, one_mul, mul_one] at this
    rw [mem_orbitStab'] at hηU'
    refine ⟨(γ : SOAdele Q₀) * MonoidHom.prodMap (𝔇).ιInf (𝔇).ιFin η * (γ : SOAdele Q₀)⁻¹,
      ⟨(GammaSOAdele Q₀).mul_mem ((GammaSOAdele Q₀).mul_mem γ.2 ((𝔇).gamma_mem η hηΓ))
        ((GammaSOAdele Q₀).inv_mem γ.2), ?_⟩, ?_⟩
    · show (dcRep Q₀ i)⁻¹ * ((γ : SOAdele Q₀) * MonoidHom.prodMap (𝔇).ιInf (𝔇).ιFin η * (γ : SOAdele Q₀)⁻¹).2 *
        dcRep Q₀ i ∈ KSO Q₀
      have e : (dcRep Q₀ i)⁻¹ * ((γ : SOAdele Q₀) * MonoidHom.prodMap (𝔇).ιInf (𝔇).ιFin η * (γ : SOAdele Q₀)⁻¹).2 *
          dcRep Q₀ i = b * (𝔇).ιFin η.2 * b⁻¹ := by
        simp only [Prod.snd_mul, Prod.snd_inv, prodMap_snd', prodMap_fst', hb]
        group
      rw [e]; exact hηU'
    · show ((γ : SOAdele Q₀) * MonoidHom.prodMap (𝔇).ιInf (𝔇).ιFin η * (γ : SOAdele Q₀)⁻¹).1 = _
      simp only [Prod.fst_mul, Prod.fst_inv, prodMap_snd', prodMap_fst', ← hη1]
      rfl

/-! ### The covolume of a classical stabilizer -/

section Transport

variable {G H : Type*} [Group G] [Group H] [MeasurableSpace G] [MeasurableSpace H] [MeasurableMul G]
  [MeasurableMul H]

/-- A measure invariant under `Λ` is carried by a measurable group isomorphism to a measure invariant under `φ(Λ)`. -/
theorem smulInvariantMeasure_map_of_equiv (φ : G ≃* H) (hφ : Measurable φ) (Λ : Subgroup G) (Λ' : Subgroup H)
    (hΛ : Λ.map φ.toMonoidHom = Λ') (μ : Measure G) [SMulInvariantMeasure Λ G μ] :
    SMulInvariantMeasure Λ' H (μ.map φ) := by
  refine ⟨fun γ A hA => ?_⟩
  have hγ : (γ : H) ∈ Λ.map φ.toMonoidHom := hΛ ▸ γ.2
  obtain ⟨x, hx, hxγ⟩ := hγ
  rw [Measure.map_apply hφ (measurable_const_smul _ hA), Measure.map_apply hφ hA]
  have e : φ ⁻¹' ((fun y => γ • y) ⁻¹' A) = (fun y => (⟨x, hx⟩ : Λ) • y) ⁻¹' (φ ⁻¹' A) := by
    ext y
    simp only [mem_preimage, Subgroup.smul_def, smul_eq_mul, map_mul]
    rw [show φ x = (γ : H) from hxγ]
  rw [e, measure_preimage_smul]

end Transport

include hiso in
/-- **Transport of the stabilizer covolume** to $SO(Q'')(F_\infty)$: for $X = a\,\Xi_\infty$ and a countable subgroup
$\Gamma'\le G_\infty$, the covolume of $\Gamma'\cap H_X$ for `isoStabAt` is that of
$\{h : a\,\iota_\infty(h)\,a^{-1}\in\Gamma'\}$ for `isoStabBase`. -/
theorem covolume_isoStabAt (Γ' : Subgroup (GInfSO Q₀)) [Countable Γ'] (a : GInfSO Q₀)
    {X : Fin r → VInf F (r + 2)} (ha : a • ratAT Q₀ T₀ Ξ = X)
    [hinv : SMulInvariantMeasure (Γ'.comap ((MulAut.conj a).toMonoidHom.comp (𝔇).ιInf)) (GInfSO (𝔇).Q'')
      (isoStabBase Q₀ hQ T₀ hT hiso Ξ)] :
    covolume (stabArith Γ' X) (stabilizer (GInfSO Q₀) X) (isoStabAt Q₀ hQ T₀ hT hiso Ξ a ha) =
      covolume (Γ'.comap ((MulAut.conj a).toMonoidHom.comp (𝔇).ιInf)) (GInfSO (𝔇).Q'')
        (isoStabBase Q₀ hQ T₀ hT hiso Ξ) := by
  subst ha
  set φ0 := (𝔇).conjInf Q₀ hQ T₀ Ξ a with hφ0
  have hbij : Function.Bijective φ0 := by
    refine ⟨fun h h' e => (𝔇).ιInf_injective Q₀ hQ T₀ Ξ ?_, fun s => ?_⟩
    · have := congrArg (fun z : stabilizer (GInfSO Q₀) (a • ratAT Q₀ T₀ Ξ) => a⁻¹ * (z : GInfSO Q₀) * a) e
      simpa [hφ0, FrameTowerAlg.conjInf_apply, mul_assoc] using this
    · obtain ⟨h, hh⟩ := (𝔇).stab_ιInf Q₀ hQ T₀ Ξ (a⁻¹ * s * a) (by
        rw [mul_smul, mul_smul, s.2, inv_smul_smul])
      exact ⟨h, Subtype.ext (by simp [hφ0, FrameTowerAlg.conjInf_apply, hh, mul_assoc])⟩
  set φ : GInfSO (𝔇).Q'' ≃* stabilizer (GInfSO Q₀) (a • ratAT Q₀ T₀ Ξ) := MulEquiv.ofBijective φ0 hbij with hφ
  have hφm : Measurable φ := (𝔇).measurable_conjInf Q₀ hQ T₀ Ξ a
  have hφm' : Measurable φ.symm := by
    have hME := (𝔇).measurableEmbedding_ιInf Q₀ hQ T₀ Ξ
    have hrange : ∀ s : stabilizer (GInfSO Q₀) (a • ratAT Q₀ T₀ Ξ), a⁻¹ * s * a ∈ Set.range (𝔇).ιInf := fun s =>
      (𝔇).stab_ιInf Q₀ hQ T₀ Ξ _ (by rw [mul_smul, mul_smul, s.2, inv_smul_smul])
    have hm : Measurable fun s : stabilizer (GInfSO Q₀) (a • ratAT Q₀ T₀ Ξ) =>
        (⟨a⁻¹ * s * a, hrange s⟩ : Set.range (𝔇).ιInf) :=
      (((measurable_const_mul a⁻¹).comp measurable_subtype_coe).mul_const a).subtype_mk
    have heq : (φ.symm : stabilizer (GInfSO Q₀) (a • ratAT Q₀ T₀ Ξ) → GInfSO (𝔇).Q'') =
        fun s : stabilizer (GInfSO Q₀) (a • ratAT Q₀ T₀ Ξ) =>
          hME.equivRange.symm ⟨a⁻¹ * (s : GInfSO Q₀) * a, hrange s⟩ := by
      funext s
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      have h1 := congrArg Subtype.val (hME.equivRange.apply_symm_apply ⟨a⁻¹ * s * a, hrange s⟩)
      simp only [MeasurableEmbedding.equivRange_apply] at h1
      show (s : GInfSO Q₀) = a * (𝔇).ιInf _ * a⁻¹
      rw [h1]; group
    rw [heq]
    exact hME.equivRange.symm.measurable.comp hm
  have hΓ : (Γ'.comap ((MulAut.conj a).toMonoidHom.comp (𝔇).ιInf)).map φ.toMonoidHom = stabArith Γ' (a • ratAT Q₀ T₀ Ξ) := by
    ext s
    constructor
    · rintro ⟨h, hh, rfl⟩
      show ((φ h : stabilizer (GInfSO Q₀) (a • ratAT Q₀ T₀ Ξ)) : GInfSO Q₀) ∈ Γ'
      exact hh
    · intro hs
      obtain ⟨h, rfl⟩ := hbij.2 s
      exact ⟨h, hs, rfl⟩
  haveI : Countable (stabArith Γ' (a • ratAT Q₀ T₀ Ξ)) := by
    refine Function.Injective.countable (f := fun γ : stabArith Γ' (a • ratAT Q₀ T₀ Ξ) =>
      (⟨((γ : stabilizer (GInfSO Q₀) (a • ratAT Q₀ T₀ Ξ)) : GInfSO Q₀), Subgroup.mem_subgroupOf.mp γ.2⟩ : Γ'))
      fun γ γ' h => ?_
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  haveI : Countable (Γ'.comap ((MulAut.conj a).toMonoidHom.comp (𝔇).ιInf)) := by
    refine Function.Injective.countable (f := fun h : Γ'.comap ((MulAut.conj a).toMonoidHom.comp (𝔇).ιInf) =>
      (⟨_, h.2⟩ : Γ')) fun h h' e => ?_
    apply Subtype.ext
    apply (𝔇).ιInf_injective Q₀ hQ T₀ Ξ
    have := congrArg Subtype.val e
    simpa using this
  haveI := measurableMul_subgroup (stabilizer (GInfSO Q₀) (a • ratAT Q₀ T₀ Ξ))
  haveI : SMulInvariantMeasure (stabArith Γ' (a • ratAT Q₀ T₀ Ξ)) (stabilizer (GInfSO Q₀) (a • ratAT Q₀ T₀ Ξ))
      ((isoStabBase Q₀ hQ T₀ hT hiso Ξ).map φ) :=
    smulInvariantMeasure_map_of_equiv φ hφm _ _ hΓ _
  exact (covolume_restrict_eq_of_map _ _ φ hφm hφm' hΓ _ _ rfl).symm

include hiso in
/-- The conjugation by any $a$ with $a\,\Xi_\infty = \gamma_\infty\Xi_\infty$ agrees on $\iota_\infty(H_\infty)$ with the conjugation
by $\gamma_\infty$ ($H_\infty$ is commutative). -/
theorem conj_eq_of_smul_eq (γ : GammaSOAdele Q₀) (a : GInfSO Q₀) (ha : a • ratAT Q₀ T₀ Ξ = ratAT Q₀ T₀ (γ • Ξ))
    (h : GInfSO (𝔇).Q'') :
    a * (𝔇).ιInf h * a⁻¹ = (γ : SOAdele Q₀).1 * (𝔇).ιInf h * (γ : SOAdele Q₀).1⁻¹ := by
  rw [ratAT_smul] at ha
  have hfix : ((γ : SOAdele Q₀).1⁻¹ * a) • ratAT Q₀ T₀ Ξ = ratAT Q₀ T₀ Ξ := by
    rw [mul_smul, ha, inv_smul_smul]
  obtain ⟨s, hs⟩ := (𝔇).stab_ιInf Q₀ hQ T₀ Ξ _ hfix
  have ha' : a = (γ : SOAdele Q₀).1 * (𝔇).ιInf s := by rw [hs]; group
  have hc : (𝔇).ιInf s * (𝔇).ιInf h * ((𝔇).ιInf s)⁻¹ = (𝔇).ιInf h := by
    rw [← map_mul, ← map_inv, ← map_mul, mul_comm_GInfSO_iso (𝔇).Q'' (𝔇).hQ'' 𝔢 s h, mul_assoc, mul_inv_cancel,
      mul_one]
  rw [ha', _root_.mul_inv_rev, show (γ : SOAdele Q₀).1 * (𝔇).ιInf s * (𝔇).ιInf h * (((𝔇).ιInf s)⁻¹ *
      (γ : SOAdele Q₀).1⁻¹) = (γ : SOAdele Q₀).1 * ((𝔇).ιInf s * (𝔇).ιInf h * ((𝔇).ιInf s)⁻¹) *
      (γ : SOAdele Q₀).1⁻¹ by group, hc]

include hiso in
/-- **The arithmetic stabilizer, pulled back to $SO(Q'')(F_\infty)$, is the level group $\Gamma_{U_b}$.** -/
theorem comap_unitGroup_eq (i : DC Q₀) (γ : GammaSOAdele Q₀) (a : GInfSO Q₀)
    (ha : a • ratAT Q₀ T₀ Ξ = ratAT Q₀ T₀ (γ • Ξ)) :
    (unitGroup Q₀ i).comap ((MulAut.conj a).toMonoidHom.comp (𝔇).ιInf) =
      levelGroup (GammaSOAdele (𝔇).Q'') (orbitStab (𝔇).ιFin (KSO Q₀) ((dcRep Q₀ i)⁻¹ * (γ : SOAdele Q₀).2)) 1 := by
  ext h
  rw [Subgroup.mem_comap]
  show a * (𝔇).ιInf h * a⁻¹ ∈ unitGroup Q₀ i ↔ _
  rw [conj_eq_of_smul_eq Q₀ hQ T₀ hT hiso Ξ γ a ha h]
  exact conj_mem_unitGroup_iff Q₀ hQ T₀ hT hiso Ξ i γ h

theorem smulInvariantMeasure_smul' {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α]
    [MeasurableSpace G] [MeasurableConstSMul G α] (μ : Measure α) [SMulInvariantMeasure G α μ] (c : ℝ≥0∞) :
    SMulInvariantMeasure G α (c • μ) :=
  ⟨fun γ A hA => by rw [Measure.smul_apply, Measure.smul_apply, measure_preimage_smul]⟩

/-- **Scaling the shell measure scales the covolume.** -/
theorem covolume_smul_shell (U : Subgroup (SOAf (𝔇).Q''))
    (hU1 : ∀ u ∈ U, isoNormFin (𝔇).Q'' (𝔇).hQ'' 𝔢 u = 1)
    (hdisc : DiscreteTopology (levelGroup (GammaSOAdele (𝔇).Q'') U 1)) (c : ℝ≥0∞) :
    covolume (levelGroup (GammaSOAdele (𝔇).Q'') U 1) (GInfSO (𝔇).Q'')
        (c • (muArchTamSO (𝔇).Q'' (𝔇).hQ'').restrict (isoShellInf (𝔇).Q'' (𝔇).hQ'' 𝔢)) =
      c * isoCov Q₀ hQ T₀ hT hiso Ξ U := by
  haveI := countable_GammaSOAdele (𝔇).Q''
  haveI := countable_levelGroup (Γ := GammaSOAdele (𝔇).Q'') U 1
  haveI := measurableConstSMul_subgroup (levelGroup (GammaSOAdele (𝔇).Q'') U 1)
  haveI := smulInvariantMeasure_subgroup (levelGroup (GammaSOAdele (𝔇).Q'') U 1) (muArchTamSO (𝔇).Q'' (𝔇).hQ'')
  haveI hinv : SMulInvariantMeasure (levelGroup (GammaSOAdele (𝔇).Q'') U 1) (GInfSO (𝔇).Q'')
      ((muArchTamSO (𝔇).Q'' (𝔇).hQ'').restrict (isoShellInf (𝔇).Q'' (𝔇).hQ'' 𝔢)) :=
    smulInvariantMeasure_restrict _ _ (smul_mem_isoShellInf_iff (𝔇).Q'' (𝔇).hQ'' 𝔢 U hU1 1)
  haveI := smulInvariantMeasure_smul' (G := levelGroup (GammaSOAdele (𝔇).Q'') U 1)
    ((muArchTamSO (𝔇).Q'' (𝔇).hQ'').restrict (isoShellInf (𝔇).Q'' (𝔇).hQ'' 𝔢)) c
  obtain ⟨E, hEm, hE⟩ := exists_measurableSet_forall_existsUnique_smul_mem
    (levelGroup (GammaSOAdele (𝔇).Q'') U 1)
  rw [isoCov, (IsFundamentalDomain.mk' hEm.nullMeasurableSet hE).covolume_eq_volume,
    (IsFundamentalDomain.mk' hEm.nullMeasurableSet hE).covolume_eq_volume, Measure.smul_apply, smul_eq_mul]

set_option maxHeartbeats 1600000 in
/-- **The classical stabilizer covolume** of a representation $X = \gamma\,\Xi$ of $T_0$ by $M_i$:
$\operatorname{covol}(\Gamma_{i,X}\backslash H_X, \texttt{isoStabMeasure}) = \lambda\cdot\texttt{isoCov}(U_b)$, $b = b_i^{-1}\gamma_f$. -/
theorem covolume_isoStabMeasure (i : DC Q₀) (γ : GammaSOAdele Q₀)
    (hU1 : ∀ u ∈ orbitStab (𝔇).ιFin (KSO Q₀) ((dcRep Q₀ i)⁻¹ * (γ : SOAdele Q₀).2),
      isoNormFin (𝔇).Q'' (𝔇).hQ'' 𝔢 u = 1)
    (hdisc : DiscreteTopology (levelGroup (GammaSOAdele (𝔇).Q'')
      (orbitStab (𝔇).ιFin (KSO Q₀) ((dcRep Q₀ i)⁻¹ * (γ : SOAdele Q₀).2)) 1)) :
    covolume (stabArith (unitGroup Q₀ i) (ratAT Q₀ T₀ (γ • Ξ))) (stabilizer (GInfSO Q₀) (ratAT Q₀ T₀ (γ • Ξ)))
        (isoStabMeasure Q₀ hQ T₀ hT hiso Ξ (ratAT Q₀ T₀ (γ • Ξ))) =
      isoFrameLam Q₀ hQ T₀ hT Ξ *
        isoCov Q₀ hQ T₀ hT hiso Ξ (orbitStab (𝔇).ιFin (KSO Q₀) ((dcRep Q₀ i)⁻¹ * (γ : SOAdele Q₀).2)) := by
  set U := orbitStab (𝔇).ιFin (KSO Q₀) ((dcRep Q₀ i)⁻¹ * (γ : SOAdele Q₀).2) with hU
  have hX : ∃ a : GInfSO Q₀, a • ratAT Q₀ T₀ Ξ = ratAT Q₀ T₀ (γ • Ξ) :=
    ⟨(γ : SOAdele Q₀).1, (ratAT_smul Q₀ T₀ γ Ξ).symm⟩
  rw [isoStabMeasure, dif_pos hX]
  have hcomap := comap_unitGroup_eq Q₀ hQ T₀ hT hiso Ξ i γ hX.choose hX.choose_spec
  haveI := countable_GammaSOAdele Q₀
  haveI : Countable (unitGroup Q₀ i) := countable_levelGroup (Γ := GammaSOAdele Q₀) (KSO Q₀) (dcRep Q₀ i)
  haveI := measurableConstSMul_subgroup (levelGroup (GammaSOAdele (𝔇).Q'') U 1)
  haveI := smulInvariantMeasure_subgroup (levelGroup (GammaSOAdele (𝔇).Q'') U 1) (muArchTamSO (𝔇).Q'' (𝔇).hQ'')
  haveI hinv : SMulInvariantMeasure (levelGroup (GammaSOAdele (𝔇).Q'') U 1) (GInfSO (𝔇).Q'')
      ((muArchTamSO (𝔇).Q'' (𝔇).hQ'').restrict (isoShellInf (𝔇).Q'' (𝔇).hQ'' 𝔢)) :=
    smulInvariantMeasure_restrict _ _ (smul_mem_isoShellInf_iff (𝔇).Q'' (𝔇).hQ'' 𝔢 U hU1 1)
  haveI hinv' : SMulInvariantMeasure ((unitGroup Q₀ i).comap ((MulAut.conj hX.choose).toMonoidHom.comp (𝔇).ιInf))
      (GInfSO (𝔇).Q'') (isoStabBase Q₀ hQ T₀ hT hiso Ξ) := by
    rw [hcomap]
    exact smulInvariantMeasure_smul' _ _
  rw [covolume_isoStabAt Q₀ hQ T₀ hT hiso Ξ (unitGroup Q₀ i) hX.choose hX.choose_spec]
  rw [show covolume ((unitGroup Q₀ i).comap ((MulAut.conj hX.choose).toMonoidHom.comp (𝔇).ιInf)) (GInfSO (𝔇).Q'')
      (isoStabBase Q₀ hQ T₀ hT hiso Ξ) = covolume (levelGroup (GammaSOAdele (𝔇).Q'') U 1) (GInfSO (𝔇).Q'')
      (isoStabBase Q₀ hQ T₀ hT hiso Ξ) by rw [hcomap]]
  exact covolume_smul_shell Q₀ hQ T₀ hT hiso Ξ U hU1 hdisc _

/-! ### The bijection: $\Gamma_i$-orbits of representations over an orbit $O$ versus $H(F)\backslash H(\mathbb A_f)/U_O$ -/

/-- The index set of the classical sum: the classes $i$ and the $\Gamma_i$-orbits of representations of $T_0$ by $M_i$. -/
abbrev RepIdx : Type := Σ i : DC Q₀, orbitRel.Quotient (unitGroup Q₀ i) (repsT Q₀ T₀ i)

include hQ hT in
/-- Every representation is $\gamma\,\Xi$ with $b_i^{-1}\gamma_f\,\Xi_f$ integral (Witt). -/
theorem exists_gamma_of_rep (i : DC Q₀) (X : repsT Q₀ T₀ i) :
    ∃ γ : GammaSOAdele Q₀, ratAT Q₀ T₀ (γ • Ξ) = X ∧
      ((dcRep Q₀ i)⁻¹ * (γ : SOAdele Q₀).2) • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + 2) r := by
  obtain ⟨η, hη, hηX⟩ := X.2
  obtain ⟨γ, hγ⟩ := (𝔇).exists_smul_eq_ratFrame Q₀ hQ T₀ Ξ hT (by norm_num) η
  refine ⟨γ, by rw [hγ]; exact hηX, ?_⟩
  have hη' : ratFT Q₀ T₀ η ∈ dcRep Q₀ i • latHatT F (r + 2) r := hη
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hη'
  rw [mul_smul, ← ratFT_smul, hγ]
  exact hη'

/-- The chosen rational element $\gamma$ of an index ($X = \gamma\Xi$ for the representative $X$ of the orbit). -/
def isoGam (p : RepIdx Q₀ T₀) : GammaSOAdele Q₀ :=
  (exists_gamma_of_rep Q₀ hQ T₀ hT Ξ p.1 p.2.out).choose

theorem isoGam_spec (p : RepIdx Q₀ T₀) :
    ratAT Q₀ T₀ (isoGam Q₀ hQ T₀ hT Ξ p • Ξ) = p.2.out ∧
      ((dcRep Q₀ p.1)⁻¹ * (isoGam Q₀ hQ T₀ hT Ξ p : SOAdele Q₀).2) • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + 2) r :=
  (exists_gamma_of_rep Q₀ hQ T₀ hT Ξ p.1 p.2.out).choose_spec

/-- The integral frame $b = b_i^{-1}\gamma_f$ of an index. -/
def isoB (p : RepIdx Q₀ T₀) : {b : SOAf Q₀ // b • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + 2) r} :=
  ⟨(dcRep Q₀ p.1)⁻¹ * (isoGam Q₀ hQ T₀ hT Ξ p : SOAdele Q₀).2, (isoGam_spec Q₀ hQ T₀ hT Ξ p).2⟩

/-- The orbit of integral frames of an index. -/
def isoPi (p : RepIdx Q₀ T₀) : FinOrbit Q₀ T₀ Ξ := Quotient.mk _ (isoB Q₀ hQ T₀ hT Ξ p)

/-- **Change of representative**: for any $\gamma$ with $\gamma\Xi$ in the orbit of the index $p$,
$b_p = k\,b_i^{-1}\gamma_f\,\iota_f(\eta_f)$ with $k\in K$, $\eta\in SO(Q'')(F)$. -/
theorem isoB_eq (p : RepIdx Q₀ T₀) (γ : GammaSOAdele Q₀) (X : repsT Q₀ T₀ p.1)
    (hXq : (Quotient.mk _ X : orbitRel.Quotient (unitGroup Q₀ p.1) (repsT Q₀ T₀ p.1)) = p.2)
    (hγX : ratAT Q₀ T₀ (γ • Ξ) = X) :
    ∃ k ∈ KSO Q₀, ∃ η ∈ GammaSOAdele (𝔇).Q'',
      (isoB Q₀ hQ T₀ hT Ξ p).1 = k * ((dcRep Q₀ p.1)⁻¹ * (γ : SOAdele Q₀).2) * (𝔇).ιFin η.2 := by
  have hγ'X := (isoGam_spec Q₀ hQ T₀ hT Ξ p).1
  have hX' : (Quotient.mk _ p.2.out : orbitRel.Quotient (unitGroup Q₀ p.1) (repsT Q₀ T₀ p.1)) =
      Quotient.mk _ X := by rw [Quotient.out_eq, hXq]
  obtain ⟨δ, hδ⟩ := Quotient.exact hX'
  obtain ⟨d, ⟨hdΓ, hdK⟩, hd1⟩ := δ.2
  have hdK' : (dcRep Q₀ p.1)⁻¹ * d.2 * dcRep Q₀ p.1 ∈ KSO Q₀ := hdK
  have hfr : isoGam Q₀ hQ T₀ hT Ξ p • Ξ = ((⟨d, hdΓ⟩ : GammaSOAdele Q₀) * γ) • Ξ := by
    apply ratAT_injective Q₀ T₀
    rw [hγ'X, mul_smul, ratAT_smul Q₀ T₀ ⟨d, hdΓ⟩, hγX, ← hδ]
    show ((δ : GInfSO Q₀)) • (X : Fin r → VInf F (r + 2)) = d.1 • (X : Fin r → VInf F (r + 2))
    rw [← hd1]; rfl
  have hfix : (((⟨d, hdΓ⟩ : GammaSOAdele Q₀) * γ)⁻¹ * isoGam Q₀ hQ T₀ hT Ξ p) • Ξ = Ξ := by
    rw [mul_smul, hfr, inv_smul_smul]
  have hfixA : ((((⟨d, hdΓ⟩ : GammaSOAdele Q₀) * γ)⁻¹ * isoGam Q₀ hQ T₀ hT Ξ p : GammaSOAdele Q₀) :
      SOAdele Q₀) • frameA (cols Ξ.1) = frameA (cols Ξ.1) := by
    have := congrArg (ratFrameA Q₀ T₀) hfix
    rwa [ratFrameA_smul] at this
  obtain ⟨η, hηΓ, hηe⟩ := (𝔇).stabΓ _ (((⟨d, hdΓ⟩ : GammaSOAdele Q₀) * γ)⁻¹ * isoGam Q₀ hQ T₀ hT Ξ p).2 hfixA
  refine ⟨(dcRep Q₀ p.1)⁻¹ * d.2 * dcRep Q₀ p.1, hdK', η, hηΓ, ?_⟩
  have h2 : (𝔇).ιFin η.2 = ((((⟨d, hdΓ⟩ : GammaSOAdele Q₀) * γ)⁻¹ * isoGam Q₀ hQ T₀ hT Ξ p :
      GammaSOAdele Q₀) : SOAdele Q₀).2 := congrArg Prod.snd hηe
  rw [h2]
  show (dcRep Q₀ p.1)⁻¹ * (isoGam Q₀ hQ T₀ hT Ξ p : SOAdele Q₀).2 = _
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Prod.snd_mul, Prod.snd_inv]
  group

include hiso in
/-- From $b \sim b_O$: $b = k\,b_O\,\iota_f(h)$. -/
theorem exists_k_h (b : {b : SOAf Q₀ // b • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + 2) r}) (O : FinOrbit Q₀ T₀ Ξ)
    (hO : Quotient.mk _ b = O) :
    ∃ k ∈ KSO Q₀, ∃ h : SOAf (𝔇).Q'', b.1 = k * finOrbitRep Q₀ T₀ Ξ O * (𝔇).ιFin h := by
  have hrel : (finOrbitSetoid Q₀ T₀ Ξ).r (Quotient.out O) b := by
    rw [← hO]; exact Quotient.mk_out (s := finOrbitSetoid Q₀ T₀ Ξ) b
  obtain ⟨k, hk, y, hy, hky⟩ := Set.mem_smul.1 hrel
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have hfix : ((k * finOrbitRep Q₀ T₀ Ξ O)⁻¹ * b.1) • ratFT Q₀ T₀ Ξ = ratFT Q₀ T₀ Ξ := by
    rw [mul_smul, ← hky, ← mul_smul k, show finOrbitRep Q₀ T₀ Ξ O = (Quotient.out O).1 from rfl, inv_smul_smul]
  obtain ⟨h, hh⟩ := (𝔇).stab_ιFin Q₀ hQ T₀ Ξ _ hfix
  exact ⟨k, hk, h, by rw [hh]; group⟩

/-- The double coset of an index over $O$: $b_p = k\,b_O\,\iota_f(h)\mapsto H(F)\,h\,U_O$. -/
def isoPsi (O : FinOrbit Q₀ T₀ Ξ) (p : {p : RepIdx Q₀ T₀ // isoPi Q₀ hQ T₀ hT Ξ p = O}) :
    DCq (𝔇).Q'' (isoU Q₀ hQ T₀ hT Ξ O) :=
  Quotient.mk _ (exists_k_h Q₀ hQ T₀ hT hiso Ξ (isoB Q₀ hQ T₀ hT Ξ p.1) O p.2).choose_spec.2.choose

include hiso in
theorem rel_of_eq (O : FinOrbit Q₀ T₀ Ξ) {k k' : SOAf Q₀} (hk : k ∈ KSO Q₀) (hk' : k' ∈ KSO Q₀)
    (h h' : SOAf (𝔇).Q'') (η : SOAdele (𝔇).Q'') (hη : η ∈ GammaSOAdele (𝔇).Q'')
    (he : k' * finOrbitRep Q₀ T₀ Ξ O * (𝔇).ιFin h' = k * finOrbitRep Q₀ T₀ Ξ O * (𝔇).ιFin h * (𝔇).ιFin η.2) :
    (dcqSetoid (𝔇).Q'' (isoU Q₀ hQ T₀ hT Ξ O)).r h h' := by
  set ρ := finOrbitRep Q₀ T₀ Ξ O
  have hc : ∀ x y : SOAf (𝔇).Q'', x * y = y * x := mul_comm_SOAf_iso (𝔇).Q'' (𝔇).hQ'' 𝔢
  refine ⟨η, hη, h' * h⁻¹ * η.2⁻¹, ?_, ?_⟩
  · show h' * h⁻¹ * η.2⁻¹ ∈ orbitStab (𝔇).ιFin (KSO Q₀) ρ
    rw [mem_orbitStab']
    have e1 : (𝔇).ιFin h' = ρ⁻¹ * k'⁻¹ * k * ρ * (𝔇).ιFin h * (𝔇).ιFin η.2 := by
      rw [show ρ⁻¹ * k'⁻¹ * k * ρ * (𝔇).ιFin h * (𝔇).ιFin η.2 =
        ρ⁻¹ * k'⁻¹ * (k * ρ * (𝔇).ιFin h * (𝔇).ιFin η.2) by group, ← he]; group
    have e2 : (𝔇).ιFin h * (𝔇).ιFin η.2 = (𝔇).ιFin η.2 * (𝔇).ιFin h := by
      rw [← map_mul, ← map_mul, hc]
    have e : ρ * (𝔇).ιFin (h' * h⁻¹ * η.2⁻¹) * ρ⁻¹ = k'⁻¹ * k := by
      rw [map_mul, map_mul, e1, map_inv, map_inv,
        show ρ * (ρ⁻¹ * k'⁻¹ * k * ρ * (𝔇).ιFin h * (𝔇).ιFin η.2 * ((𝔇).ιFin h)⁻¹ * ((𝔇).ιFin η.2)⁻¹) * ρ⁻¹ =
          k'⁻¹ * k * ρ * ((𝔇).ιFin h * (𝔇).ιFin η.2) * ((𝔇).ιFin h)⁻¹ * ((𝔇).ιFin η.2)⁻¹ * ρ⁻¹ by group, e2]
      group
    rw [e]
    exact (KSO Q₀).mul_mem ((KSO Q₀).inv_mem hk') hk
  · rw [show η.2 * h * (h' * h⁻¹ * η.2⁻¹) = η.2 * (h * h') * h⁻¹ * η.2⁻¹ by group, hc h h',
      show η.2 * (h' * h) * h⁻¹ * η.2⁻¹ = η.2 * h' * η.2⁻¹ by group, hc η.2 h', mul_inv_cancel_right]

/-- **The double coset of an index does not depend on the choices**: for any $\gamma$ with $\gamma\Xi$ in the orbit
and any $b_i^{-1}\gamma_f = k\,b_O\,\iota_f(h)$, the double coset is that of $h$. -/
theorem isoPsi_eq (O : FinOrbit Q₀ T₀ Ξ) (p : {p : RepIdx Q₀ T₀ // isoPi Q₀ hQ T₀ hT Ξ p = O})
    (γ : GammaSOAdele Q₀) (X : repsT Q₀ T₀ p.1.1)
    (hXq : (Quotient.mk _ X : orbitRel.Quotient (unitGroup Q₀ p.1.1) (repsT Q₀ T₀ p.1.1)) = p.1.2)
    (hγX : ratAT Q₀ T₀ (γ • Ξ) = X) {k : SOAf Q₀} (hk : k ∈ KSO Q₀) (h : SOAf (𝔇).Q'')
    (hb : (dcRep Q₀ p.1.1)⁻¹ * (γ : SOAdele Q₀).2 = k * finOrbitRep Q₀ T₀ Ξ O * (𝔇).ιFin h) :
    isoPsi Q₀ hQ T₀ hT hiso Ξ O p = Quotient.mk _ h := by
  have hspec := (exists_k_h Q₀ hQ T₀ hT hiso Ξ (isoB Q₀ hQ T₀ hT Ξ p.1) O p.2).choose_spec
  set k' := (exists_k_h Q₀ hQ T₀ hT hiso Ξ (isoB Q₀ hQ T₀ hT Ξ p.1) O p.2).choose
  have hk' := hspec.1
  set h' := hspec.2.choose
  have hb' : (isoB Q₀ hQ T₀ hT Ξ p.1).1 = k' * finOrbitRep Q₀ T₀ Ξ O * (𝔇).ιFin h' := hspec.2.choose_spec
  show (Quotient.mk _ h' : DCq (𝔇).Q'' (isoU Q₀ hQ T₀ hT Ξ O)) = Quotient.mk _ h
  obtain ⟨k₁, hk₁, η, hη, hb₁⟩ := isoB_eq Q₀ hQ T₀ hT Ξ p.1 γ X hXq hγX
  refine (Quotient.sound (rel_of_eq Q₀ hQ T₀ hT hiso Ξ O ((KSO Q₀).mul_mem hk₁ hk) hk' h h' η hη ?_)).symm
  rw [← hb', hb₁, hb]
  group

include hiso in
theorem iotaGamma_inv_smul_ratFrame (η : SOAdele (𝔇).Q'') (hη : η ∈ GammaSOAdele (𝔇).Q'') :
    (⟨MonoidHom.prodMap (𝔇).ιInf (𝔇).ιFin η, (𝔇).gamma_mem η hη⟩ : GammaSOAdele Q₀)⁻¹ • Ξ = Ξ := by
  rw [inv_smul_eq_iff]
  exact (iotaGamma_smul_ratFrame Q₀ hQ T₀ hT hiso Ξ η hη).symm

set_option maxHeartbeats 1600000 in
/-- **Injectivity**: indices over $O$ with the same double coset are equal. -/
theorem isoPsi_injective (O : FinOrbit Q₀ T₀ Ξ) : Function.Injective (isoPsi Q₀ hQ T₀ hT hiso Ξ O) := by
  rintro ⟨⟨i, q⟩, hp⟩ ⟨⟨i', q'⟩, hp'⟩ he
  have hc : ∀ x y : SOAf (𝔇).Q'', x * y = y * x := mul_comm_SOAf_iso (𝔇).Q'' (𝔇).hQ'' 𝔢
  have hs := (exists_k_h Q₀ hQ T₀ hT hiso Ξ (isoB Q₀ hQ T₀ hT Ξ ⟨i, q⟩) O hp).choose_spec
  have hs' := (exists_k_h Q₀ hQ T₀ hT hiso Ξ (isoB Q₀ hQ T₀ hT Ξ ⟨i', q'⟩) O hp').choose_spec
  set k := (exists_k_h Q₀ hQ T₀ hT hiso Ξ (isoB Q₀ hQ T₀ hT Ξ ⟨i, q⟩) O hp).choose
  set k' := (exists_k_h Q₀ hQ T₀ hT hiso Ξ (isoB Q₀ hQ T₀ hT Ξ ⟨i', q'⟩) O hp').choose
  set h := hs.2.choose
  set h' := hs'.2.choose
  have hb : (isoB Q₀ hQ T₀ hT Ξ ⟨i, q⟩).1 = k * finOrbitRep Q₀ T₀ Ξ O * (𝔇).ιFin h := hs.2.choose_spec
  have hb' : (isoB Q₀ hQ T₀ hT Ξ ⟨i', q'⟩).1 = k' * finOrbitRep Q₀ T₀ Ξ O * (𝔇).ιFin h' := hs'.2.choose_spec
  have he' : (Quotient.mk _ h : DCq (𝔇).Q'' (isoU Q₀ hQ T₀ hT Ξ O)) = Quotient.mk _ h' := he
  obtain ⟨η, hη, u, hu, hhu⟩ := Quotient.exact he'
  have hu' : finOrbitRep Q₀ T₀ Ξ O * (𝔇).ιFin u * (finOrbitRep Q₀ T₀ Ξ O)⁻¹ ∈ KSO Q₀ := hu
  set γ := isoGam Q₀ hQ T₀ hT Ξ ⟨i, q⟩
  set γ' := isoGam Q₀ hQ T₀ hT Ξ ⟨i', q'⟩
  set ρ := finOrbitRep Q₀ T₀ Ξ O
  set kt := k' * (ρ * (𝔇).ιFin u * ρ⁻¹) * k⁻¹ with hkt
  have hkt_mem : kt ∈ KSO Q₀ := (KSO Q₀).mul_mem ((KSO Q₀).mul_mem hs'.1 hu') ((KSO Q₀).inv_mem hs.1)
  -- `b' = kt * b * ι(η_f)`
  have hι : (𝔇).ιFin h' = (𝔇).ιFin u * (𝔇).ιFin h * (𝔇).ιFin η.2 := by
    rw [hhu, ← map_mul, ← map_mul, show η.2 * h * u = u * h * η.2 by
      rw [hc η.2 h, mul_assoc, hc η.2 u, ← mul_assoc, hc h u]]
  have hbb : (dcRep Q₀ i')⁻¹ * (γ' : SOAdele Q₀).2 = kt * ((dcRep Q₀ i)⁻¹ * (γ : SOAdele Q₀).2) * (𝔇).ιFin η.2 := by
    have e1 : (dcRep Q₀ i')⁻¹ * (γ' : SOAdele Q₀).2 = (isoB Q₀ hQ T₀ hT Ξ ⟨i', q'⟩).1 := rfl
    have e2 : (dcRep Q₀ i)⁻¹ * (γ : SOAdele Q₀).2 = (isoB Q₀ hQ T₀ hT Ξ ⟨i, q⟩).1 := rfl
    rw [e1, e2, hb', hb, hι, hkt]
    group
  set ιη : GammaSOAdele Q₀ := ⟨MonoidHom.prodMap (𝔇).ιInf (𝔇).ιFin η, (𝔇).gamma_mem η hη⟩ with hιη
  set δ : GammaSOAdele Q₀ := γ' * ιη⁻¹ * γ⁻¹ with hδ
  have hδ2 : (δ : SOAdele Q₀).2 * dcRep Q₀ i * 1 = dcRep Q₀ i' * kt := by
    have : (γ' : SOAdele Q₀).2 = dcRep Q₀ i' * (kt * ((dcRep Q₀ i)⁻¹ * (γ : SOAdele Q₀).2) * (𝔇).ιFin η.2) := by
      rw [← hbb]; group
    simp only [hδ, hιη, Subgroup.coe_mul, Subgroup.coe_inv, Prod.snd_mul, Prod.snd_inv, mul_one]
    rw [this, prodMap_snd']
    group
  have hii : i = i' := dcRep_disj Q₀ i i' δ δ.2 1 (KSO Q₀).one_mem kt hkt_mem hδ2
  subst hii
  have hδK : (dcRep Q₀ i)⁻¹ * (δ : SOAdele Q₀).2 * dcRep Q₀ i ∈ KSO Q₀ := by
    have : (dcRep Q₀ i)⁻¹ * (δ : SOAdele Q₀).2 * dcRep Q₀ i = kt := by
      rw [show (dcRep Q₀ i)⁻¹ * (δ : SOAdele Q₀).2 * dcRep Q₀ i =
        (dcRep Q₀ i)⁻¹ * ((δ : SOAdele Q₀).2 * dcRep Q₀ i * 1) by group, hδ2]; group
    rw [this]; exact hkt_mem
  have hδU : (δ : SOAdele Q₀).1 ∈ unitGroup Q₀ i := ⟨δ, ⟨δ.2, hδK⟩, rfl⟩
  have hfr : δ • (γ • Ξ) = γ' • Ξ := by
    rw [hδ, ← mul_smul, mul_assoc, inv_mul_cancel, mul_one, mul_smul,
      iotaGamma_inv_smul_ratFrame Q₀ hQ T₀ hT hiso Ξ η hη]
  have hq : q = q' := by
    have hr : (orbitRel (unitGroup Q₀ i) (repsT Q₀ T₀ i)) q'.out q.out := by
      refine ⟨⟨(δ : SOAdele Q₀).1, hδU⟩, Subtype.ext ?_⟩
      show (δ : SOAdele Q₀).1 • ((q.out : repsT Q₀ T₀ i) : Fin r → VInf F (r + 2)) = (q'.out : repsT Q₀ T₀ i)
      rw [← (isoGam_spec Q₀ hQ T₀ hT Ξ ⟨i, q⟩).1, ← (isoGam_spec Q₀ hQ T₀ hT Ξ ⟨i, q'⟩).1, ← ratAT_smul, hfr]
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    exact Quotient.sound ((orbitRel (unitGroup Q₀ i) (repsT Q₀ T₀ i)).iseqv.symm hr)
  subst hq
  rfl

/-- **Surjectivity**: every double coset of $U_O$ comes from a representation. -/
theorem isoPsi_surjective (O : FinOrbit Q₀ T₀ Ξ) : Function.Surjective (isoPsi Q₀ hQ T₀ hT hiso Ξ O) := by
  intro c
  set ρ := finOrbitRep Q₀ T₀ Ξ O
  set h := dcqRep (𝔇).Q'' (isoU Q₀ hQ T₀ hT Ξ O) c
  obtain ⟨i, d, hd, k₀, hk₀, hg⟩ := dcRep_cov Q₀ (((𝔇).ιFin h)⁻¹ * ρ⁻¹)
  set γ : GammaSOAdele Q₀ := (⟨d, hd⟩ : GammaSOAdele Q₀)⁻¹ with hγ
  have hb : (dcRep Q₀ i)⁻¹ * (γ : SOAdele Q₀).2 = k₀ * ρ * (𝔇).ιFin h := by
    have : (γ : SOAdele Q₀).2 = d.2⁻¹ := rfl
    rw [this]
    have e : d.2⁻¹ = dcRep Q₀ i * k₀ * (((𝔇).ιFin h)⁻¹ * ρ⁻¹)⁻¹ := by rw [hg]; group
    rw [e]; group
  have hint : ratFT Q₀ T₀ (γ • Ξ) ∈ dcRep Q₀ i • latHatT F (r + 2) r := by
    rw [Set.mem_smul_set_iff_inv_smul_mem, ratFT_smul, smul_smul, hb, mul_smul, mul_smul,
      (𝔇).ιFin_smul_ratFT Q₀ hQ T₀ Ξ, latHatT_stable Q₀ k₀ hk₀]
    exact (Quotient.out O).2
  set X : repsT Q₀ T₀ i := ⟨ratAT Q₀ T₀ (γ • Ξ), ⟨γ • Ξ, hint, rfl⟩⟩
  have hO : isoPi Q₀ hQ T₀ hT Ξ ⟨i, Quotient.mk _ X⟩ = O := by
    obtain ⟨k₁, hk₁, η, hη, hb₁⟩ := isoB_eq Q₀ hQ T₀ hT Ξ ⟨i, Quotient.mk _ X⟩ γ X rfl rfl
    conv_rhs => rw [← Quotient.out_eq O]
    refine (Quotient.sound ?_).symm
    refine Set.mem_smul.2 ⟨k₁ * k₀, (KSO Q₀).mul_mem hk₁ hk₀, _, rfl, ?_⟩
    show (k₁ * k₀) • ((Quotient.out O).1 • ratFT Q₀ T₀ Ξ) = (isoB Q₀ hQ T₀ hT Ξ ⟨i, Quotient.mk _ X⟩).1 • ratFT Q₀ T₀ Ξ
    rw [hb₁, hb]
    simp only [mul_smul, (𝔇).ιFin_smul_ratFT Q₀ hQ T₀ Ξ]
    rfl
  refine ⟨⟨⟨i, Quotient.mk _ X⟩, hO⟩, ?_⟩
  rw [isoPsi_eq Q₀ hQ T₀ hT hiso Ξ O ⟨⟨i, Quotient.mk _ X⟩, hO⟩ γ X rfl rfl hk₀ h hb]
  exact Quotient.out_eq c

set_option maxHeartbeats 1600000 in
/-- **The classical-adelic dictionary**: $\sum_i\rho^1(M_i,T_0) = \lambda\sum_O\sum_{c}\texttt{isoCov}(U_O)$. -/
theorem tsum_repMeasureIso
    (hU1 : ∀ (b : SOAf Q₀) (u : SOAf (𝔇).Q''), u ∈ orbitStab (𝔇).ιFin (KSO Q₀) b →
      isoNormFin (𝔇).Q'' (𝔇).hQ'' 𝔢 u = 1)
    (hdisc : ∀ (b : SOAf Q₀) (c : SOAf (𝔇).Q''),
      DiscreteTopology (levelGroup (GammaSOAdele (𝔇).Q'') (orbitStab (𝔇).ιFin (KSO Q₀) b) c)) :
    ∑' i, repMeasureIso Q₀ hQ T₀ hT hiso Ξ i = isoFrameLam Q₀ hQ T₀ hT Ξ *
      ∑' O : FinOrbit Q₀ T₀ Ξ, ∑' _c : DCq (𝔇).Q'' (isoU Q₀ hQ T₀ hT Ξ O),
        isoCov Q₀ hQ T₀ hT hiso Ξ (isoU Q₀ hQ T₀ hT Ξ O) := by
  set g : FinOrbit Q₀ T₀ Ξ → ℝ≥0∞ := fun O => isoFrameLam Q₀ hQ T₀ hT Ξ *
    isoCov Q₀ hQ T₀ hT hiso Ξ (isoU Q₀ hQ T₀ hT Ξ O) with hg
  have hterm : ∀ p : RepIdx Q₀ T₀,
      covolume (stabArith (unitGroup Q₀ p.1) ((p.2.out : repsT Q₀ T₀ p.1) : Fin r → VInf F (r + 2)))
        (stabilizer (GInfSO Q₀) ((p.2.out : repsT Q₀ T₀ p.1) : Fin r → VInf F (r + 2)))
        (isoStabMeasure Q₀ hQ T₀ hT hiso Ξ ((p.2.out : repsT Q₀ T₀ p.1) : Fin r → VInf F (r + 2))) =
      g (isoPi Q₀ hQ T₀ hT Ξ p) := by
    intro p
    rw [← (isoGam_spec Q₀ hQ T₀ hT Ξ p).1]
    rw [covolume_isoStabMeasure Q₀ hQ T₀ hT hiso Ξ p.1 (isoGam Q₀ hQ T₀ hT Ξ p) (hU1 _) (hdisc _ 1)]
    have hrel : (finOrbitSetoid Q₀ T₀ Ξ).r (Quotient.out (isoPi Q₀ hQ T₀ hT Ξ p)) (isoB Q₀ hQ T₀ hT Ξ p) :=
      Quotient.mk_out (s := finOrbitSetoid Q₀ T₀ Ξ) (isoB Q₀ hQ T₀ hT Ξ p)
    have hU := orbitStab_eq_of_rel Q₀ hQ T₀ hT hiso Ξ _ _ hrel
    change _ = isoFrameLam Q₀ hQ T₀ hT Ξ * isoCov Q₀ hQ T₀ hT hiso Ξ
      (orbitStab (𝔇).ιFin (KSO Q₀) (Quotient.out (isoPi Q₀ hQ T₀ hT Ξ p)).1)
    rw [← hU]
    rfl
  calc ∑' i, repMeasureIso Q₀ hQ T₀ hT hiso Ξ i
      = ∑' p : RepIdx Q₀ T₀, g (isoPi Q₀ hQ T₀ hT Ξ p) := by
        simp only [repMeasureIso, repMeasureOf]
        rw [ENNReal.tsum_sigma']
        exact tsum_congr fun i => tsum_congr fun q => hterm ⟨i, q⟩
    _ = ∑' O : FinOrbit Q₀ T₀ Ξ, ∑' p : {p : RepIdx Q₀ T₀ // isoPi Q₀ hQ T₀ hT Ξ p = O}, g O := by
        rw [← (Equiv.sigmaFiberEquiv (isoPi Q₀ hQ T₀ hT Ξ)).tsum_eq, ENNReal.tsum_sigma']
        refine tsum_congr fun O => tsum_congr fun p => ?_
        rw [Equiv.sigmaFiberEquiv_apply, p.2]
    _ = ∑' O : FinOrbit Q₀ T₀ Ξ, ∑' _c : DCq (𝔇).Q'' (isoU Q₀ hQ T₀ hT Ξ O), g O := by
        refine tsum_congr fun O => ?_
        exact (Equiv.ofBijective (isoPsi Q₀ hQ T₀ hT hiso Ξ O)
          ⟨isoPsi_injective Q₀ hQ T₀ hT hiso Ξ O, isoPsi_surjective Q₀ hQ T₀ hT hiso Ξ O⟩).tsum_eq (fun _ => g O)
    _ = _ := by
        simp only [hg, ENNReal.tsum_mul_left]

end QuadFormsKB.Tamagawa.Indefinite
