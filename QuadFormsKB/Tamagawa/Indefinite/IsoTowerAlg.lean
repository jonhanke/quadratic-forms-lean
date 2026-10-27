/-
# Algebraic frame data without measures

**Layer:** number fields, adeles. A `FrameTower` (`FrameTower.lean`) carries Weil's fibration for the Tamagawa measures
with $\lambda_v = 1$, which forces `muTam Q'' 1 ≠ 0`; for an **isotropic** binary complement $Q''$ that measure is $0$
($\prod_v(1 - Nv^{-1})$ diverges to $0$), so no tower exists. Its algebraic part does exist:

* `FrameTowerAlg Q₀ hQ n' Ξ`: the complement form $Q''$ over $\mathcal O_F$ in $n'$ variables, the stabilizer embedding
  $\iota = \iota_\infty\times\iota_f : SO(Q'')(\mathbb A)\to SO(V)(\mathbb A)$ (injective, fixing the adelic frame $\Xi$, onto
  its stabilizer, also over $F$), and the complement matrix $C$ ($\iota(h)\,C = C\,h$ at every place, $C^{\mathsf T}HC = H''$,
  $C^{\mathsf T}H\Xi = 0$); `FrameTower.toAlg` forgets the measures of a tower;
* **`nonempty_frameTowerAlg_ratFrame`**: every rational frame of a nondegenerate $T_0$ has such data, for every
  complement rank $n'\ge1$ (the induction of `nonempty_frameTower` and `nonempty_frameTower_ratFrame`, without the
  measure fields).

Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.Indefinite.FrameTowerFrame

open MeasureTheory Set Matrix MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F]

/-- **The algebraic frame data** of a rational frame $\Xi$ of $Q_0$ with complement of rank $n'$ (no measures).
Fields: `Q''`, `hQ''`, `ιInf`, `ιFin`, `measurable_ιInf`, `continuous_ιInf`, `fix`, `injective`, `gamma_mem`, `stabΓ`,
`stab`, `Cm`, `hCR`, `hCC`, `hCV`, `hCH`, `hΞC`. -/
structure FrameTowerAlg {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate) (n' : ℕ) {r : ℕ}
    (Ξ : Fin r → Fin N → F) where
  /-- The complement form. -/
  Q'' : QuadForm (𝓞 F) n'
  hQ'' : Q''.Nondegenerate
  /-- The embedding at the infinite places. -/
  ιInf : GInfSO Q'' →* GInfSO Q₀
  /-- The embedding at the finite places. -/
  ιFin : SOAf Q'' →* SOAf Q₀
  /-- The archimedean embedding is measurable. -/
  measurable_ιInf : Measurable ιInf
  /-- The archimedean embedding is continuous. -/
  continuous_ιInf : Continuous ιInf
  /-- $\iota(h)$ fixes the adelic frame $\Xi$. -/
  fix : ∀ h, MonoidHom.prodMap ιInf ιFin h • frameA Ξ = frameA Ξ
  /-- $\iota$ is injective. -/
  injective : Function.Injective (MonoidHom.prodMap ιInf ιFin)
  /-- $\iota(SO(Q'')(F))\subseteq SO(V)(F)$. -/
  gamma_mem : ∀ h ∈ GammaSOAdele Q'', MonoidHom.prodMap ιInf ιFin h ∈ GammaSOAdele Q₀
  /-- The stabilizer of $\Xi$ in $SO(V)(F)$ is in $\iota(SO(Q'')(F))$. -/
  stabΓ : ∀ γ ∈ GammaSOAdele Q₀, γ • frameA Ξ = frameA Ξ → ∃ h ∈ GammaSOAdele Q'', MonoidHom.prodMap ιInf ιFin h = γ
  /-- The stabilizer of $\Xi$ in $SO(V)(\mathbb A)$ is in $\iota(SO(Q'')(\mathbb A))$. -/
  stab : ∀ g : SOAdele Q₀, g • frameA Ξ = frameA Ξ → ∃ h, MonoidHom.prodMap ιInf ιFin h = g
  /-- The complement matrix. -/
  Cm : Matrix (Fin N) (Fin n') F
  /-- $\iota(h)\,C = C\,h$ at the real places. -/
  hCR : ∀ (h : SOAdele Q'') (w : {w : InfinitePlace F // w.IsReal}),
    matR Q₀ (MonoidHom.prodMap ιInf ιFin h) w * Cm.map (σR w) = Cm.map (σR w) * matR Q'' h w
  /-- $\iota(h)\,C = C\,h$ at the complex places. -/
  hCC : ∀ (h : SOAdele Q'') (w : {w : InfinitePlace F // w.IsComplex}),
    matC Q₀ (MonoidHom.prodMap ιInf ιFin h) w * Cm.map (σC w) = Cm.map (σC w) * matC Q'' h w
  /-- $\iota(h)\,C = C\,h$ at the finite places. -/
  hCV : ∀ (h : SOAdele Q'') (v : HeightOneSpectrum (𝓞 F)),
    matV Q₀ (MonoidHom.prodMap ιInf ιFin h) v * Cm.map (σV v) = Cm.map (σV v) * matV Q'' h v
  /-- $C^{\mathsf T}HC = H''$. -/
  hCH : Cmᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian * Cm = (Q''.map (algebraMap (𝓞 F) F)).hessian
  /-- $C^{\mathsf T}H\xi_j = 0$. -/
  hΞC : ∀ j, (Cmᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian) *ᵥ Ξ j = 0

/-- **A frame tower forgets to its algebraic data.** -/
def FrameTower.toAlg {N : ℕ} {Q₀ : QuadForm (𝓞 F) N} {hQ : Q₀.Nondegenerate} {n' r : ℕ} {Ξ : Fin r → Fin N → F}
    (D : FrameTower Q₀ hQ n' Ξ) : FrameTowerAlg Q₀ hQ n' Ξ where
  Q'' := D.Q''
  hQ'' := D.hQ''
  ιInf := D.ιInf
  ιFin := D.ιFin
  measurable_ιInf := D.measurable_ιInf
  continuous_ιInf := D.continuous_ιInf
  fix := D.C.ι_smul
  injective := D.C.ι_injective
  gamma_mem := D.gamma_mem
  stabΓ := D.stabΓ
  stab := D.stab
  Cm := D.Cm
  hCR := D.hCR
  hCC := D.hCC
  hCV := D.hCV
  hCH := D.hCH
  hΞC := D.hΞC

/-- **The empty frame** ($r = 0$). -/
def FrameTowerAlg.base {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate) (Ξ : Fin 0 → Fin N → F) :
    FrameTowerAlg Q₀ hQ N Ξ where
  Q'' := Q₀
  hQ'' := hQ
  ιInf := MonoidHom.id _
  ιFin := MonoidHom.id _
  measurable_ιInf := measurable_id
  continuous_ιInf := continuous_id
  fix := fun _ => funext fun j => j.elim0
  injective := fun a b h => by simpa using h
  gamma_mem := fun h hh => hh
  stabΓ := fun γ hγ _ => ⟨γ, hγ, rfl⟩
  stab := fun g _ => ⟨g, rfl⟩
  Cm := 1
  hCR := fun h w => by simp [Matrix.map_one]
  hCC := fun h w => by simp [Matrix.map_one]
  hCV := fun h v => by simp [Matrix.map_one]
  hCH := by simp
  hΞC := fun j => j.elim0

/-! ### The induction step -/

section Step

variable {k r n' : ℕ} {Q₀ : QuadForm (𝓞 F) (k + 1)} {ρ : F} (S : AdelicSphereSetup Q₀ ρ) (hρ : ρ ≠ 0)
  (hQ : Q₀.Nondegenerate) (Ξ : Fin (r + 1) → Fin (k + 1) → F) (hΞ0 : S.ξ.1 = Ξ 0)
  (hperp : ∀ j : Fin r, bH (Q₀.map (algebraMap (𝓞 F) F)).hessian S.ξ.1 (Ξ j.succ) = 0)
  (D' : FrameTowerAlg S.C.Q' S.C.hQ' n' fun j : Fin r => S.complRat (Ξ j.succ))

/-- The archimedean part of the composite embedding. -/
def stepAlgInf : GInfSO D'.Q'' →* GInfSO Q₀ :=
  (MonoidHom.prodMap (MonoidHom.piMap S.iotaR) (MonoidHom.piMap S.iotaC)).comp D'.ιInf

/-- The finite part of the composite embedding. -/
def stepAlgFin : SOAf D'.Q'' →* SOAf Q₀ := S.iotaFin.comp D'.ιFin

theorem stepAlg_ι_apply (h : SOAdele D'.Q'') :
    MonoidHom.prodMap (stepAlgInf S Ξ D') (stepAlgFin S Ξ D') h = S.iota (MonoidHom.prodMap D'.ιInf D'.ιFin h) := rfl

include hΞ0 hperp in
theorem stepAlg_base : (Fin.cons S.ξA fun j => S.complA (frameA (fun j : Fin r => S.complRat (Ξ j.succ)) j) :
    Fin (r + 1) → AdeleSpace F (Fin (k + 1))) = frameA Ξ := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Fin.cons_zero, frameA, AdelicSphereSetup.ξA, hΞ0]
  · simp only [Fin.cons_succ, frameA]
    rw [S.complA_diagVec, S.Gc_mulVec_complRat (hperp j)]

include hρ hΞ0 hperp in
theorem stepAlg_fix (h : SOAdele D'.Q'') :
    MonoidHom.prodMap (stepAlgInf S Ξ D') (stepAlgFin S Ξ D') h • frameA Ξ = frameA Ξ := by
  rw [← stepAlg_base S Ξ hΞ0 hperp, stepAlg_ι_apply]
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · show S.iota _ • S.ξA = S.ξA
    exact S.iota_smul_ξA hρ _
  · show S.iota _ • S.complA _ = S.complA _
    rw [S.iota_smul_complA]
    exact congrArg S.complA (congrFun (D'.fix h) j)

theorem stepAlg_injective : Function.Injective (MonoidHom.prodMap (stepAlgInf S Ξ D') (stepAlgFin S Ξ D')) :=
  fun a b hab => D'.injective (S.iota_injective (by rwa [stepAlg_ι_apply, stepAlg_ι_apply] at hab))

/-- The tower stabilizer property for `FrameTowerAlg`, as needed by `stab_compose`. -/
theorem stepAlg_he (h : SOAdele S.C.Q') (z : AdeleSpace F (Fin k)) : S.complA (h • z) = S.iota h • S.complA z :=
  (S.iota_smul_complA h z).symm

include hρ hΞ0 hperp in
theorem stepAlg_stabΓ : ∀ γ ∈ GammaSOAdele Q₀, γ • frameA Ξ = frameA Ξ →
    ∃ h ∈ GammaSOAdele D'.Q'', MonoidHom.prodMap (stepAlgInf S Ξ D') (stepAlgFin S Ξ D') h = γ := by
  intro γ hγ hfix
  rw [← stepAlg_base S Ξ hΞ0 hperp] at hfix
  exact stab_compose (Γ := GammaSOAdele Q₀) (Γ₀ := GammaSOAdele S.C.Q') (Γ' := GammaSOAdele D'.Q'')
    S.complA (stepAlg_he S) S.complA_injective S.iota_injective (fun γ hγ hfix => S.exists_iota_gamma hρ hγ hfix)
    D'.stabΓ γ hγ hfix

include hρ hΞ0 hperp in
theorem stepAlg_stab : ∀ g : SOAdele Q₀, g • frameA Ξ = frameA Ξ →
    ∃ h, MonoidHom.prodMap (stepAlgInf S Ξ D') (stepAlgFin S Ξ D') h = g := by
  intro g hfix
  rw [← stepAlg_base S Ξ hΞ0 hperp] at hfix
  obtain ⟨h, -, e⟩ := stab_compose (Γ := ⊤) (Γ₀ := ⊤) (Γ' := ⊤) S.complA (stepAlg_he S) S.complA_injective
    S.iota_injective (fun γ _ hfix => (S.exists_iota_eq hρ hfix).imp fun h hh => ⟨trivial, hh⟩)
    (fun γ _ hfix => (D'.stab γ hfix).imp fun h hh => ⟨trivial, hh⟩) g trivial hfix
  exact ⟨h, e⟩

theorem stepAlg_gamma_mem : ∀ h ∈ GammaSOAdele D'.Q'',
    MonoidHom.prodMap (stepAlgInf S Ξ D') (stepAlgFin S Ξ D') h ∈ GammaSOAdele Q₀ := fun h hh => by
  rw [stepAlg_ι_apply]; exact S.iota_mem_gamma (D'.gamma_mem h hh)

theorem stepAlg_hCR (h : SOAdele D'.Q'') (w : {w : InfinitePlace F // w.IsReal}) :
    matR Q₀ (MonoidHom.prodMap (stepAlgInf S Ξ D') (stepAlgFin S Ξ D') h) w * (S.Gc * D'.Cm).map (σR w) =
      (S.Gc * D'.Cm).map (σR w) * matR D'.Q'' h w := by
  rw [stepAlg_ι_apply, Matrix.map_mul, ← Matrix.mul_assoc, S.matR_iota_mul_Gc, Matrix.mul_assoc, D'.hCR,
    Matrix.mul_assoc]

theorem stepAlg_hCC (h : SOAdele D'.Q'') (w : {w : InfinitePlace F // w.IsComplex}) :
    matC Q₀ (MonoidHom.prodMap (stepAlgInf S Ξ D') (stepAlgFin S Ξ D') h) w * (S.Gc * D'.Cm).map (σC w) =
      (S.Gc * D'.Cm).map (σC w) * matC D'.Q'' h w := by
  rw [stepAlg_ι_apply, Matrix.map_mul, ← Matrix.mul_assoc, S.matC_iota_mul_Gc, Matrix.mul_assoc, D'.hCC,
    Matrix.mul_assoc]

theorem stepAlg_hCV (h : SOAdele D'.Q'') (v : HeightOneSpectrum (𝓞 F)) :
    matV Q₀ (MonoidHom.prodMap (stepAlgInf S Ξ D') (stepAlgFin S Ξ D') h) v * (S.Gc * D'.Cm).map (σV v) =
      (S.Gc * D'.Cm).map (σV v) * matV D'.Q'' h v := by
  rw [stepAlg_ι_apply, Matrix.map_mul, ← Matrix.mul_assoc, S.matV_iota_mul_Gc, Matrix.mul_assoc, D'.hCV,
    Matrix.mul_assoc]

theorem stepAlg_hCH : (S.Gc * D'.Cm)ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian * (S.Gc * D'.Cm) =
    (D'.Q''.map (algebraMap (𝓞 F) F)).hessian := by
  have e : (S.Gc * D'.Cm)ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian * (S.Gc * D'.Cm) =
      D'.Cmᵀ * (S.Gcᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian * S.Gc) * D'.Cm := by
    rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  rw [e, S.Gc_hes, D'.hCH]

include hΞ0 hperp in
theorem stepAlg_hΞC (j : Fin (r + 1)) :
    ((S.Gc * D'.Cm)ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian) *ᵥ Ξ j = 0 := by
  have e : (S.Gc * D'.Cm)ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian =
      D'.Cmᵀ * (S.Gcᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian) := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc]
  refine Fin.cases ?_ (fun j => ?_) j
  · rw [e, ← Matrix.mulVec_mulVec, ← hΞ0, S.Gc_hes_ξ, Matrix.mulVec_zero]
  · have h1 : Ξ j.succ = S.Gc *ᵥ S.complRat (Ξ j.succ) := (S.Gc_mulVec_complRat (hperp j)).symm
    rw [h1, Matrix.mulVec_mulVec, e, Matrix.mul_assoc, S.Gc_hes]
    exact D'.hΞC j

include S hρ hΞ0 hperp D' in
/-- **The induction step**: algebraic data for the complement frame of $\xi_0$ give algebraic data for $\Xi$. -/
def FrameTowerAlg.step : FrameTowerAlg Q₀ hQ n' Ξ where
  Q'' := D'.Q''
  hQ'' := D'.hQ''
  ιInf := stepAlgInf S Ξ D'
  ιFin := stepAlgFin S Ξ D'
  measurable_ιInf := ((measurable_pi_iff.mpr fun w => (S.measurable_iotaR w).comp (measurable_pi_apply w)).comp
      measurable_fst).prodMk
    ((measurable_pi_iff.mpr fun w => (S.measurable_iotaC w).comp (measurable_pi_apply w)).comp
      measurable_snd) |>.comp D'.measurable_ιInf
  continuous_ιInf := (((continuous_pi fun w => (S.continuous_iotaR w).comp (continuous_apply w)).comp
      continuous_fst).prodMk
    ((continuous_pi fun w => (S.continuous_iotaC w).comp (continuous_apply w)).comp continuous_snd)).comp
      D'.continuous_ιInf
  fix := stepAlg_fix S hρ Ξ hΞ0 hperp D'
  injective := stepAlg_injective S Ξ D'
  gamma_mem := stepAlg_gamma_mem S Ξ D'
  stabΓ := stepAlg_stabΓ S hρ Ξ hΞ0 hperp D'
  stab := stepAlg_stab S hρ Ξ hΞ0 hperp D'
  Cm := S.Gc * D'.Cm
  hCR := stepAlg_hCR S Ξ D'
  hCC := stepAlg_hCC S Ξ D'
  hCV := stepAlg_hCV S Ξ D'
  hCH := stepAlg_hCH S Ξ D'
  hΞC := stepAlg_hΞC S Ξ hΞ0 hperp D'

end Step

/-- **Existence of the algebraic frame data** for every orthogonal rational frame with nonzero values, $n'\ge1$. -/
theorem nonempty_frameTowerAlg {n' : ℕ} (hn' : 1 ≤ n') :
    ∀ (r : ℕ) {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate) (_hN : N = r + n')
      (Ξ : Fin r → Fin N → F)
      (_horth : ∀ i j, i ≠ j → bH (Q₀.map (algebraMap (𝓞 F) F)).hessian (Ξ i) (Ξ j) = 0)
      (_hne : ∀ j, qF Q₀ (Ξ j) ≠ 0), Nonempty (FrameTowerAlg Q₀ hQ n' Ξ) := by
  intro r
  induction r with
  | zero =>
    intro N Q₀ hQ hN Ξ _ _
    obtain rfl : N = n' := by omega
    exact ⟨FrameTowerAlg.base Q₀ hQ Ξ⟩
  | succ r ih =>
    intro N Q₀ hQ hN Ξ horth hne
    obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨r + n', by omega⟩
    have hρ : qF Q₀ (Ξ 0) ≠ 0 := hne 0
    obtain ⟨Cc⟩ := exists_sphereComplement Q₀ hQ (Ξ 0) hρ
    have hdet : (Q₀.map (algebraMap (𝓞 F) F)).hessian.det ≠ 0 := by
      rw [Siegel.hessian_map_NF, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ
    have hx₀ : qH (Q₀.map (algebraMap (𝓞 F) F)).hessian (Ξ 0) ≠ 0 := by
      rw [qH_hessian]; exact mul_ne_zero two_ne_zero hρ
    obtain ⟨w, hw, hworth⟩ := exists_orth_anisotropic (H := (Q₀.map (algebraMap (𝓞 F) F)).hessian)
      (hessian_transpose Q₀) two_ne_zero hdet (by omega) hx₀
    obtain ⟨S, hS⟩ : ∃ S : AdelicSphereSetup Q₀ (qF Q₀ (Ξ 0)), S.ξ.1 = Ξ 0 :=
      ⟨⟨⟨Ξ 0, rfl⟩, Cc, w, hw, hworth⟩, rfl⟩
    have hperp : ∀ j : Fin r, bH (Q₀.map (algebraMap (𝓞 F) F)).hessian S.ξ.1 (Ξ j.succ) = 0 := by
      rw [hS]; exact bH_cols_zero horth
    have horth' : ∀ i j : Fin r, i ≠ j →
        bH (S.C.Q'.map (algebraMap (𝓞 F) F)).hessian (S.complRat (Ξ i.succ)) (S.complRat (Ξ j.succ)) = 0 := by
      intro i j hij
      rw [S.bH_complRat (hperp i) (hperp j)]
      exact horth _ _ (fun h => hij (Fin.succ_injective _ h))
    have hne' : ∀ j : Fin r, qF S.C.Q' (S.complRat (Ξ j.succ)) ≠ 0 := fun j => by
      rw [S.qF_complRat (hperp j)]; exact hne _
    obtain ⟨D'⟩ := ih S.C.Q' S.C.hQ' (by omega) (fun j => S.complRat (Ξ j.succ)) horth' hne'
    exact ⟨FrameTowerAlg.step S hρ hQ Ξ hS hperp D'⟩

/-- **Transport of the algebraic data along an invertible change of basis of the frame.** -/
def FrameTowerAlg.transport {N r n' : ℕ} {Q₀ : QuadForm (𝓞 F) N} {hQ : Q₀.Nondegenerate} {Ξ : Fin r → Fin N → F}
    (D : FrameTowerAlg Q₀ hQ n' Ξ) (M : Matrix (Fin r) (Fin r) F) (hM : IsUnit M.det) :
    FrameTowerAlg Q₀ hQ n' (frameMul Ξ M) where
  Q'' := D.Q''
  hQ'' := D.hQ''
  ιInf := D.ιInf
  ιFin := D.ιFin
  measurable_ιInf := D.measurable_ιInf
  continuous_ιInf := D.continuous_ιInf
  fix := fun h => by rw [← frameMulA_frameA, smul_frameMulA, D.fix]
  injective := D.injective
  gamma_mem := D.gamma_mem
  stabΓ := fun γ hγ hfix => by
    refine D.stabΓ γ hγ ?_
    have e : frameA Ξ = frameMulA M⁻¹ (frameA (frameMul Ξ M)) := by
      rw [← frameMulA_frameA, frameMulA_mul, Matrix.mul_nonsing_inv _ hM, frameMulA_one]
    rw [e, smul_frameMulA, hfix]
  stab := fun g hfix => by
    refine D.stab g ?_
    have e : frameA Ξ = frameMulA M⁻¹ (frameA (frameMul Ξ M)) := by
      rw [← frameMulA_frameA, frameMulA_mul, Matrix.mul_nonsing_inv _ hM, frameMulA_one]
    rw [e, smul_frameMulA, hfix]
  Cm := D.Cm
  hCR := D.hCR
  hCC := D.hCC
  hCV := D.hCV
  hCH := D.hCH
  hΞC := fun j => by
    have e : frameMul Ξ M j = ∑ l, M l j • Ξ l := by
      funext i; simp [frameMul, Finset.sum_apply]
    rw [e, Matrix.mulVec_sum]
    exact Finset.sum_eq_zero fun l _ => by rw [Matrix.mulVec_smul, D.hΞC l, smul_zero]

/-- **Every rational frame of a nondegenerate form has algebraic frame data**, for every complement rank $n'\ge1$. -/
theorem nonempty_frameTowerAlg_ratFrame {r n' : ℕ} (hn' : 1 ≤ n') (Q₀ : QuadForm (𝓞 F) (r + n'))
    (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (X : RatFrame Q₀ T₀) :
    Nonempty (FrameTowerAlg Q₀ hQ n' (cols X.1)) := by
  obtain ⟨P, dg, hP, hdg, hPd⟩ := QuadFormsKB.Tamagawa.Frames.exists_diag_global T₀ hT
  set f := algebraMap (𝓞 F) F with hf
  set PF : Matrix (Fin r) (Fin r) F := P.map f with hPF
  have hdet : IsUnit PF.det := by
    rw [isUnit_iff_ne_zero, hPF, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hP
  have hG : (Q₀.map f).compMat (X.1 * PF) = (QuadForm.diag dg).map f := by
    rw [← QuadFormsKB.QuadForm.compMat_mul, X.2, hPF, QuadFormsKB.QuadForm.map_compMat, hPd]
  have hcols : frameMul (cols X.1) PF = cols (X.1 * PF) := by
    funext j i
    simp only [frameMul, cols, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hdiag : ∀ i j, i ≠ j →
      bH (Q₀.map f).hessian (cols (X.1 * PF) i) (cols (X.1 * PF) j) = 0 := by
    intro i j hij
    have h1 := congrArg (fun G => QuadForm.hessian G i j) hG
    simp only [QuadFormsKB.QuadForm.hessian_compMat] at h1
    have h2 := QuadFormsKB.QuadForm.transpose_mul_mul_apply (Q₀.map f).hessian (X.1 * PF) i j
    unfold bH
    rw [show (cols (X.1 * PF) i) = fun l => (X.1 * PF) l i from rfl, show (cols (X.1 * PF) j) =
      fun l => (X.1 * PF) l j from rfl, ← h2, h1, QuadFormsKB.QuadForm.hessian_map]
    simp [QuadFormsKB.Tamagawa.Frames.hessian_diag, Matrix.diagonal_apply, hij]
  have hne : ∀ j, qF Q₀ (cols (X.1 * PF) j) ≠ 0 := by
    intro j
    have := QuadFormsKB.Tamagawa.Frames.eval_col_of_compMat (Q₀.map f) hG j
    show (Q₀.map f).eval (fun i => (X.1 * PF) i j) ≠ 0
    rw [this]
    simp only [QuadForm.map, QuadForm.diag, Matrix.map_apply]
    simp only [Matrix.diagonal_apply_eq]
    exact (map_ne_zero_iff f RingOfIntegers.coe_injective).mpr (hdg j)
  obtain ⟨D⟩ := nonempty_frameTowerAlg hn' r Q₀ hQ rfl (cols (X.1 * PF)) hdiag hne
  have hinv : IsUnit PF⁻¹.det := Matrix.isUnit_nonsing_inv_det _ hdet
  have e : frameMul (cols (X.1 * PF)) PF⁻¹ = cols X.1 := by
    rw [← hcols, frameMul_mul, Matrix.mul_nonsing_inv _ hdet, frameMul_one]
  exact ⟨e ▸ D.transport PF⁻¹ hinv⟩

end QuadFormsKB.Tamagawa.Indefinite
