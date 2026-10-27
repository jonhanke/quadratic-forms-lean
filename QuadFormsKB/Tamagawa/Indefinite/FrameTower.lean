/-
# The adelic frame coordinates and Weil's fibration for frames

**Layer:** number fields, adeles. $F$ a number field, $Q_0$ nondegenerate over $\mathcal O_F$ in $N$ variables (any
signature), $\Xi = (\xi_0, \dots, \xi_{r-1})$ an **orthogonal** rational frame ($B(\xi_i,\xi_j) = 0$ for $i\ne j$,
$Q_0(\xi_j)\ne0$), $N = r + n'$, $n'\ge3$. A **`FrameTower Q₀ hQ n' Ξ`** is:

* the complement form $Q''$ over $\mathcal O_F$ in $n'$ variables, the embedding $\iota = \iota_\infty\times\iota_f :
  SO(Q'')(\mathbb A)\to SO(V)(\mathbb A)$ and the complement matrix $C\in F^{N\times n'}$ ($Q_0\circ C = Q''$, $C\perp\Xi$,
  $\iota(h)\,C = C\,h$ at every place, so $\iota(h) = g\,\mathrm{diag}(1_r, h)\,g^{-1}$ for $g = [\Xi\mid C]$);
* orbit coordinates $T\times SO(Q'')(\mathbb A)\cong SO(V)(\mathbb A)$ of the adelic frame $\Xi$ (`OrbitCoord`) with
  **Weil's fibration** $\mu_{SO(V)} = \mathrm{coord}_*(\sigma\otimes\mu_{SO(Q'')})$ for the Tamagawa measures (constant $1$);
* the stabilizer of $\Xi$ is $\iota(SO(Q'')(\mathbb A))$, and in $SO(V)(F)$ it is $\iota(SO(Q'')(F))$.

**`nonempty_frameTower`**: a tower exists. *Proof:* induction on $r$; the step (`FrameTower.step`) is the adelic
sphere fibration (`sphereFibration`) for $\xi_0$, the remaining columns lie in $\xi_0^\perp$, i.e. in the complement
(`complRat`), and the coordinates and fibrations compose (`OrbitCoord.compose`, `fib_compose`, `stab_compose`). No new
local measure theory. Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.Indefinite.FrameSetup
import QuadFormsKB.Tamagawa.Indefinite.FrameCoordCompose

open MeasureTheory Set Matrix MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F]

/-- The adelic frame of a rational frame (columns embedded diagonally). -/
abbrev frameA {N r : ℕ} (Ξ : Fin r → Fin N → F) : Fin r → AdeleSpace F (Fin N) := fun j => diagVec F (Fin N) (Ξ j)

/-- **The adelic frame coordinates** of an orthogonal rational frame $\Xi$ of $Q_0$, with complement of rank $n'$.
Fields: `Q''`, `hQ''`, `ιInf`, `ιFin`, `T`, `mT`, `σ`, `τ`, `C`, `sFinite`, `fib`, `gamma_mem`, `stabΓ`, `stab`, `Cm`,
`hCR`, `hCC`, `hCV`, `hCH`, `hΞC`. -/
structure FrameTower {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate) (n' : ℕ) {r : ℕ}
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
  /-- The parameter space. -/
  T : Type
  [mT : MeasurableSpace T]
  /-- The measure on the parameter space (Weil's quotient measure). -/
  σ : Measure T
  /-- The parametrization of the orbit of $\Xi$. -/
  τ : T → Fin r → AdeleSpace F (Fin N)
  /-- The orbit coordinates. -/
  C : OrbitCoord (MonoidHom.prodMap ιInf ιFin) τ (frameA Ξ)
  sFinite : SFinite σ
  /-- Weil's fibration for frames, constant $1$. -/
  fib : muTam Q₀ hQ 1 = (σ.prod (muTam Q'' hQ'' 1)).map C.coord
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

attribute [instance] FrameTower.mT

/-- Orbit coordinates transported along equalities of the embedding and of the base point (same `coord`). -/
def _root_.QuadFormsKB.Tamagawa.Measure.Weil.OrbitCoord.congr {G H T Y : Type*} [Group G] [Group H]
    [MeasurableSpace G] [MeasurableSpace H] [MeasurableSpace T] [MulAction G Y] {ι ι' : H →* G} {τ : T → Y}
    {y₀ y₀' : Y} (C : OrbitCoord ι τ y₀) (hι : ι = ι') (hy : y₀ = y₀') : OrbitCoord ι' τ y₀' where
  coord := C.coord
  mul x h h' := hι ▸ C.mul x h h'
  orbit x h := hy ▸ C.orbit x h

/-- **The empty tower** ($r = 0$). -/
def FrameTower.base {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate) (Ξ : Fin 0 → Fin N → F) :
    FrameTower Q₀ hQ N Ξ where
  Q'' := Q₀
  hQ'' := hQ
  ιInf := MonoidHom.id _
  ιFin := MonoidHom.id _
  measurable_ιInf := measurable_id
  continuous_ιInf := continuous_id
  T := Unit
  σ := Measure.dirac ()
  τ := fun _ => Fin.elim0
  C :=
    { coord := MeasurableEquiv.punitProd
      mul := fun _ _ _ => rfl
      orbit := fun _ _ => funext fun j => j.elim0 }
  sFinite := inferInstance
  fib := by
    have := fib_base (V := Fin 0 → AdeleSpace F (Fin N)) (muTam Q₀ hQ 1)
    rw [one_smul] at this
    exact this
  gamma_mem := fun h hh => hh
  stabΓ := fun γ hγ _ => ⟨γ, hγ, rfl⟩
  stab := fun g _ => ⟨g, rfl⟩
  Cm := 1
  hCR := fun h w => by simp [Matrix.map_one]
  hCC := fun h w => by simp [Matrix.map_one]
  hCV := fun h v => by simp [Matrix.map_one]
  hCH := by simp
  hΞC := fun j => j.elim0

/-- The frame lies in the complement of its first column. -/
theorem bH_cols_zero {N r : ℕ} {Q₀ : QuadForm (𝓞 F) N} {Ξ : Fin (r + 1) → Fin N → F}
    (horth : ∀ i j, i ≠ j → bH (Q₀.map (algebraMap (𝓞 F) F)).hessian (Ξ i) (Ξ j) = 0) (j : Fin r) :
    bH (Q₀.map (algebraMap (𝓞 F) F)).hessian (Ξ 0) (Ξ j.succ) = 0 :=
  horth 0 j.succ (Fin.succ_ne_zero j).symm

/-! ### The induction step -/

section Step

variable {k r n' : ℕ} {Q₀ : QuadForm (𝓞 F) (k + 1)} {ρ : F} (S : AdelicSphereSetup Q₀ ρ) (hρ : ρ ≠ 0)
  (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k) (Ξ : Fin (r + 1) → Fin (k + 1) → F) (hΞ0 : S.ξ.1 = Ξ 0)
  (hperp : ∀ j : Fin r, bH (Q₀.map (algebraMap (𝓞 F) F)).hessian S.ξ.1 (Ξ j.succ) = 0)
  (D' : FrameTower S.C.Q' S.C.hQ' n' fun j : Fin r => S.complRat (Ξ j.succ))

/-- The sphere coordinates of a setup, as `OrbitCoord`. -/
def _root_.QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereSetup.orbitCoord :
    OrbitCoord S.iota (Subtype.val : adelicSphere Q₀ ρ → AdeleSpace F (Fin (k + 1))) S.ξA :=
  ⟨S.coordEquiv hρ, fun x h h' => S.coordFun_mul hρ x h h', fun x h => S.coordFun_inv_smul hρ (x, h)⟩

theorem step_he (h : SOAdele S.C.Q') (z : AdeleSpace F (Fin k)) : S.complA (h • z) = S.iota h • S.complA z :=
  (S.iota_smul_complA h z).symm

include hΞ0 hperp in
theorem step_base : (Fin.cons S.ξA fun j => S.complA (frameA (fun j : Fin r => S.complRat (Ξ j.succ)) j) :
    Fin (r + 1) → AdeleSpace F (Fin (k + 1))) = frameA Ξ := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Fin.cons_zero, frameA, AdelicSphereSetup.ξA, hΞ0]
  · simp only [Fin.cons_succ, frameA]
    rw [S.complA_diagVec, S.Gc_mulVec_complRat (hperp j)]

/-- The archimedean part of the composite embedding. -/
def stepInf : GInfSO D'.Q'' →* GInfSO Q₀ :=
  (MonoidHom.prodMap (MonoidHom.piMap S.iotaR) (MonoidHom.piMap S.iotaC)).comp D'.ιInf

/-- The finite part of the composite embedding. -/
def stepFin : SOAf D'.Q'' →* SOAf Q₀ := S.iotaFin.comp D'.ιFin

theorem step_ι : S.iota.comp (MonoidHom.prodMap D'.ιInf D'.ιFin) = MonoidHom.prodMap (stepInf S Ξ D') (stepFin S Ξ D') :=
  MonoidHom.ext fun _ => rfl

theorem step_ι_apply (h : SOAdele D'.Q'') :
    MonoidHom.prodMap (stepInf S Ξ D') (stepFin S Ξ D') h = S.iota (MonoidHom.prodMap D'.ιInf D'.ιFin h) := rfl

/-- The composite orbit coordinates. -/
def stepC : OrbitCoord (MonoidHom.prodMap (stepInf S Ξ D') (stepFin S Ξ D'))
    (composeτ (S.orbitCoord hρ) S.complA D'.τ) (frameA Ξ) :=
  ((S.orbitCoord hρ).compose S.complA (step_he S) D'.C).congr (step_ι S Ξ D') (step_base S Ξ hΞ0 hperp)

theorem step_fib :
    haveI : SFinite (S.sphereMeasure hρ hQ hk) := (S.sphereFibration hρ hQ hk).sFinite
    haveI := D'.sFinite
    muTam Q₀ hQ 1 = (((S.sphereMeasure hρ hQ hk).prod D'.σ).prod (muTam D'.Q'' D'.hQ'' 1)).map
      (stepC S hρ Ξ hΞ0 hperp D').coord := by
  haveI : SFinite (S.sphereMeasure hρ hQ hk) := (S.sphereFibration hρ hQ hk).sFinite
  haveI := D'.sFinite
  have h0 : muTam Q₀ hQ 1 = (1 : ℝ≥0∞) • ((S.sphereMeasure hρ hQ hk).prod (muTam S.C.Q' S.C.hQ' 1)).map
      (S.orbitCoord hρ).coord := by rw [one_smul]; exact (S.sphereFibration hρ hQ hk).fib
  have h1 : muTam S.C.Q' S.C.hQ' 1 = (1 : ℝ≥0∞) • (D'.σ.prod (muTam D'.Q'' D'.hQ'' 1)).map D'.C.coord := by
    rw [one_smul]; exact D'.fib
  have := fib_compose (S.orbitCoord hρ) S.complA (step_he S) D'.C h0 h1
  rwa [one_mul, one_smul] at this

include hρ hΞ0 hperp in
theorem step_stabΓ : ∀ γ ∈ GammaSOAdele Q₀, γ • frameA Ξ = frameA Ξ →
    ∃ h ∈ GammaSOAdele D'.Q'', MonoidHom.prodMap (stepInf S Ξ D') (stepFin S Ξ D') h = γ := by
  intro γ hγ hfix
  rw [← step_base S Ξ hΞ0 hperp] at hfix
  exact stab_compose (Γ := GammaSOAdele Q₀) (Γ₀ := GammaSOAdele S.C.Q') (Γ' := GammaSOAdele D'.Q'')
    S.complA (step_he S) S.complA_injective S.iota_injective (fun γ hγ hfix => S.exists_iota_gamma hρ hγ hfix)
    D'.stabΓ γ hγ hfix

include hρ hΞ0 hperp in
theorem step_stab : ∀ g : SOAdele Q₀, g • frameA Ξ = frameA Ξ →
    ∃ h, MonoidHom.prodMap (stepInf S Ξ D') (stepFin S Ξ D') h = g := by
  intro g hfix
  rw [← step_base S Ξ hΞ0 hperp] at hfix
  obtain ⟨h, -, e⟩ := stab_compose (Γ := ⊤) (Γ₀ := ⊤) (Γ' := ⊤) S.complA (step_he S) S.complA_injective
    S.iota_injective (fun γ _ hfix => (S.exists_iota_eq hρ hfix).imp fun h hh => ⟨trivial, hh⟩)
    (fun γ _ hfix => (D'.stab γ hfix).imp fun h hh => ⟨trivial, hh⟩) g trivial hfix
  exact ⟨h, e⟩

theorem step_gamma_mem : ∀ h ∈ GammaSOAdele D'.Q'',
    MonoidHom.prodMap (stepInf S Ξ D') (stepFin S Ξ D') h ∈ GammaSOAdele Q₀ := fun h hh => by
  rw [step_ι_apply]; exact S.iota_mem_gamma (D'.gamma_mem h hh)

theorem step_hCR (h : SOAdele D'.Q'') (w : {w : InfinitePlace F // w.IsReal}) :
    matR Q₀ (MonoidHom.prodMap (stepInf S Ξ D') (stepFin S Ξ D') h) w * (S.Gc * D'.Cm).map (σR w) =
      (S.Gc * D'.Cm).map (σR w) * matR D'.Q'' h w := by
  rw [step_ι_apply, Matrix.map_mul, ← Matrix.mul_assoc, S.matR_iota_mul_Gc, Matrix.mul_assoc, D'.hCR,
    Matrix.mul_assoc]

theorem step_hCC (h : SOAdele D'.Q'') (w : {w : InfinitePlace F // w.IsComplex}) :
    matC Q₀ (MonoidHom.prodMap (stepInf S Ξ D') (stepFin S Ξ D') h) w * (S.Gc * D'.Cm).map (σC w) =
      (S.Gc * D'.Cm).map (σC w) * matC D'.Q'' h w := by
  rw [step_ι_apply, Matrix.map_mul, ← Matrix.mul_assoc, S.matC_iota_mul_Gc, Matrix.mul_assoc, D'.hCC,
    Matrix.mul_assoc]

theorem step_hCV (h : SOAdele D'.Q'') (v : HeightOneSpectrum (𝓞 F)) :
    matV Q₀ (MonoidHom.prodMap (stepInf S Ξ D') (stepFin S Ξ D') h) v * (S.Gc * D'.Cm).map (σV v) =
      (S.Gc * D'.Cm).map (σV v) * matV D'.Q'' h v := by
  rw [step_ι_apply, Matrix.map_mul, ← Matrix.mul_assoc, S.matV_iota_mul_Gc, Matrix.mul_assoc, D'.hCV,
    Matrix.mul_assoc]

theorem step_hCH : (S.Gc * D'.Cm)ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian * (S.Gc * D'.Cm) =
    (D'.Q''.map (algebraMap (𝓞 F) F)).hessian := by
  have e : (S.Gc * D'.Cm)ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian * (S.Gc * D'.Cm) =
      D'.Cmᵀ * (S.Gcᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian * S.Gc) * D'.Cm := by
    rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  rw [e, S.Gc_hes, D'.hCH]

include hΞ0 hperp in
theorem step_hΞC (j : Fin (r + 1)) : ((S.Gc * D'.Cm)ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian) *ᵥ Ξ j = 0 := by
  have e : (S.Gc * D'.Cm)ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian =
      D'.Cmᵀ * (S.Gcᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian) := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc]
  refine Fin.cases ?_ (fun j => ?_) j
  · rw [e, ← Matrix.mulVec_mulVec, ← hΞ0, S.Gc_hes_ξ, Matrix.mulVec_zero]
  · have h1 : Ξ j.succ = S.Gc *ᵥ S.complRat (Ξ j.succ) := (S.Gc_mulVec_complRat (hperp j)).symm
    rw [h1, Matrix.mulVec_mulVec, e, Matrix.mul_assoc, S.Gc_hes]
    exact D'.hΞC j

include S hρ hk hΞ0 hperp D' in
/-- **The induction step**: a tower for the complement frame of $\xi_0$ gives a tower for $\Xi$. -/
def FrameTower.step : FrameTower Q₀ hQ n' Ξ :=
  haveI : SFinite (S.sphereMeasure hρ hQ hk) := (S.sphereFibration hρ hQ hk).sFinite
  haveI := D'.sFinite
  { Q'' := D'.Q''
    hQ'' := D'.hQ''
    ιInf := stepInf S Ξ D'
    ιFin := stepFin S Ξ D'
    measurable_ιInf := ((measurable_pi_iff.mpr fun w => (S.measurable_iotaR w).comp (measurable_pi_apply w)).comp
        measurable_fst).prodMk
      ((measurable_pi_iff.mpr fun w => (S.measurable_iotaC w).comp (measurable_pi_apply w)).comp
        measurable_snd) |>.comp D'.measurable_ιInf
    continuous_ιInf := (((continuous_pi fun w => (S.continuous_iotaR w).comp (continuous_apply w)).comp
        continuous_fst).prodMk
      ((continuous_pi fun w => (S.continuous_iotaC w).comp (continuous_apply w)).comp continuous_snd)).comp
        D'.continuous_ιInf
    T := adelicSphere Q₀ ρ × D'.T
    σ := (S.sphereMeasure hρ hQ hk).prod D'.σ
    τ := composeτ (S.orbitCoord hρ) S.complA D'.τ
    C := stepC S hρ Ξ hΞ0 hperp D'
    sFinite := inferInstance
    fib := step_fib S hρ hQ hk Ξ hΞ0 hperp D'
    gamma_mem := step_gamma_mem S Ξ D'
    stabΓ := step_stabΓ S hρ Ξ hΞ0 hperp D'
    stab := step_stab S hρ Ξ hΞ0 hperp D'
    Cm := S.Gc * D'.Cm
    hCR := step_hCR S Ξ D'
    hCC := step_hCC S Ξ D'
    hCV := step_hCV S Ξ D'
    hCH := step_hCH S Ξ D'
    hΞC := step_hΞC S Ξ hΞ0 hperp D' }

end Step

/-- **Existence of the frame coordinates** for every orthogonal rational frame with nonzero values, $n'\ge3$. -/
theorem nonempty_frameTower {n' : ℕ} (hn' : 3 ≤ n') :
    ∀ (r : ℕ) {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate) (_hN : N = r + n')
      (Ξ : Fin r → Fin N → F)
      (_horth : ∀ i j, i ≠ j → bH (Q₀.map (algebraMap (𝓞 F) F)).hessian (Ξ i) (Ξ j) = 0)
      (_hne : ∀ j, qF Q₀ (Ξ j) ≠ 0), Nonempty (FrameTower Q₀ hQ n' Ξ) := by
  intro r
  induction r with
  | zero =>
    intro N Q₀ hQ hN Ξ _ _
    obtain rfl : N = n' := by omega
    exact ⟨FrameTower.base Q₀ hQ Ξ⟩
  | succ r ih =>
    intro N Q₀ hQ hN Ξ horth hne
    obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨r + n', by omega⟩
    have hk : 3 ≤ k := by omega
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
    exact ⟨FrameTower.step S hρ hQ hk Ξ hS hperp D'⟩

end QuadFormsKB.Tamagawa.Indefinite
