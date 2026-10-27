/-
# The global count of representations for frames of corank zero

**Layer:** number fields, adeles. $F$ a number field, $Q_0$ nondegenerate over $\mathcal O_F$ in $N$ variables (any
signature), $L = \mathcal O_F^N$, $T_0$ nondegenerate over $\mathcal O_F$ in $N$ variables, $\Xi$ a rational frame of $T_0$
($Q_0\circ\Xi = T_0$). A representation of $T_0$ by a class $M_i$ is an isometry, and the stabilizer of a square frame in
$SO(V)$ is trivial at every place (`eq_one_of_smul_ratAT_zero`, `eq_one_of_smul_ratFT_zero`).

**The two orbits.** The rational frames of $T_0$ form one $O(V)(F)$-orbit ($X\Xi^{-1}\in O(V)(F)$), hence **two**
$SO(V)(F)$-orbits, distinguished by $\det X = \pm\det\Xi$ (`det_ratFrame_eq_or`). The frames with $\det X = \det\Xi$ are the
**proper frames** relative to $\Xi$ (`PropFrame`, one $SO(V)(F)$-orbit: `exists_smul_eq_propFrame`), and the representations
split accordingly: $n(M_i, T_0) = n^+_\Xi(M_i,T_0) + n^+_{\Xi'}(M_i,T_0)$ for any rational frame $\Xi'$ with
$\det\Xi' = -\det\Xi$ (`repCount_eq_add`; such $\Xi' = s\Xi$ exist, $s$ a rational reflection: `exists_ratFrame_det_neg`).

**Proves** **`tsum_repCountP_eq`**: $\sum_in^+_\Xi(M_i,T_0)$ is the number of $SO(\hat L)$-orbits of integral finite-adelic
frames in $SO(V)(\mathbb A_f)\,\Xi_f$ (`FinOrbit`). *Proof:* as `tsum_repCount_eq` (corank one), with the proper frames in
place of all rational frames: the theta integral over a fundamental domain of $SO(V)(F)$ computed classically
(`lintegral_theta_eq` with the trivial archimedean fibration over the $SO(V)(F_\infty)$-orbit of $\Xi_\infty$) and adelically
(`lintegral_sphere_unfold`, transitive on the proper frames, trivial stabilizer). No Tamagawa number is used.
-/
import QuadFormsKB.Tamagawa.Indefinite.SiegelCorankOne

open MeasureTheory Set Matrix MulAction
open scoped ENNReal Pointwise

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### Trivial stabilizers of square frames -/

section StabilizerHelpers

variable (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) N)

/-- The Gram matrix of a rational frame (corank zero): $X^{\mathsf T}HX = H_{T_0}$. -/
theorem gram_ratFrame_zero (X : RatFrame Q₀ T₀) :
    X.1ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian * X.1 = (T₀.map (algebraMap (𝓞 F) F)).hessian := by
  rw [← QuadForm.hessian_compMat, X.2]

/-- A square rational frame of a nondegenerate form stays invertible under every embedding. -/
theorem det_map_ne_zero_zero (hT : T₀.Nondegenerate) (X : RatFrame Q₀ T₀) {K : Type*} [Field K] (σ : F →+* K) :
    (X.1.map σ).det ≠ 0 := by
  intro h0
  have e : (X.1.map σ)ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian.map σ * X.1.map σ =
      ((T₀.map (algebraMap (𝓞 F) F)).hessian).map σ := by
    rw [← gram_ratFrame_zero Q₀ T₀ X, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have h1 : (((T₀.map (algebraMap (𝓞 F) F)).hessian).map σ).det = 0 := by
    rw [← e, Matrix.det_mul, h0, mul_zero]
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h1
  exact (map_ne_zero σ).mpr (det_hessian_map_ne_zero T₀ hT) h1

/-- If $gX = X$ with $X$ invertible then $g = 1$. -/
theorem eq_one_of_mul_frame_zero {K : Type*} [Field K] (g X : Matrix (Fin N) (Fin N) K) (hX : X.det ≠ 0)
    (h : g * X = X) : g = 1 := by
  have hu : IsUnit X.det := isUnit_iff_ne_zero.mpr hX
  calc g = g * (X * X⁻¹) := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = (g * X) * X⁻¹ := by rw [Matrix.mul_assoc]
    _ = 1 := by rw [h, Matrix.mul_nonsing_inv _ hu]

variable {Q₀ T₀}

variable {X : RatFrame Q₀ T₀}

theorem matR_mul_frame_zero {g : SOAdele Q₀} (h : g • ratFrameA Q₀ T₀ X = ratFrameA Q₀ T₀ X)
    (w : {w : InfinitePlace F // w.IsReal}) : matR Q₀ g w * X.1.map (σR w) = X.1.map (σR w) := by
  refine Matrix.ext fun i j => ?_
  have h1 : (matR Q₀ g w *ᵥ fun k => σR w (X.1 k j)) i = σR w (X.1 i j) := by
    have := congrArg (fun y : Fin N → AdeleSpace F (Fin N) => (y j i).1.1 w) h
    simpa [ratFrameA, smul_def, adeleSMul, diag_real] using this
  simpa only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.map_apply] using h1

theorem matC_mul_frame_zero {g : SOAdele Q₀} (h : g • ratFrameA Q₀ T₀ X = ratFrameA Q₀ T₀ X)
    (w : {w : InfinitePlace F // w.IsComplex}) : matC Q₀ g w * X.1.map (σC w) = X.1.map (σC w) := by
  refine Matrix.ext fun i j => ?_
  have h1 : (matC Q₀ g w *ᵥ fun k => σC w (X.1 k j)) i = σC w (X.1 i j) := by
    have := congrArg (fun y : Fin N → AdeleSpace F (Fin N) => (y j i).1.2 w) h
    simpa [ratFrameA, smul_def, adeleSMul, diag_complex] using this
  simpa only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.map_apply] using h1

theorem matV_mul_frame_zero {g : SOAdele Q₀} (h : g • ratFrameA Q₀ T₀ X = ratFrameA Q₀ T₀ X)
    (v : HeightOneSpectrum (𝓞 F)) : matV Q₀ g v * X.1.map (σV v) = X.1.map (σV v) := by
  refine Matrix.ext fun i j => ?_
  have h1 : (matV Q₀ g v *ᵥ fun k => σV v (X.1 k j)) i = σV v (X.1 i j) := by
    exact congrArg (fun y : Fin N → AdeleSpace F (Fin N) => (y j i).2 v) h
  simpa only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.map_apply] using h1

end StabilizerHelpers

section Stabilizer

variable (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) N) (hT : T₀.Nondegenerate) (X : RatFrame Q₀ T₀)

include hT in
/-- **The stabilizer of the adelic image of a rational frame of corank zero is trivial**: at every place the local
component of $g$ fixes the $N$ columns of the invertible matrix $X$. -/
theorem eq_one_of_smul_ratFrameA_zero {g : SOAdele Q₀} (h : g • ratFrameA Q₀ T₀ X = ratFrameA Q₀ T₀ X) : g = 1 := by
  refine Prod.ext (Prod.ext (funext fun w => ?_) (funext fun w => ?_)) ?_
  · have e : matR Q₀ g w = 1 :=
      eq_one_of_mul_frame_zero _ _ (det_map_ne_zero_zero Q₀ T₀ hT X (σR w)) (matR_mul_frame_zero h w)
    exact Subtype.ext (Units.ext e)
  · have e : matC Q₀ g w = 1 :=
      eq_one_of_mul_frame_zero _ _ (det_map_ne_zero_zero Q₀ T₀ hT X (σC w)) (matC_mul_frame_zero h w)
    exact Subtype.ext (Units.ext e)
  · apply Subtype.ext
    apply RestrictedProduct.ext
    intro v
    have e : matV Q₀ g v = 1 :=
      eq_one_of_mul_frame_zero _ _ (det_map_ne_zero_zero Q₀ T₀ hT X (σV v)) (matV_mul_frame_zero h v)
    exact Subtype.ext (Units.ext e)

include hT in
/-- $a\cdot X_\infty = X_\infty$ implies $a = 1$ in $SO(V)(F_\infty)$ (corank zero). -/
theorem eq_one_of_smul_ratAT_zero {a : GInfSO Q₀} (h : a • ratAT Q₀ T₀ X = ratAT Q₀ T₀ X) : a = 1 := by
  have h1 : ((a, 1) : SOAdele Q₀) • ratFrameA Q₀ T₀ X = ratFrameA Q₀ T₀ X := by
    refine splitFrame_injective ?_
    rw [splitFrame_smul]
    show ((a, 1) : SOAdele Q₀) • (ratAT Q₀ T₀ X, ratFT Q₀ T₀ X) = (ratAT Q₀ T₀ X, ratFT Q₀ T₀ X)
    rw [prod_smul_def, h, one_smul]
  exact congrArg Prod.fst (eq_one_of_smul_ratFrameA_zero Q₀ T₀ hT X h1)

include hT in
/-- $b\cdot X_f = X_f$ implies $b = 1$ in $SO(V)(\mathbb A_f)$ (corank zero). -/
theorem eq_one_of_smul_ratFT_zero {b : SOAf Q₀} (h : b • ratFT Q₀ T₀ X = ratFT Q₀ T₀ X) : b = 1 := by
  have h1 : (((1 : GInfSO Q₀), b) : SOAdele Q₀) • ratFrameA Q₀ T₀ X = ratFrameA Q₀ T₀ X := by
    refine splitFrame_injective ?_
    rw [splitFrame_smul]
    show (((1 : GInfSO Q₀), b) : SOAdele Q₀) • (ratAT Q₀ T₀ X, ratFT Q₀ T₀ X) = (ratAT Q₀ T₀ X, ratFT Q₀ T₀ X)
    rw [prod_smul_def, h, one_smul]
  exact congrArg Prod.snd (eq_one_of_smul_ratFrameA_zero Q₀ T₀ hT X h1)

end Stabilizer

/-! ### Proper frames -/

section Proper

variable (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) N) (Ξ : RatFrame Q₀ T₀)

/-- $\det(\gamma X) = \det X$ for $\gamma\in SO(V)(F)$. -/
theorem det_smul_ratFrame (γ : GammaSOAdele Q₀) (X : RatFrame Q₀ T₀) : (γ • X).1.det = X.1.det := by
  have h : (ratMat Q₀ ((gammaEquiv Q₀).symm γ)).det = 1 := ((gammaEquiv Q₀).symm γ).2
  rw [ratFrame_smul_val, Matrix.det_mul, h, one_mul]

/-- **The proper rational frames relative to $\Xi$**: the rational frames $X$ of $T_0$ with $\det X = \det\Xi$ (the
$SO(V)(F)$-orbit of $\Xi$). -/
def PropFrame : Type := {X : RatFrame Q₀ T₀ // X.1.det = Ξ.1.det}

instance : Countable (PropFrame Q₀ T₀ Ξ) := by unfold PropFrame; infer_instance

/-- $SO(V)(F)$ acts on the proper frames. -/
instance instMulActionPropFrame : MulAction (GammaSOAdele Q₀) (PropFrame Q₀ T₀ Ξ) where
  smul γ X := ⟨γ • X.1, (det_smul_ratFrame Q₀ T₀ γ X.1).trans X.2⟩
  one_smul X := Subtype.ext (one_smul _ X.1)
  mul_smul γ δ X := Subtype.ext (mul_smul γ δ X.1)

theorem propFrame_smul_val (γ : GammaSOAdele Q₀) (X : PropFrame Q₀ T₀ Ξ) : (γ • X).1 = γ • X.1 := rfl

/-- The base point $\Xi$ of the proper frames. -/
def propBase : PropFrame Q₀ T₀ Ξ := ⟨Ξ, rfl⟩

/-- **$SO(V)(F)$ is transitive on the proper frames**: $X = \gamma\Xi$ with $\gamma = X\Xi^{-1}\in SO(V)(F)$. -/
theorem exists_smul_eq_propFrame (hT : T₀.Nondegenerate) (X : PropFrame Q₀ T₀ Ξ) :
    ∃ γ : GammaSOAdele Q₀, γ • propBase Q₀ T₀ Ξ = X := by
  have hΞ : Ξ.1.det ≠ 0 := by simpa using det_map_ne_zero_zero Q₀ T₀ hT Ξ (RingHom.id F)
  have hu : IsUnit Ξ.1.det := isUnit_iff_ne_zero.mpr hΞ
  set M : Matrix (Fin N) (Fin N) F := X.1.1 * Ξ.1⁻¹ with hMdef
  have hMΞ : M * Ξ.1 = X.1.1 := by
    rw [hMdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
  have hdet : M.det = 1 := by
    have h1 := congrArg Matrix.det hMΞ
    rw [Matrix.det_mul, X.2] at h1
    exact mul_right_cancel₀ hΞ (by rw [h1, one_mul])
  let φ : GL (Fin N) F := Matrix.nonsingInvUnit M (by rw [hdet]; exact isUnit_one)
  have hφO : φ ∈ orthGroup (Q₀.map (algebraMap (𝓞 F) F)) F := by
    refine mem_orthGroup_of_eval _ fun z => ?_
    have hz' : Ξ.1 *ᵥ (Ξ.1⁻¹ *ᵥ z) = z := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
    have hM : M *ᵥ z = X.1.1 *ᵥ (Ξ.1⁻¹ *ᵥ z) := by
      calc M *ᵥ z = M *ᵥ (Ξ.1 *ᵥ (Ξ.1⁻¹ *ᵥ z)) := by rw [hz']
        _ = (M * Ξ.1) *ᵥ (Ξ.1⁻¹ *ᵥ z) := by rw [Matrix.mulVec_mulVec]
        _ = _ := by rw [hMΞ]
    have e1 : (Q₀.map (algebraMap (𝓞 F) F)).eval (X.1.1 *ᵥ (Ξ.1⁻¹ *ᵥ z)) =
        (T₀.map (algebraMap (𝓞 F) F)).eval (Ξ.1⁻¹ *ᵥ z) := by
      rw [← QuadForm.eval_compMat, X.1.2]
    have e2 : (Q₀.map (algebraMap (𝓞 F) F)).eval (Ξ.1 *ᵥ (Ξ.1⁻¹ *ᵥ z)) =
        (T₀.map (algebraMap (𝓞 F) F)).eval (Ξ.1⁻¹ *ᵥ z) := by
      rw [← QuadForm.eval_compMat, Ξ.2]
    show (Q₀.map (algebraMap (𝓞 F) F)).eval (M *ᵥ z) = _
    rw [hM, e1, ← e2, hz']
  refine ⟨gammaEquiv Q₀ ⟨⟨φ, hφO⟩, hdet⟩, Subtype.ext (Subtype.ext ?_)⟩
  show ((gammaEquiv Q₀ ⟨⟨φ, hφO⟩, hdet⟩ • Ξ : RatFrame Q₀ T₀)).1 = X.1.1
  rw [ratFrame_smul_val, MulEquiv.symm_apply_apply]
  exact hMΞ

/-- The archimedean embedding of the proper frames. -/
def propAT (X : PropFrame Q₀ T₀ Ξ) : Fin N → VInf F N := ratAT Q₀ T₀ X.1

/-- The finite embedding of the proper frames. -/
def propFT (X : PropFrame Q₀ T₀ Ξ) : Fin N → Fin N → AF := ratFT Q₀ T₀ X.1

theorem propAT_smul (γ : GammaSOAdele Q₀) (X : PropFrame Q₀ T₀ Ξ) :
    propAT Q₀ T₀ Ξ (γ • X) = (γ : SOAdele Q₀).1 • propAT Q₀ T₀ Ξ X := ratAT_smul Q₀ T₀ γ X.1

theorem propFT_smul (γ : GammaSOAdele Q₀) (X : PropFrame Q₀ T₀ Ξ) :
    propFT Q₀ T₀ Ξ (γ • X) = (γ : SOAdele Q₀).2 • propFT Q₀ T₀ Ξ X := ratFT_smul Q₀ T₀ γ X.1

/-- **The proper representations of $T_0$ by the class $i$**: $R^+_\Xi(M_i,T_0) = \{X\in M_i^N : Q\circ X = T_0,\
\det X = \det\Xi\}$, embedded in $V_\infty^N$; a $\Gamma_i$-set. -/
def repsP (i : DC Q₀) : SubMulAction (unitGroup Q₀ i) (Fin N → VInf F N) :=
  repSet (propAT_smul Q₀ T₀ Ξ) (propFT_smul Q₀ T₀ Ξ) (latHatT_stable Q₀ (r := N)) (dcRep Q₀ i)

/-- **The number of classes of proper representations modulo units**:
$n^+_\Xi(M_i, T_0) = \#(\Gamma_i\backslash R^+_\Xi(M_i, T_0))\in[0,\infty]$. Parameters: `Q₀`, `T₀`, `Ξ`, `i`. -/
def repCountP (i : DC Q₀) : ℝ≥0∞ :=
  ∑' _q : orbitRel.Quotient (unitGroup Q₀ i) (repsP Q₀ T₀ Ξ i), (1 : ℝ≥0∞)

end Proper

/-! ### The global count for proper frames -/

section Count

variable (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) N) (hT : T₀.Nondegenerate)
  (Ξ : RatFrame Q₀ T₀)

/-! ### The archimedean fibration with trivial stabilizers -/

/-- The archimedean orbit of $\Xi_\infty$. -/
abbrev orbInfZero : Set (Fin N → VInf F N) := Set.range fun a : GInfSO Q₀ => a • ratAT Q₀ T₀ Ξ

include hT in
theorem subsingleton_stabilizer_orbInfZero {y : Fin N → VInf F N} (hy : y ∈ orbInfZero Q₀ T₀ Ξ) :
    Subsingleton (stabilizer (GInfSO Q₀) y) := by
  obtain ⟨a, rfl⟩ := hy
  refine ⟨fun s t => Subtype.ext ?_⟩
  have key : ∀ s : stabilizer (GInfSO Q₀) (a • ratAT Q₀ T₀ Ξ), (s : GInfSO Q₀) = 1 := by
    intro s
    have hs : (s : GInfSO Q₀) • a • ratAT Q₀ T₀ Ξ = a • ratAT Q₀ T₀ Ξ := s.2
    have h1 : (a⁻¹ * s * a) • ratAT Q₀ T₀ Ξ = ratAT Q₀ T₀ Ξ := by
      rw [mul_smul, mul_smul, hs, inv_smul_smul]
    have h2 := eq_one_of_smul_ratAT_zero Q₀ T₀ hT Ξ h1
    have : (s : GInfSO Q₀) = a * (a⁻¹ * s * a) * a⁻¹ := by group
    rw [this, h2]; group
  rw [key s, key t]

/-- The orbit coordinates at $y = a_y\Xi_\infty$: $(x, h)\mapsto a_yx$. -/
def archCoordTrivZero (y : Fin N → VInf F N) (hy : y ∈ orbInfZero Q₀ T₀ Ξ) :
    OrbitCoord (stabilizer (GInfSO Q₀) y).subtype (fun x : GInfSO Q₀ => x⁻¹ • ratAT Q₀ T₀ Ξ) y :=
  haveI := subsingleton_stabilizer_orbInfZero Q₀ T₀ hT Ξ hy
  { coord := (prodSubsingletonEquiv _ _ 1).trans (MeasurableEquiv.mulLeft hy.choose)
    mul := fun x h h' => by
      have : h' = 1 := Subsingleton.elim _ _
      subst this
      simp
    orbit := fun x h => by
      show (hy.choose * x)⁻¹ • y = x⁻¹ • ratAT Q₀ T₀ Ξ
      have e : hy.choose • ratAT Q₀ T₀ Ξ = y := hy.choose_spec
      calc (hy.choose * x)⁻¹ • y = (hy.choose * x)⁻¹ • hy.choose • ratAT Q₀ T₀ Ξ := by rw [e]
        _ = x⁻¹ • ratAT Q₀ T₀ Ξ := by rw [_root_.mul_inv_rev, mul_smul, inv_smul_smul] }

open Classical in
/-- **The archimedean fibration with trivial stabilizers** over the orbit of $\Xi_\infty$: $T = SO(V)(F_\infty)$ with
$\mu_\infty$, $\tau(x) = x^{-1}\Xi_\infty$, stabilizer measures $\delta_1$, constant $1$. -/
def archFibTrivZero :
    ArchFibration (muArchTamSO Q₀ hQ) (orbInfZero Q₀ T₀ Ξ) (muArchTamSO Q₀ hQ)
      (fun x : GInfSO Q₀ => x⁻¹ • ratAT Q₀ T₀ Ξ) 1 where
  μH y := if y ∈ orbInfZero Q₀ T₀ Ξ then Measure.dirac 1 else 0
  coord y hy := archCoordTrivZero Q₀ T₀ hT Ξ y hy
  sigmaFinite y := by
    split_ifs <;> infer_instance
  leftInv y := by
    split_ifs with hy
    · haveI := subsingleton_stabilizer_orbInfZero Q₀ T₀ hT Ξ hy
      exact isMulLeftInvariant_dirac_of_subsingleton
    · exact ⟨fun g => by simp⟩
  fib y hy := by
    rw [if_pos hy, one_smul, Measure.prod_dirac, Measure.map_map (archCoordTrivZero Q₀ T₀ hT Ξ y hy).coord.measurable
      measurable_prodMk_right]
    have : ((archCoordTrivZero Q₀ T₀ hT Ξ y hy).coord ∘ fun x : GInfSO Q₀ => (x, (1 : stabilizer (GInfSO Q₀) y))) =
        fun x => hy.choose * x := rfl
    rw [this, map_mul_left_eq_self]

include hT in
/-- Every proper representation of $T_0$ lies in the archimedean orbit of $\Xi_\infty$. -/
theorem ratAT_mem_orbInfZero (X : PropFrame Q₀ T₀ Ξ) : propAT Q₀ T₀ Ξ X ∈ orbInfZero Q₀ T₀ Ξ := by
  obtain ⟨γ, rfl⟩ := exists_smul_eq_propFrame Q₀ T₀ Ξ hT X
  exact ⟨(γ : SOAdele Q₀).1, (propAT_smul Q₀ T₀ Ξ γ (propBase Q₀ T₀ Ξ)).symm⟩

/-- **With trivial stabilizers the measure of representations is the count**: `repMeasureT` for `archFibTrivZero` is
$n(M_i,T_0)$. -/
theorem repMeasureP_archFibTrivZero (i : DC Q₀) :
    repMeasureOf (unitGroup Q₀ i) (repsP Q₀ T₀ Ξ i) (archFibTrivZero Q₀ hQ T₀ hT Ξ).μH = repCountP Q₀ T₀ Ξ i := by
  classical
  unfold repMeasureOf repCountP
  refine tsum_congr fun q => ?_
  set y := ((q.out : repsP Q₀ T₀ Ξ i) : Fin N → VInf F N) with hydef
  have hy : y ∈ orbInfZero Q₀ T₀ Ξ := by
    obtain ⟨X, -, hX⟩ := (q.out : repsP Q₀ T₀ Ξ i).2
    rw [hydef, ← hX]
    exact ratAT_mem_orbInfZero Q₀ T₀ hT Ξ X
  haveI := subsingleton_stabilizer_orbInfZero Q₀ T₀ hT Ξ hy
  haveI : Countable (stabArith (unitGroup Q₀ i) y) := by
    haveI : Subsingleton (stabArith (unitGroup Q₀ i) y) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    infer_instance
  rw [covolume_of_subsingleton]
  show (if y ∈ orbInfZero Q₀ T₀ Ξ then Measure.dirac 1 else 0) univ = 1
  rw [if_pos hy, Measure.dirac_apply_of_mem (mem_univ _)]

/-! ### The adelic side -/

/-- The adelic orbit coordinates with trivial stabilizer: $T = SO(V)(\mathbb A)$, $\tau(x) = x^{-1}\Xi$. -/
def adelicCoordTrivZero :
    OrbitCoord (1 : Unit →* SOAdele Q₀) (fun x : SOAdele Q₀ => x⁻¹ • ratFrameA Q₀ T₀ Ξ) (ratFrameA Q₀ T₀ Ξ) where
  coord := prodSubsingletonEquiv _ _ ()
  mul x h h' := by
    show x = (1 : Unit →* SOAdele Q₀) h' * x
    rw [MonoidHom.one_apply, one_mul]
  orbit _ _ := rfl

/-- The test function along $x\mapsto x^{-1}\Xi$ splits into archimedean and finite parts. -/
theorem testFnT_inv_smulZero (Φ : (Fin N → VInf F N) → ℝ≥0∞) (x : SOAdele Q₀) :
    testFnT Φ (x⁻¹ • ratFrameA Q₀ T₀ Ξ) =
      Φ (x.1⁻¹ • ratAT Q₀ T₀ Ξ) * (latHatT F N N).indicator 1 (x.2⁻¹ • ratFT Q₀ T₀ Ξ) := by
  rw [testFnT, splitFrame_smul]
  rfl

theorem measurable_latSetZero :
    MeasurableSet {b : SOAf Q₀ | b⁻¹ • ratFT Q₀ T₀ Ξ ∈ latHatT F N N} :=
  (red_isOpen_latSet (n' := 0) Q₀ (ratFT Q₀ T₀ Ξ)).measurableSet

theorem indicator_latSet_eqZero :
    (fun b : SOAf Q₀ => (latHatT F N N).indicator (1 : (Fin N → Fin N → AF) → ℝ≥0∞) (b⁻¹ • ratFT Q₀ T₀ Ξ)) =
      {b : SOAf Q₀ | b⁻¹ • ratFT Q₀ T₀ Ξ ∈ latHatT F N N}.indicator 1 := by
  funext b; rfl

set_option maxHeartbeats 800000 in
include hT in
/-- **The theta integral with trivial stabilizers, adelically**: for every left-invariant $\mu_f$ and every fundamental
domain $E$ of $SO(V)(F)$ for $\mu_\infty\times\mu_f$,
$$\int_E\theta = \int\Phi(a^{-1}\Xi_\infty)\,d\mu_\infty(a)\cdot\mu_f\{b : b^{-1}\Xi_f\in\hat L^r\}.$$ -/
theorem lintegral_theta_trivZero {μB : Measure (SOAf Q₀)} [SFinite μB] [μB.IsMulLeftInvariant]
    {Φ : (Fin N → VInf F N) → ℝ≥0∞} (hΦ : Measurable Φ) {E : Set (SOAdele Q₀)}
    (hE : IsFundamentalDomain (GammaSOAdele Q₀) E ((muArchTamSO Q₀ hQ).prod μB)) :
    ∫⁻ g in E, thetaFn (propAT Q₀ T₀ Ξ) (propFT Q₀ T₀ Ξ) Φ (latHatT F N N) g ∂(muArchTamSO Q₀ hQ).prod μB =
      (∫⁻ a, Φ (a⁻¹ • ratAT Q₀ T₀ Ξ) ∂muArchTamSO Q₀ hQ) *
        μB {b : SOAf Q₀ | b⁻¹ • ratFT Q₀ T₀ Ξ ∈ latHatT F N N} := by
  have := countable_GammaSOAdele Q₀
  haveI : MeasurableConstSMul (⊤ : Subgroup Unit) Unit := ⟨fun _ => Subsingleton.measurable⟩
  haveI : SMulInvariantMeasure (⊤ : Subgroup Unit) Unit (Measure.dirac ()) :=
    ⟨fun c s _ => by
      have : (fun x : Unit => c • x) = id := funext fun _ => Subsingleton.elim _ _
      rw [this]; rfl⟩
  set μ := (muArchTamSO Q₀ hQ).prod μB with hμ
  have hιΓ : ∀ h ∈ (⊤ : Subgroup Unit), (1 : Unit →* SOAdele Q₀) h ∈ GammaSOAdele Q₀ := fun h _ => by
    rw [MonoidHom.one_apply]; exact one_mem _
  have hfix : ∀ (h : Unit) (hh : h ∈ (⊤ : Subgroup Unit)),
      (⟨(1 : Unit →* SOAdele Q₀) h, hιΓ h hh⟩ : GammaSOAdele Q₀) • propBase Q₀ T₀ Ξ = propBase Q₀ T₀ Ξ := by
    intro h hh
    have e : (⟨(1 : Unit →* SOAdele Q₀) h, hιΓ h hh⟩ : GammaSOAdele Q₀) = 1 :=
      Subtype.ext rfl
    rw [e, one_smul]
  have hstab : ∀ γ : GammaSOAdele Q₀, γ • propBase Q₀ T₀ Ξ = propBase Q₀ T₀ Ξ → ∃ h ∈ (⊤ : Subgroup Unit), (1 : Unit →* SOAdele Q₀) h = γ := by
    intro γ hγ
    have h1 : (γ : SOAdele Q₀) • ratFrameA Q₀ T₀ Ξ = ratFrameA Q₀ T₀ Ξ := by rw [← ratFrameA_smul]; exact congrArg (ratFrameA Q₀ T₀) (congrArg Subtype.val hγ)
    exact ⟨(), trivial, by rw [MonoidHom.one_apply, eq_one_of_smul_ratFrameA_zero Q₀ T₀ hT Ξ h1]⟩
  have hDHx : ∀ h : Unit, ∃! γ : (⊤ : Subgroup Unit), γ • h ∈ (univ : Set Unit) :=
    fun h => ⟨1, mem_univ _, fun γ _ => Subtype.ext (Subsingleton.elim _ _)⟩
  have hfib : μ = (1 : ℝ≥0∞) • (μ.prod (Measure.dirac ())).map (adelicCoordTrivZero Q₀ T₀ Ξ).coord := by
    rw [one_smul, Measure.prod_dirac, Measure.map_map (adelicCoordTrivZero Q₀ T₀ Ξ).coord.measurable
      measurable_prodMk_right]
    exact (Measure.map_id).symm
  have hmeas : Measurable fun x : SOAdele Q₀ => testFnT Φ (x⁻¹ • ratFrameA Q₀ T₀ Ξ) := by
    simp_rw [testFnT_inv_smulZero]
    refine Measurable.mul ((measurable_GInf_inv_smulT Q₀ hΦ _).comp measurable_fst) ?_
    have : (fun x : SOAdele Q₀ => (latHatT F N N).indicator (1 : (Fin N → Fin N → AF) → ℝ≥0∞) (x.2⁻¹ • ratFT Q₀ T₀ Ξ)) =
        fun x => {b : SOAf Q₀ | b⁻¹ • ratFT Q₀ T₀ Ξ ∈ latHatT F N N}.indicator 1 x.2 := by
      funext x; rfl
    rw [this]
    exact (measurable_one.indicator (measurable_latSetZero Q₀ T₀ Ξ)).comp measurable_snd
  have key := lintegral_sphere_unfold (Γ := GammaSOAdele Q₀) (μ := μ) (ΓH := (⊤ : Subgroup Unit))
    (μH := Measure.dirac ()) (fun η : PropFrame Q₀ T₀ Ξ => ratFrameA Q₀ T₀ η.1)
    (fun γ η => ratFrameA_smul Q₀ T₀ γ η.1) (propBase Q₀ T₀ Ξ)
    (fun η => exists_smul_eq_propFrame Q₀ T₀ Ξ hT η)
    (1 : Unit →* SOAdele Q₀) μ (fun x => x⁻¹ • ratFrameA Q₀ T₀ Ξ) (adelicCoordTrivZero Q₀ T₀ Ξ) hιΓ hfix hstab
    (DH := univ) MeasurableSet.univ hDHx 1 hfib hE (testFnT Φ) hmeas
  rw [covolume_of_subsingleton, measure_univ, one_mul, one_mul] at key
  have hθ : ∀ g : SOAdele Q₀, thetaFn (propAT Q₀ T₀ Ξ) (propFT Q₀ T₀ Ξ) Φ (latHatT F N N) g =
      ∑' η : PropFrame Q₀ T₀ Ξ, testFnT Φ (g⁻¹ • ratFrameA Q₀ T₀ η.1) := fun g => by
    unfold thetaFn
    refine tsum_congr fun η => ?_
    rw [testFnT, splitFrame_smul]
    rfl
  simp_rw [hθ]
  rw [key]
  simp_rw [testFnT_inv_smulZero]
  have hf : AEMeasurable (fun a : GInfSO Q₀ => Φ (a⁻¹ • ratAT Q₀ T₀ Ξ)) (muArchTamSO Q₀ hQ) :=
    (measurable_GInf_inv_smulT Q₀ hΦ _).aemeasurable
  have hg : AEMeasurable (fun b : SOAf Q₀ => (latHatT F N N).indicator (1 : (Fin N → Fin N → AF) → ℝ≥0∞) (b⁻¹ • ratFT Q₀ T₀ Ξ))
      μB := by
    rw [indicator_latSet_eqZero]
    exact (measurable_one.indicator (measurable_latSetZero Q₀ T₀ Ξ)).aemeasurable
  rw [hμ, lintegral_prod_mul hf hg, indicator_latSet_eqZero, lintegral_indicator_one (measurable_latSetZero Q₀ T₀ Ξ)]

set_option maxHeartbeats 1600000 in
include hT in
/-- **The integral finite-adelic frames are a disjoint union of translates of $SO(\hat L)$**:
$\mu_f\{b : b^{-1}\Xi_f\in\hat L^r\} = \#\mathrm{FinOrbit}\cdot\mu_f(SO(\hat L))$ (trivial stabilizer of $\Xi_f$). -/
theorem measure_latSet_eqZero (μB : Measure (SOAf Q₀)) [μB.IsMulLeftInvariant] :
    μB {b : SOAf Q₀ | b⁻¹ • ratFT Q₀ T₀ Ξ ∈ latHatT F N N} =
      (∑' _O : FinOrbit (n' := 0) Q₀ T₀ Ξ, (1 : ℝ≥0∞)) * μB (KSO Q₀ : Set (SOAf Q₀)) := by
  set S : FinOrbit (n' := 0) Q₀ T₀ Ξ → Set (SOAf Q₀) := fun O => {b : SOAf Q₀ | b⁻¹ • ratFT Q₀ T₀ Ξ ∈
    (KSO Q₀ : Set (SOAf Q₀)) • ({finOrbitRep (n' := 0) Q₀ T₀ Ξ O • ratFT Q₀ T₀ Ξ} : Set (Fin N → Fin N → AF))} with hS
  have hU : {b : SOAf Q₀ | b⁻¹ • ratFT Q₀ T₀ Ξ ∈ latHatT F N N} = ⋃ O, S O := by
    ext b
    simp only [mem_setOf_eq, mem_iUnion, hS]
    constructor
    · intro h
      refine ⟨Quotient.mk (finOrbitSetoid (n' := 0) Q₀ T₀ Ξ) ⟨b⁻¹, h⟩, ?_⟩
      exact Quotient.mk_out (s := finOrbitSetoid (n' := 0) Q₀ T₀ Ξ)
        (⟨b⁻¹, h⟩ : {b : SOAf Q₀ // b • ratFT Q₀ T₀ Ξ ∈ latHatT F N N})
    · rintro ⟨O, k, hk, y, hy, hz⟩
      rw [Set.mem_singleton_iff] at hy
      subst hy
      rw [← hz]
      exact (latHatT_stable Q₀ k hk _).2 (orb_rep_mem (n' := 0) Q₀ T₀ Ξ O)
  have hdisj : Pairwise (Function.onFun Disjoint S) := fun i j hij =>
    (orb_disjoint (n' := 0) Q₀ T₀ Ξ hij).preimage (fun b : SOAf Q₀ => b⁻¹ • ratFT Q₀ T₀ Ξ)
  have hmeas : ∀ O, MeasurableSet (S O) := fun O =>
    (orb_isOpen_orbitSet (n' := 0) Q₀ (ratFT Q₀ T₀ Ξ) (finOrbitRep (n' := 0) Q₀ T₀ Ξ O • ratFT Q₀ T₀ Ξ)).measurableSet
  have hSO : ∀ O, S O = (finOrbitRep (n' := 0) Q₀ T₀ Ξ O)⁻¹ • (KSO Q₀ : Set (SOAf Q₀)) := by
    intro O
    set g := finOrbitRep (n' := 0) Q₀ T₀ Ξ O
    ext b
    simp only [hS, mem_setOf_eq]
    constructor
    · rintro ⟨k, hk, y, hy, hz⟩
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have h1 : (b * k * g) • ratFT Q₀ T₀ Ξ = ratFT Q₀ T₀ Ξ := by
        have hz' : k • g • ratFT Q₀ T₀ Ξ = b⁻¹ • ratFT Q₀ T₀ Ξ := hz
        rw [mul_smul, mul_smul, hz', smul_inv_smul]
      have h2 := eq_one_of_smul_ratFT_zero Q₀ T₀ hT Ξ h1
      refine Set.mem_smul_set.2 ⟨k⁻¹, (KSO Q₀).inv_mem hk, ?_⟩
      show g⁻¹ * k⁻¹ = b
      have : b = (b * k * g) * g⁻¹ * k⁻¹ := by group
      rw [this, h2]; group
    · intro hb
      obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.1 hb
      refine ⟨k⁻¹, (KSO Q₀).inv_mem hk, g • ratFT Q₀ T₀ Ξ, rfl, ?_⟩
      show k⁻¹ • g • ratFT Q₀ T₀ Ξ = (g⁻¹ * k)⁻¹ • ratFT Q₀ T₀ Ξ
      rw [_root_.mul_inv_rev, inv_inv, mul_smul]
  rw [hU, measure_iUnion hdisj hmeas, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun O => ?_
  rw [hSO, measure_smul, one_mul]


include hQ hT in
/-- **The global count** (corank zero, proper frames): the number of classes of proper representations of $T_0$ over the
genus of $L$ is the number of $SO(\hat L)$-orbits of integral finite-adelic frames in $SO(V)(\mathbb A_f)\,\Xi_f$:
$$\sum_in^+_\Xi(M_i, T_0) = \#\mathrm{FinOrbit}(\Xi).$$ -/
theorem tsum_repCountP_eq :
    ∑' i, repCountP Q₀ T₀ Ξ i = ∑' _O : FinOrbit (n' := 0) Q₀ T₀ Ξ, (1 : ℝ≥0∞) := by
  classical
  have := countable_GammaSOAdele Q₀
  have := discreteTopology_GammaSOAdele Q₀
  obtain ⟨E, hE⟩ := exists_measurableSet_forall_existsUnique_smul_mem (GammaSOAdele Q₀)
  have hEf : IsFundamentalDomain (GammaSOAdele Q₀) E ((muArchTamSO Q₀ hQ).prod (muFinK Q₀)) :=
    IsFundamentalDomain.mk' hE.1.nullMeasurableSet hE.2
  -- a compact neighbourhood of `1` and the test function
  haveI : (muArchTamSO Q₀ hQ).IsHaarMeasure := by
    have := LerayArch.isHaarMeasure_muArchLeray (QRe Q₀) (QCx Q₀) (gramDetR_QRe_ne_zero Q₀ hQ)
      (gramDetC_QCx_ne_zero Q₀ hQ)
    unfold muArchTamSO LerayArch.muArchNF
    rw [ofReal_smul_eq]
    exact Measure.IsHaarMeasure.nnreal_smul _ (Real.toNNReal_pos.mpr (mul_pos (Real.rpow_pos_of_pos (abs_pos.mpr
      (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero F))) _) cxWeil_pos)).ne'
  obtain ⟨U, hUc, hU1⟩ := exists_compact_mem_nhds (1 : GInfSO Q₀)
  have hU0 : muArchTamSO Q₀ hQ U ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hU1).ne'
  have hUt : muArchTamSO Q₀ hQ U ≠ ⊤ := hUc.measure_lt_top.ne
  set orbMap : GInfSO Q₀ → Fin N → VInf F N := fun a => a⁻¹ • ratAT Q₀ T₀ Ξ with horbMap
  have hcont : Continuous orbMap :=
    (continuous_GInf_smulT Q₀).comp (continuous_inv.prodMk continuous_const)
  haveI : OpensMeasurableSpace (Fin N → VInf F N) := Pi.opensMeasurableSpace
  have hSm : MeasurableSet (orbMap '' U) := (hUc.image hcont).isClosed.measurableSet
  set Φ : (Fin N → VInf F N) → ℝ≥0∞ := (orbMap '' U).indicator 1 with hΦdef
  have hΦ : Measurable Φ := measurable_one.indicator hSm
  have hΦU : ∀ a, Φ (orbMap a) = U.indicator 1 a := by
    intro a
    by_cases ha : a ∈ U
    · rw [Set.indicator_of_mem ha, hΦdef, Set.indicator_of_mem (Set.mem_image_of_mem _ ha)]; rfl
    · rw [Set.indicator_of_notMem ha, hΦdef, Set.indicator_of_notMem]
      rintro ⟨u, hu, hua⟩
      have h1 : (u * a⁻¹) • ratAT Q₀ T₀ Ξ = ratAT Q₀ T₀ Ξ := by
        have : u⁻¹ • ratAT Q₀ T₀ Ξ = a⁻¹ • ratAT Q₀ T₀ Ξ := hua
        rw [mul_smul, ← this, smul_inv_smul]
      have h2 := eq_one_of_smul_ratAT_zero Q₀ T₀ hT Ξ h1
      have : u = a := by
        have := congrArg (· * a) h2
        simpa using this
      exact ha (this ▸ hu)
  have hI : ∫⁻ a, Φ (orbMap a) ∂muArchTamSO Q₀ hQ = muArchTamSO Q₀ hQ U := by
    simp_rw [hΦU]
    exact lintegral_indicator_one hUc.measurableSet
  -- the two computations
  have h1 := lintegral_theta_eq (Γ := GammaSOAdele Q₀) (KSO Q₀) (isOpen_KSO Q₀).measurableSet (dcRep Q₀)
    (dcRep_cov Q₀) (fun i j γ hγ k hk k' hk' h => dcRep_disj Q₀ i j γ hγ k hk k' hk' h)
    (fun i γ hγ h1 => GammaSOAdele_injA Q₀ γ hγ.1 h1)
    (fun i => (exists_fd_levelGroup Q₀ (dcRep Q₀ i)).choose)
    (fun i => (exists_fd_levelGroup Q₀ (dcRep Q₀ i)).choose_spec.1)
    (fun i => (exists_fd_levelGroup Q₀ (dcRep Q₀ i)).choose_spec.2)
    (muArchTamSO Q₀ hQ) (muFinK Q₀) (propAT_smul Q₀ T₀ Ξ) (propFT_smul Q₀ T₀ Ξ)
    (fun a b h => Subtype.ext (ratAT_injective Q₀ T₀ h))
    (latHatT_stable Q₀) (archFibTrivZero Q₀ hQ T₀ hT Ξ) (ratAT_mem_orbInfZero Q₀ T₀ hT Ξ)
    (fun i y => exists_fd_stabArithT Q₀ (dcRep Q₀ i) y) Φ
    (measurable_GInf_inv_smulT Q₀ hΦ) (measurable_GInf_inv_smulT Q₀ hΦ _) hEf
  have h2 := lintegral_theta_trivZero Q₀ hQ T₀ hT Ξ hΦ hEf
  rw [measure_latSet_eqZero Q₀ T₀ hT Ξ, muFinK_KSO, mul_one] at h2
  rw [h2, muFinK_KSO] at h1
  simp only [one_mul, mul_one] at h1
  have hsum : (∑' i, repMeasureOf (levelGroup (GammaSOAdele Q₀) (KSO Q₀) (dcRep Q₀ i))
      (repSet (propAT_smul Q₀ T₀ Ξ) (propFT_smul Q₀ T₀ Ξ) (latHatT_stable Q₀) (dcRep Q₀ i))
      (archFibTrivZero Q₀ hQ T₀ hT Ξ).μH) = ∑' i, repCountP Q₀ T₀ Ξ i :=
    tsum_congr fun i => repMeasureP_archFibTrivZero Q₀ hQ T₀ hT Ξ i
  rw [hsum] at h1
  change (∫⁻ a, Φ (orbMap a) ∂muArchTamSO Q₀ hQ) * _ = _ * ∫⁻ a, Φ (orbMap a) ∂muArchTamSO Q₀ hQ at h1
  rw [hI, mul_comm] at h1
  exact ((ENNReal.mul_left_inj hU0 hUt).mp h1).symm

end Count

/-! ### Splitting the representations by the determinant -/

section Split

variable (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) N) (i : DC Q₀)

/-- The proper representations are representations. -/
def repsPIncl (Ξ : RatFrame Q₀ T₀) (y : repsP Q₀ T₀ Ξ i) : repsT Q₀ T₀ i :=
  ⟨y.1, by obtain ⟨η, hη, h⟩ := y.2; exact ⟨η.1, hη, h⟩⟩

theorem repsPIncl_smul (Ξ : RatFrame Q₀ T₀) (g : unitGroup Q₀ i) (y : repsP Q₀ T₀ Ξ i) :
    repsPIncl Q₀ T₀ i Ξ (g • y) = g • repsPIncl Q₀ T₀ i Ξ y := Subtype.ext rfl

/-- The induced map on classes modulo units. -/
def quotIncl (Ξ : RatFrame Q₀ T₀) :
    orbitRel.Quotient (unitGroup Q₀ i) (repsP Q₀ T₀ Ξ i) → orbitRel.Quotient (unitGroup Q₀ i) (repsT Q₀ T₀ i) :=
  Quotient.map' (repsPIncl Q₀ T₀ i Ξ) (fun a b h => by
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
    exact MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ⟨g, by rw [← repsPIncl_smul, hg]⟩))

/-- Units preserve the determinant of a frame. -/
theorem det_eq_of_smul_ratAT (g : unitGroup Q₀ i) (X X' : RatFrame Q₀ T₀)
    (h : (g : GInfSO Q₀) • ratAT Q₀ T₀ X = ratAT Q₀ T₀ X') : X'.1.det = X.1.det := by
  obtain ⟨γ, hγ, hγg⟩ := Subgroup.mem_map.mp g.2
  have h1 : ratAT Q₀ T₀ ((⟨γ, hγ.1⟩ : GammaSOAdele Q₀) • X) = ratAT Q₀ T₀ X' := by
    rw [ratAT_smul, ← h, ← hγg]
    rfl
  rw [← ratAT_injective Q₀ T₀ h1]
  exact det_smul_ratFrame Q₀ T₀ _ X

/-- Equal classes of proper representations (relative to $\Xi_1$, $\Xi_2$) force equal determinants. -/
theorem det_eq_of_quotIncl_eq (Ξ₁ Ξ₂ : RatFrame Q₀ T₀) (a : repsP Q₀ T₀ Ξ₁ i) (b : repsP Q₀ T₀ Ξ₂ i)
    (g : unitGroup Q₀ i) (hg : g • repsPIncl Q₀ T₀ i Ξ₂ b = repsPIncl Q₀ T₀ i Ξ₁ a) :
    Ξ₁.1.det = Ξ₂.1.det := by
  obtain ⟨ηa, -, hηa⟩ := a.2
  obtain ⟨ηb, -, hηb⟩ := b.2
  have h : (g : GInfSO Q₀) • ratAT Q₀ T₀ ηb.1 = ratAT Q₀ T₀ ηa.1 := by
    have := congrArg Subtype.val hg
    exact (congrArg (fun y => (g : GInfSO Q₀) • y) hηb).trans (this.trans hηa.symm)
  rw [← ηa.2, ← ηb.2]
  exact det_eq_of_smul_ratAT Q₀ T₀ i g ηb.1 ηa.1 h

end Split

/-! ### The two orbits -/

section TwoOrbits

variable (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) N) (hT : T₀.Nondegenerate)
  (Ξ : RatFrame Q₀ T₀)

include hQ in
/-- **Two determinants**: every rational frame $X$ of $T_0$ has $\det X = \pm\det\Xi$ ($(\det X)^2\det H_{Q_0} = \det H_{T_0}$). -/
theorem det_ratFrame_eq_or (X : RatFrame Q₀ T₀) : X.1.det = Ξ.1.det ∨ X.1.det = -Ξ.1.det := by
  have h := congrArg Matrix.det ((gram_ratFrame_zero Q₀ T₀ X).trans (gram_ratFrame_zero Q₀ T₀ Ξ).symm)
  simp only [Matrix.det_mul, Matrix.det_transpose] at h
  have hH := det_hessian_map_ne_zero Q₀ hQ
  have h2 : X.1.det ^ 2 = Ξ.1.det ^ 2 := by
    apply mul_right_cancel₀ hH
    linear_combination h
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h2

include hQ in
/-- **An improper rational frame**: $s\Xi$ for a rational reflection $s$ has $\det(s\Xi) = -\det\Xi$. -/
theorem exists_ratFrame_det_neg (hN : 0 < N) : ∃ Ξ' : RatFrame Q₀ T₀, Ξ'.1.det = -Ξ.1.det := by
  obtain ⟨s, hs⟩ := exists_orthGroup_det_neg_one (Q₀.map (algebraMap (𝓞 F) F)) (witt_nd Q₀ hQ) hN
  refine ⟨⟨(s : GL (Fin N) F).val * Ξ.1, ?_⟩, ?_⟩
  · rw [compMat_orth _ s.2, Ξ.2]
  · show ((s : GL (Fin N) F).val * Ξ.1).det = -Ξ.1.det
    rw [Matrix.det_mul, hs, neg_one_mul]

include hQ hT in
/-- **The representations split into the two orbits**: $n(M_i,T_0) = n^+_\Xi(M_i,T_0) + n^+_{\Xi'}(M_i,T_0)$ when
$\det\Xi' = -\det\Xi$. -/
theorem repCount_eq_add (Ξ' : RatFrame Q₀ T₀) (h' : Ξ'.1.det = -Ξ.1.det) (i : DC Q₀) :
    repCount Q₀ T₀ i = repCountP Q₀ T₀ Ξ i + repCountP Q₀ T₀ Ξ' i := by
  have hΞ : Ξ.1.det ≠ 0 := by simpa using det_map_ne_zero_zero Q₀ T₀ hT Ξ (RingHom.id F)
  have hne : Ξ.1.det ≠ Ξ'.1.det := by
    intro h
    rw [h'] at h
    have h2 : (2 : F) * Ξ.1.det = 0 := by linear_combination h
    exact hΞ ((mul_eq_zero.1 h2).resolve_left two_ne_zero)
  have hbij : Function.Bijective (Sum.elim (quotIncl Q₀ T₀ i Ξ) (quotIncl Q₀ T₀ i Ξ')) := by
    have hinj : ∀ Ξ₀ : RatFrame Q₀ T₀, Function.Injective (quotIncl Q₀ T₀ i Ξ₀) := by
      intro Ξ₀ a b hab
      obtain ⟨a, rfl⟩ := Quotient.exists_rep a
      obtain ⟨b, rfl⟩ := Quotient.exists_rep b
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.exact hab))
      have hg' := congrArg Subtype.val hg
      exact Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2
        ⟨g, Subtype.ext hg'⟩))
    refine ⟨?_, ?_⟩
    · rintro (a | a) (b | b) hab
      · exact congrArg Sum.inl (hinj Ξ hab)
      · exfalso
        obtain ⟨a, rfl⟩ := Quotient.exists_rep a
        obtain ⟨b, rfl⟩ := Quotient.exists_rep b
        obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.exact hab))
        exact hne (det_eq_of_quotIncl_eq Q₀ T₀ i Ξ Ξ' a b g hg)
      · exfalso
        obtain ⟨a, rfl⟩ := Quotient.exists_rep a
        obtain ⟨b, rfl⟩ := Quotient.exists_rep b
        obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.exact hab.symm))
        exact hne (det_eq_of_quotIncl_eq Q₀ T₀ i Ξ Ξ' b a g hg)
      · exact congrArg Sum.inr (hinj Ξ' hab)
    · intro q
      obtain ⟨y, rfl⟩ := Quotient.exists_rep q
      obtain ⟨X, hX, hXy⟩ := y.2
      rcases det_ratFrame_eq_or Q₀ hQ T₀ Ξ X with h | h
      · exact ⟨Sum.inl (Quotient.mk _ ⟨y.1, ⟨⟨X, h⟩, hX, hXy⟩⟩), rfl⟩
      · exact ⟨Sum.inr (Quotient.mk _ ⟨y.1, ⟨⟨X, h.trans h'.symm⟩, hX, hXy⟩⟩), rfl⟩
  unfold repCount repCountP
  rw [← (Equiv.ofBijective _ hbij).tsum_eq (fun _ => (1 : ℝ≥0∞))]
  exact Summable.tsum_sum (f := fun _ => (1 : ℝ≥0∞)) ENNReal.summable ENNReal.summable

end TwoOrbits

end QuadFormsKB.Tamagawa.Indefinite
