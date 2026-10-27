/-
# Siegel's formula for frames, Weil's form: reduction to a sum over integral adelic frames

**Layer:** number fields, adeles. $F$ a number field, $Q_0$ nondegenerate over $\mathcal O_F$ in $N = r + n'$ variables
(any signature), $T_0$ of rank $r$, a rational frame $\Xi$ of $T_0$ and frame coordinates `D : FrameTower Q₀ hQ n' Ξ`
(complement $Q''$, $\iota = \iota_\infty\times\iota_f$). $G = SO(V)$, $K = SO(\hat L)$, $H = SO(Q'')$.

**Defines**
* `FinOrbit`, `finOrbitRep`: the $K$-orbits of finite-adelic frames $g\,\Xi_f$ ($g\in G(\mathbb A_f)$) lying in $\hat L^r$, and
  representatives; **`frameOrbitSum`** $=\sum_O\mu_f(K)/\mu_{H,f}(K_O)$, $K_O = \iota_f^{-1}(g_O^{-1}Kg_O)$ (Weil's measure of the
  integral adelic frames).

**Proves**
* `exists_smul_eq_ratFrame`: Witt's theorem for frames, $SO(V)(F)$ is transitive on the rational frames of $T_0$ ($n'\ge1$);
* `lintegral_theta_frame`: $\int_E\theta = \operatorname{covol}(H(F)\backslash H(\mathbb A))\int(\Phi\otimes1_{\hat L^r})\circ\tau\,d\sigma$;
* `lintegral_testFnT_eq`: $\int(\Phi\otimes1_{\hat L^r})\circ\tau\,d\sigma = \texttt{frameOrbitSum}\cdot\int\Phi\,d\sigma_A$
  (`FrameOrbitVolume.lean`);
* **`siegelFormsWeil`** (Siegel's formula in Weil's form): if $\tau(SO(V)) = \tau(SO(Q'')) = 2$,
  $$\sum_i\rho^{\mathrm{Tam}}(M_i, T_0) = \texttt{frameOrbitSum}\cdot\sum_iv(M_i).$$
-/
import QuadFormsKB.Tamagawa.Indefinite.FrameSiegelArch
import QuadFormsKB.Tamagawa.Indefinite.FrameOrbitVolume
import QuadFormsKB.Tamagawa.Indefinite.SiegelIndefinite

open MeasureTheory Set Matrix MulAction
open scoped ENNReal Pointwise

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F] {r n' : ℕ}

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### Algebra for Witt's theorem on frames -/

section WittAlg

open QuadFormsKB.Tamagawa.Frames

/-- The block matrix `[Ξ | C]`. -/
def wittG {K : Type*} {r n' : ℕ} (Ξ : Matrix (Fin (r + n')) (Fin r) K) (C : Matrix (Fin (r + n')) (Fin n') K) :
    Matrix (Fin (r + n')) (Fin (r + n')) K :=
  Matrix.of fun i j => Fin.addCases (fun a => Ξ i a) (fun b => C i b) j

theorem wittG_gram {K : Type*} [Field K] {r n' : ℕ} (H : Matrix (Fin (r + n')) (Fin (r + n')) K) (hH : Hᵀ = H)
    (Ξ : Matrix (Fin (r + n')) (Fin r) K) (C : Matrix (Fin (r + n')) (Fin n') K)
    (hCΞ : ∀ j, (Cᵀ * H) *ᵥ (fun i => Ξ i j) = 0) :
    (wittG Ξ C)ᵀ * H * wittG Ξ C = blockMat (Ξᵀ * H * Ξ) 0 0 (Cᵀ * H * C) := by
  have hl : ∀ a, (fun l => wittG Ξ C l (Fin.castAdd n' a)) = fun l => Ξ l a := by
    intro a; ext l; simp [wittG]
  have hr : ∀ b, (fun l => wittG Ξ C l (Fin.natAdd r b)) = fun l => C l b := by
    intro b; ext l; simp [wittG]
  have hCx : ∀ (b : Fin n') (a : Fin r), (fun l => C l b) ⬝ᵥ (H *ᵥ fun l => Ξ l a) = 0 := by
    intro b a
    have := congrFun (hCΞ a) b
    rw [← Matrix.mulVec_mulVec] at this
    simpa [Matrix.mulVec, dotProduct] using this
  ext i j
  rw [QuadFormsKB.LocalDensity.DVR.transpose_mul_mul_apply₂ H (wittG Ξ C) (wittG Ξ C)]
  induction i using Fin.addCases with
  | left a =>
    induction j using Fin.addCases with
    | left b =>
      rw [hl, hl, blockMat_castAdd_castAdd, QuadFormsKB.LocalDensity.DVR.transpose_mul_mul_apply₂]
    | right b =>
      rw [hl, hr, blockMat_castAdd_natAdd]
      have := bH_comm hH (fun l => C l b) (fun l => Ξ l a)
      simp only [bH] at this
      rw [← this, hCx]; simp
  | right a =>
    induction j using Fin.addCases with
    | left b =>
      rw [hl, hr, blockMat_natAdd_castAdd, hCx]; simp
    | right b =>
      rw [hr, hr, blockMat_natAdd_natAdd, QuadFormsKB.LocalDensity.DVR.transpose_mul_mul_apply₂]

theorem wittG_mul_std {K : Type*} [CommRing K] {r n' : ℕ} (Ξ : Matrix (Fin (r + n')) (Fin r) K)
    (C : Matrix (Fin (r + n')) (Fin n') K) :
    wittG Ξ C * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) K) = Ξ := by
  refine Matrix.ext fun i a => ?_
  rw [Matrix.mul_apply]
  simp [wittG, stdFrameMat]

theorem wittAniso {K : Type*} [Field K] [CharZero K] {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (hH : Hᵀ = H)
    (hdet : H.det ≠ 0) (hn : 1 ≤ n) : ∃ u, qH H u ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hz : H = 0 := by
    ext i j
    have h1 := hcon (Pi.single i 1 + Pi.single j 1)
    rw [qH_add hH, hcon, hcon] at h1
    have hbij : bH H (Pi.single i 1) (Pi.single j 1) = H i j := by
      simp [bH, mulVec, dotProduct, Pi.single_apply]
    rw [hbij] at h1
    have : (2 : K) * H i j = 0 := by linear_combination h1
    simpa using (mul_eq_zero.mp this).resolve_left two_ne_zero
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact hdet (by rw [hz]; simp)

theorem witt_hessian_symm {F : Type*} [Field F] {n : ℕ} (Q : QuadForm F n) : Q.hessianᵀ = Q.hessian := by
  simp [QuadForm.hessian, Matrix.transpose_add, add_comm]

theorem witt_exists_det_one {F : Type*} [Field F] [NumberField F] {r n' : ℕ} (T : QuadForm F r) (Q2 : QuadForm F n')
    (hT : T.Nondegenerate)
    (hQ2 : Q2.Nondegenerate) (hn' : 1 ≤ n') {Y : Matrix (Fin (r + n')) (Fin r) F}
    (hY : (blockForm T Q2).compMat Y = T) :
    ∃ γ : orthGroup (blockForm T Q2) F, (γ : GL (Fin (r + n')) F).val.det = 1 ∧
      (γ : GL (Fin (r + n')) F).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) F) = Y := by
  have hQB : (blockForm T Q2).Nondegenerate := by
    unfold QuadForm.Nondegenerate; rw [det_hessian_blockForm]; exact mul_ne_zero hT hQ2
  have hQ' : ((blockForm T Q2).hessian.map (algebraMap F F)).det ≠ 0 := by
    rw [hessian_map_self]; exact hQB
  have hT' : (T.hessian.map (algebraMap F F)).det ≠ 0 := by
    rw [hessian_map_self]; exact hT
  obtain ⟨γ, hγ⟩ := exists_orthGroup_mul_stdFrameMat T Q2 F hQ' hT' (X := Y)
    (by rw [map_self_quadForm, map_self_quadForm]; exact hY)
  rcases det_eq_one_or_neg_one (blockForm T Q2) hQB γ with h | h
  · exact ⟨γ, h, hγ⟩
  · obtain ⟨u, hu⟩ := wittAniso Q2.hessian (witt_hessian_symm Q2) hQ2 hn'
    have hdets : (Measure.Weil.refl Q2.hessian u).det = -1 := det_refl hu
    have hUnit : IsUnit (Measure.Weil.refl Q2.hessian u).det := by
      rw [hdets]; exact isUnit_one.neg
    let sGL : GL (Fin n') F := Matrix.nonsingInvUnit _ hUnit
    have hsO : sGL ∈ orthGroup Q2 F := by
      rw [mem_orthGroup_iff', hessian_map_self]
      exact transpose_refl_mul_mul_refl (witt_hessian_symm Q2) hu
    refine ⟨γ * orthEmbB T Q2 F ⟨sGL, hsO⟩, ?_, ?_⟩
    · show ((γ : GL (Fin (r + n')) F) * (orthEmbB T Q2 F ⟨sGL, hsO⟩ : GL (Fin (r + n')) F)).val.det = 1
      rw [Units.val_mul, Matrix.det_mul, h, orthEmbB_val, det_blockMat_diag, Matrix.det_one]
      show (-1 : F) * (1 * (Measure.Weil.refl Q2.hessian u).det) = 1
      rw [hdets]; ring
    · show ((γ : GL (Fin (r + n')) F) * (orthEmbB T Q2 F ⟨sGL, hsO⟩ : GL (Fin (r + n')) F)).val * _ = Y
      rw [Units.val_mul, Matrix.mul_assoc]
      exact (congrArg (fun z => ((γ : GL (Fin (r + n')) F)).val * z)
        (orthEmbB_mul_stdFrameMat T Q2 F ⟨sGL, hsO⟩)).trans hγ

theorem witt_eq_of_hessian_eq {F : Type*} [Field F] [NumberField F] {n : ℕ} {Q₁ Q₂ : QuadForm F n}
    (h : Q₁.hessian = Q₂.hessian) : Q₁ = Q₂ := by
  refine QuadForm.ext_upper fun i j hij => ?_
  have hij' := congrFun (congrFun h i) j
  simp only [QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply] at hij'
  rcases hij.lt_or_eq with hlt | heq
  · have h1 : Q₁.coeff j i = 0 := Q₁.upper (show id i < id j from hlt)
    have h2 : Q₂.coeff j i = 0 := Q₂.upper (show id i < id j from hlt)
    rwa [h1, h2, add_zero, add_zero] at hij'
  · subst heq
    have : (2 : F) * Q₁.coeff i i = 2 * Q₂.coeff i i := by linear_combination hij'
    exact mul_left_cancel₀ two_ne_zero this

theorem witt_core {F : Type*} [Field F] [NumberField F] {r n' : ℕ} (QF : QuadForm F (r + n')) (T : QuadForm F r)
    (Q2 : QuadForm F n') (hT : T.Nondegenerate)
    (hQ2 : Q2.Nondegenerate) (hn' : 1 ≤ n') (Ξ : Matrix (Fin (r + n')) (Fin r) F)
    (C : Matrix (Fin (r + n')) (Fin n') F) (hΞ : QF.compMat Ξ = T)
    (hCH : Cᵀ * QF.hessian * C = Q2.hessian) (hΞC : ∀ j, (Cᵀ * QF.hessian) *ᵥ (fun i => Ξ i j) = 0)
    {X : Matrix (Fin (r + n')) (Fin r) F} (hX : QF.compMat X = T) :
    ∃ φ : GL (Fin (r + n')) F, φ ∈ orthGroup QF F ∧ φ.val.det = 1 ∧ φ.val * Ξ = X := by
  set H := QF.hessian with hHdef
  have hH : Hᵀ = H := witt_hessian_symm QF
  set g := wittG Ξ C with hgdef
  have hgram : gᵀ * H * g = (blockForm T Q2).hessian := by
    rw [hgdef, wittG_gram H hH Ξ C hΞC, hessian_blockForm, hCH, ← hΞ, QuadForm.hessian_compMat]
  have hdetB : (blockForm T Q2).hessian.det ≠ 0 := by
    rw [det_hessian_blockForm]; exact mul_ne_zero hT hQ2
  have hdg : g.det ≠ 0 := by
    intro h0
    apply hdetB
    rw [← hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0]; ring
  have hu : IsUnit g.det := isUnit_iff_ne_zero.2 hdg
  have hgi : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hu
  have hig : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hu
  set Y : Matrix (Fin (r + n')) (Fin r) F := g⁻¹ * X with hYdef
  have hgY : g * Y = X := by rw [hYdef, ← Matrix.mul_assoc, hgi, Matrix.one_mul]
  have hY : (blockForm T Q2).compMat Y = T := by
    apply witt_eq_of_hessian_eq
    rw [QuadForm.hessian_compMat, ← hgram]
    have e : Yᵀ * (gᵀ * H * g) * Y = (g * Y)ᵀ * H * (g * Y) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e, hgY, ← QuadForm.hessian_compMat, hX]
  obtain ⟨γ, hdγ, hγ⟩ := witt_exists_det_one T Q2 hT hQ2 hn' hY
  have hγo : ((γ : GL (Fin (r + n')) F).val)ᵀ * (blockForm T Q2).hessian * (γ : GL (Fin (r + n')) F).val =
      (blockForm T Q2).hessian := by
    have := (mem_orthGroup_iff' (blockForm T Q2)).1 γ.2
    rwa [hessian_map_self] at this
  have hE : g * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) F) = Ξ := wittG_mul_std Ξ C
  set gGL : GL (Fin (r + n')) F := Matrix.nonsingInvUnit g hu with hgGL
  refine ⟨gGL * (γ : GL (Fin (r + n')) F) * gGL⁻¹, ?_, ?_, ?_⟩
  · rw [mem_orthGroup_iff', hessian_map_self]
    show (g * (γ : GL (Fin (r + n')) F).val * g⁻¹)ᵀ * H * (g * (γ : GL (Fin (r + n')) F).val * g⁻¹) = H
    have e1 : (g * (γ : GL (Fin (r + n')) F).val * g⁻¹)ᵀ * H * (g * (γ : GL (Fin (r + n')) F).val * g⁻¹) =
        (g⁻¹)ᵀ * (((γ : GL (Fin (r + n')) F).val)ᵀ * (gᵀ * H * g) * (γ : GL (Fin (r + n')) F).val) * g⁻¹ := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e1, hgram, hγo, ← hgram]
    have e2 : (g⁻¹)ᵀ * (gᵀ * H * g) * g⁻¹ = (g * g⁻¹)ᵀ * H * (g * g⁻¹) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e2, hgi]; simp
  · show (g * (γ : GL (Fin (r + n')) F).val * g⁻¹).det = 1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, hdγ]
    rw [Ring.inverse_eq_inv']
    field_simp
  · show (g * (γ : GL (Fin (r + n')) F).val * g⁻¹) * Ξ = X
    rw [← hE]
    have : g * (γ : GL (Fin (r + n')) F).val * g⁻¹ * (g * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) F)) =
        g * ((γ : GL (Fin (r + n')) F).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) F)) := by
      calc _ = g * (γ : GL (Fin (r + n')) F).val * (g⁻¹ * g) * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) F) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hig, Matrix.mul_one, Matrix.mul_assoc]
    rw [this, hγ, hgY]

end WittAlg

theorem witt_nd {N : ℕ} (Q : QuadForm (𝓞 F) N) (h : Q.Nondegenerate) :
    (Q.map (algebraMap (𝓞 F) F)).Nondegenerate := by
  unfold QuadForm.Nondegenerate
  rw [Siegel.hessian_map_NF, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr h

variable (Q₀ : QuadForm (𝓞 F) (r + n')) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (Ξ : RatFrame Q₀ T₀)
  (D : FrameTower Q₀ hQ n' (cols Ξ.1))

/-! ### Witt's theorem for frames and the unfolding -/

include D in
/-- **Witt's theorem for frames** (O'Meara 42:17 for $SO$; $n'\ge1$): $SO(V)(F)$ is transitive on the rational frames of
$T_0$. (The frame coordinates `D` supply the complement $C$ with $Q_0\circ C = Q''$, $C\perp\Xi$.) -/
theorem exists_smul_eq_ratFrame (hT : T₀.Nondegenerate) (hn' : 1 ≤ n') (X : RatFrame Q₀ T₀) :
    ∃ γ : GammaSOAdele Q₀, γ • Ξ = X := by
  obtain ⟨φ, hφO, hdet, hφΞ⟩ := witt_core (Q₀.map (algebraMap (𝓞 F) F)) (T₀.map (algebraMap (𝓞 F) F))
    (D.Q''.map (algebraMap (𝓞 F) F)) (witt_nd T₀ hT) (witt_nd _ D.hQ'') hn' Ξ.1 D.Cm Ξ.2 D.hCH D.hΞC
    (X := X.1) X.2
  refine ⟨gammaEquiv Q₀ ⟨⟨φ, hφO⟩, hdet⟩, Subtype.ext ?_⟩
  rw [ratFrame_smul_val, MulEquiv.symm_apply_apply]
  exact hφΞ

/-- The test function $\Phi\otimes1_{\hat L^r}$ on adelic frames. -/
def testFnT {N : ℕ} (Φ : (Fin r → VInf F N) → ℝ≥0∞) (Y : Fin r → AdeleSpace F (Fin N)) : ℝ≥0∞ :=
  Φ (splitFrame Y).1 * (latHatT F N r).indicator 1 (splitFrame Y).2

theorem ratFrameA_injective : Function.Injective (ratFrameA Q₀ T₀) := by
  intro X X' e
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  exact diag_injective (congrFun (congrFun e j) i)

/-- $\{b\in SO(V)(\mathbb A_f) : b^{-1}z\in\hat L^r\}$ is open (a union of cosets of the open subgroup $SO(\hat L)$). -/
theorem red_isOpen_latSet (z : Fin r → Fin (r + n') → AF) :
    IsOpen {b : SOAf Q₀ | b⁻¹ • z ∈ latHatT F (r + n') r} := by
  set S := {b : SOAf Q₀ | b⁻¹ • z ∈ latHatT F (r + n') r} with hS
  have hSeq : S = ⋃ b ∈ S, b • (KSO Q₀ : Set (SOAf Q₀)) := by
    ext b
    constructor
    · intro hb
      exact mem_iUnion₂.2 ⟨b, hb, Set.mem_smul_set.2 ⟨1, (KSO Q₀).one_mem, by simp⟩⟩
    · intro hb
      obtain ⟨b', hb', hmem⟩ := mem_iUnion₂.1 hb
      obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.1 hmem
      have e : (b' • k)⁻¹ • z = k⁻¹ • (b'⁻¹ • z) := by
        rw [smul_eq_mul, _root_.mul_inv_rev, mul_smul]
      show (b' • k)⁻¹ • z ∈ latHatT F (r + n') r
      rw [e]
      exact (latHatT_stable Q₀ k⁻¹ ((KSO Q₀).inv_mem hk) _).2 hb'
  rw [hSeq]
  exact isOpen_biUnion fun b _ => (isOpen_KSO Q₀).smul b

/-- The test function along the parameters is measurable. -/
theorem measurable_testFnT_tau {Φ : (Fin r → VInf F (r + n')) → ℝ≥0∞} (hΦ : Measurable Φ) :
    Measurable fun p : D.T => testFnT Φ (D.τ p) := by
  have hc : Measurable fun p : D.T => D.C.coord (p, 1) :=
    D.C.coord.measurable.comp (measurable_id.prodMk measurable_const)
  have h1 : ∀ p : D.T, testFnT Φ (D.τ p) =
      Φ ((D.C.coord (p, 1)).1⁻¹ • ratAT Q₀ T₀ Ξ) *
        (latHatT F (r + n') r).indicator 1 ((D.C.coord (p, 1)).2⁻¹ • ratFT Q₀ T₀ Ξ) := by
    intro p
    rw [testFnT, ← D.C.orbit p 1, splitFrame_smul]
    rfl
  have hS := (red_isOpen_latSet Q₀ (ratFT Q₀ T₀ Ξ)).measurableSet
  have h2 : (fun p : D.T => (latHatT F (r + n') r).indicator (1 : (Fin r → Fin (r + n') → AF) → ℝ≥0∞)
      ((D.C.coord (p, 1)).2⁻¹ • ratFT Q₀ T₀ Ξ)) =
      fun p => {b : SOAf Q₀ | b⁻¹ • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + n') r}.indicator 1 (D.C.coord (p, 1)).2 := by
    funext p
    rfl
  simp_rw [h1]
  refine Measurable.mul ?_ ?_
  · exact (measurable_GInf_inv_smulT Q₀ hΦ (ratAT Q₀ T₀ Ξ)).comp (measurable_fst.comp hc)
  · rw [h2]
    exact (measurable_one.indicator hS).comp (measurable_snd.comp hc)

/-- **The theta integral of frames, adelically** (Weil 1982, §4.5, p. 109 for frames): for every fundamental domain $E$
of $SO(V)(F)$ in $SO(V)(\mathbb A)$,
$$\int_E\theta\,d\mu = \operatorname{covol}(SO(Q'')(F)\backslash SO(Q'')(\mathbb A))\cdot\int(\Phi\otimes1_{\hat L^r})\circ\tau\,d\sigma.$$ -/
theorem lintegral_theta_frame (hT : T₀.Nondegenerate) (hn' : 1 ≤ n') {Φ : (Fin r → VInf F (r + n')) → ℝ≥0∞}
    (hΦ : Measurable Φ) {E : Set (SOAdele Q₀)}
    (hE : IsFundamentalDomain (GammaSOAdele Q₀) E (muTam Q₀ hQ fun _ => 1)) :
    ∫⁻ g in E, thetaFn (ratAT Q₀ T₀) (ratFT Q₀ T₀) Φ (latHatT F (r + n') r) g ∂muTam Q₀ hQ (fun _ => 1) =
      covolume (GammaSOAdele D.Q'') (SOAdele D.Q'') (muTam D.Q'' D.hQ'' fun _ => 1) *
        ∫⁻ p, testFnT Φ (D.τ p) ∂D.σ := by
  have := discreteTopology_GammaSOAdele D.Q''
  have := countable_GammaSOAdele Q₀
  have := countable_GammaSOAdele D.Q''
  haveI := D.sFinite
  obtain ⟨DH, hDH, hDHx⟩ := exists_measurableSet_forall_existsUnique_smul_mem (GammaSOAdele D.Q'')
  have hfix : ∀ (h : SOAdele D.Q'') (hh : h ∈ GammaSOAdele D.Q''),
      (⟨MonoidHom.prodMap D.ιInf D.ιFin h, D.gamma_mem h hh⟩ : GammaSOAdele Q₀) • Ξ = Ξ := by
    intro h hh
    apply ratFrameA_injective Q₀ T₀
    rw [ratFrameA_smul]
    exact D.C.ι_smul h
  have key := lintegral_sphere_unfold (Γ := GammaSOAdele Q₀) (μ := muTam Q₀ hQ fun _ => 1)
    (ΓH := GammaSOAdele D.Q'') (μH := muTam D.Q'' D.hQ'' fun _ => 1)
    (fun η : RatFrame Q₀ T₀ => ratFrameA Q₀ T₀ η)
    (fun γ η => ratFrameA_smul Q₀ T₀ γ η) Ξ
    (fun η => exists_smul_eq_ratFrame Q₀ hQ T₀ Ξ D hT hn' η) (MonoidHom.prodMap D.ιInf D.ιFin) D.σ D.τ D.C
    D.gamma_mem hfix
    (fun γ hγ => D.stabΓ γ γ.2 (by
      have := congrArg (ratFrameA Q₀ T₀) hγ
      rw [ratFrameA_smul] at this
      exact this))
    hDH hDHx 1 (by rw [one_smul]; exact D.fib) hE (testFnT Φ) (measurable_testFnT_tau Q₀ hQ T₀ Ξ D hΦ)
  rw [one_mul] at key
  rw [← key]
  refine lintegral_congr fun g => ?_
  unfold thetaFn
  refine tsum_congr fun η => ?_
  rw [testFnT, splitFrame_smul]
  rfl

/-! ### The integral adelic frames -/

/-- The relation "same $K$-orbit of $g\,\Xi_f$" on the $g\in G(\mathbb A_f)$ with $g\,\Xi_f\in\hat L^r$. -/
def finOrbitSetoid : Setoid {b : SOAf Q₀ // b • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + n') r} where
  r b b' := (b' : SOAf Q₀) • ratFT Q₀ T₀ Ξ ∈ (KSO Q₀ : Set (SOAf Q₀)) • ({(b : SOAf Q₀) • ratFT Q₀ T₀ Ξ} : Set _)
  iseqv := by
    refine ⟨fun b => ?_, fun {b b'} h => ?_, fun {b b' b''} h h' => ?_⟩
    · exact Set.mem_smul.2 ⟨1, (KSO Q₀).one_mem, _, rfl, one_smul _ _⟩
    · obtain ⟨k, hk, y, hy, hky⟩ := Set.mem_smul.1 h
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Set.mem_smul.2 ⟨k⁻¹, (KSO Q₀).inv_mem hk, _, rfl, by rw [← hky, inv_smul_smul]⟩
    · obtain ⟨k, hk, y, hy, hky⟩ := Set.mem_smul.1 h
      obtain ⟨k', hk', y', hy', hky'⟩ := Set.mem_smul.1 h'
      rw [Set.mem_singleton_iff] at hy hy'
      subst hy hy'
      exact Set.mem_smul.2 ⟨k' * k, (KSO Q₀).mul_mem hk' hk, _, rfl, by rw [mul_smul, hky, hky']⟩

/-- **The $SO(\hat L)$-orbits of integral finite-adelic frames** in the $G(\mathbb A_f)$-orbit of $\Xi$. -/
abbrev FinOrbit : Type := Quotient (finOrbitSetoid Q₀ T₀ Ξ)

instance : Countable (FinOrbit Q₀ T₀ Ξ) := by
  classical
  have := countable_SOAf_quot Q₀
  let φ : {b : SOAf Q₀ // b • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + n') r} → SOAf Q₀ ⧸ KSO Q₀ :=
    fun b => QuotientGroup.mk (b.1)⁻¹
  have : Countable (Set.range φ) := inferInstance
  refine Function.Surjective.countable (f := fun q : Set.range φ => (Quotient.mk (finOrbitSetoid Q₀ T₀ Ξ) q.2.choose :
    FinOrbit Q₀ T₀ Ξ)) ?_
  intro O
  induction O using Quotient.inductionOn with | _ b => ?_
  refine ⟨⟨φ b, b, rfl⟩, ?_⟩
  have hc := (⟨φ b, b, rfl⟩ : Set.range φ).2.choose_spec
  set c := (⟨φ b, b, rfl⟩ : Set.range φ).2.choose with hcdef
  apply Quotient.sound
  have hk : c.1 * (b.1)⁻¹ ∈ KSO Q₀ := by
    have := QuotientGroup.eq.1 hc
    simpa using this
  refine Set.mem_smul.2 ⟨b.1 * (c.1)⁻¹, ?_, _, rfl, ?_⟩
  · have := (KSO Q₀).inv_mem hk
    simpa [_root_.mul_inv_rev] using this
  · show (b.1 * (c.1)⁻¹) • c.1 • ratFT Q₀ T₀ Ξ = b.1 • ratFT Q₀ T₀ Ξ
    rw [smul_smul, mul_assoc, inv_mul_cancel, mul_one]

/-- A representative $g_O\in G(\mathbb A_f)$ of the orbit $O = Kg_O\Xi_f$. -/
def finOrbitRep (O : FinOrbit Q₀ T₀ Ξ) : SOAf Q₀ := (Quotient.out O : {b : SOAf Q₀ // _}).1

/-- **Weil's measure of the integral adelic frames**: $\sum_O\mu_f(K)/\mu_{H,f}(K_O)$, $K_O = \iota_f^{-1}(g_O^{-1}Kg_O)$. -/
def frameOrbitSum : ℝ≥0∞ :=
  ∑' O : FinOrbit Q₀ T₀ Ξ, muFin Q₀ (fun _ => 1) (KSO Q₀) /
    muFin D.Q'' (fun _ => 1) (orbitStab D.ιFin (KSO Q₀) (finOrbitRep Q₀ T₀ Ξ O))

/-! ### Abstract lemma: the stabilizer-of-orbit has positive finite measure -/

section Abstract

open Classical

variable {A B A' B' : Type*} [Group A] [Group B] [Group A'] [Group B']
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace A'] [MeasurableSpace B']
  [MeasurableMul₂ A] [MeasurableMul B] [MeasurableMul A'] [MeasurableMul B']
  {YA YB : Type*} [MulAction A YA] [MulAction B YB] [MeasurableSpace YA]
  {T : Type*} [MeasurableSpace T] {ιA : A' →* A} {ιB : B' →* B} {τ : T → YA × YB} {a₀ : YA} {b₀ : YB}

theorem orb_orbStab_ne (C : OrbitCoord (MonoidHom.prodMap ιA ιB) τ (a₀, b₀))
    (hst : StabIn (MonoidHom.prodMap ιA ιB) (a₀, b₀)) (μA : Measure A) (μB : Measure B) (μA' : Measure A')
    (μB' : Measure B') (σ : Measure T) [SFinite μA] [SFinite μB] [SFinite μA'] [SFinite μB'] [SFinite σ]
    [μB.IsMulLeftInvariant] [μB'.IsMulRightInvariant]
    (hfib : μA.prod μB = (σ.prod (μA'.prod μB')).map C.coord) (K : Subgroup B) (hK : MeasurableSet (K : Set B))
    (gO : B) {X : Set A} (hX : MeasurableSet X) (hX0 : μA X ≠ 0) (hXt : μA X ≠ ⊤)
    (hK0 : μB K ≠ 0) (hKt : μB K ≠ ⊤) (hιA : Measurable ιA)
    (hO : MeasurableSet {p | (τ p).2 ∈ (K : Set B) • ({gO • b₀} : Set YB)}) :
    μB' (orbitStab ιB K gO) ≠ 0 ∧ μB' (orbitStab ιB K gO) ≠ ⊤ := by
  have hmain := measure_prod_orbit C hst μA μB μA' μB' σ hfib K hK gO hX
  have hLHS0 : μA X * μB K ≠ 0 := mul_ne_zero hX0 hK0
  have hLHSt : μA X * μB K ≠ ⊤ := ENNReal.mul_ne_top hXt hKt
  set c := μB' (orbitStab ιB K gO) with hc
  set f : T → ℝ≥0∞ := fun p => μA' {h | ιA h * (C.coord (p, 1)).1 ∈ X} with hf
  have hW : MeasurableSet {q : T × A' | ιA q.2 * (C.coord (q.1, 1)).1 ∈ X} := by
    have h1 : Measurable fun q : T × A' => (C.coord (q.1, 1)).1 :=
      measurable_fst.comp (C.coord.measurable.comp (measurable_fst.prodMk measurable_const))
    exact ((hιA.comp measurable_snd).mul h1) hX
  have hfm : Measurable f := measurable_measure_prodMk_left (ν := μA') hW
  have hgm : Measurable fun p => f p * (if (τ p).2 ∈ (K : Set B) • ({gO • b₀} : Set YB) then c else 0) :=
    hfm.mul (Measurable.ite hO measurable_const measurable_const)
  refine ⟨fun h0 => ?_, fun ht => ?_⟩
  · rw [h0] at hmain
    simp at hmain
    rcases hmain with h | h
    · exact hX0 h
    · exact hK0 h
  · rw [ht] at hmain
    have hfin : ∫⁻ p, f p * (if (τ p).2 ∈ (K : Set B) • ({gO • b₀} : Set YB) then ⊤ else 0) ∂σ ≠ ⊤ := by
      rw [← hmain]; exact hLHSt
    have hae := ae_lt_top (by simpa [ht] using hgm) hfin
    have h0 : ∫⁻ p, f p * (if (τ p).2 ∈ (K : Set B) • ({gO • b₀} : Set YB) then ⊤ else 0) ∂σ = 0 := by
      rw [lintegral_eq_zero_iff (by simpa [ht] using hgm)]
      filter_upwards [hae] with p hp
      by_cases hE : (τ p).2 ∈ (K : Set B) • ({gO • b₀} : Set YB)
      · rw [if_pos hE] at hp ⊢
        by_contra hne
        exact hp.ne (ENNReal.mul_top (fun h => hne (by simp [h])))
      · rw [if_neg hE, mul_zero]; rfl
    rw [h0] at hmain
    exact hLHS0 hmain

end Abstract

/-- A reference set of the archimedean orbit space with the fibration gives a box of positive finite measure. -/
theorem orb_exists_X {A A' TA YA : Type*} [Group A] [Group A'] [MeasurableSpace A] [MeasurableSpace A']
    [MeasurableSpace TA] [MulAction A YA] {ιA : A' →* A} {τA : TA → YA} {a₀ : YA}
    (CA : OrbitCoord ιA τA a₀) (μA : Measure A) (μA' : Measure A') (σA : Measure TA) [SigmaFinite σA]
    [SFinite μA'] (hA : μA = (σA.prod μA').map CA.coord) (hσ : σA ≠ 0)
    (hU : ∃ U : Set A', MeasurableSet U ∧ μA' U ≠ 0 ∧ μA' U ≠ ⊤) :
    ∃ X : Set A, MeasurableSet X ∧ μA X ≠ 0 ∧ μA X ≠ ⊤ := by
  obtain ⟨U, hUm, hU0, hUt⟩ := hU
  obtain ⟨S, hSm, hS0, hSt⟩ := OrbitSection.exists_pos_lt_top σA hσ
  have hXm : MeasurableSet (CA.coord '' (S ×ˢ U)) := CA.coord.measurableSet_image.2 (hSm.prod hUm)
  have hμX : μA (CA.coord '' (S ×ˢ U)) = σA S * μA' U := by
    rw [hA, Measure.map_apply CA.coord.measurable hXm, MeasurableEquiv.preimage_image, Measure.prod_prod]
  exact ⟨_, hXm, by rw [hμX]; exact mul_ne_zero hS0 hU0, by rw [hμX]; exact ENNReal.mul_ne_top hSt hUt⟩

section Concrete

/-- The set of `b ∈ SO(V)(𝔸_f)` with `b⁻¹ b₀ ∈ K y` is open (a union of cosets of the open subgroup `K`). -/
theorem orb_isOpen_orbitSet (b₀ y : Fin r → Fin (r + n') → AF) :
    IsOpen {b : SOAf Q₀ | b⁻¹ • b₀ ∈ (KSO Q₀ : Set (SOAf Q₀)) • ({y} : Set (Fin r → Fin (r + n') → AF))} := by
  set S := {b : SOAf Q₀ | b⁻¹ • b₀ ∈ (KSO Q₀ : Set (SOAf Q₀)) • ({y} : Set (Fin r → Fin (r + n') → AF))} with hS
  have hSeq : S = ⋃ b ∈ S, b • (KSO Q₀ : Set (SOAf Q₀)) := by
    ext b
    constructor
    · intro hb
      exact mem_iUnion₂.2 ⟨b, hb, Set.mem_smul_set.2 ⟨1, (KSO Q₀).one_mem, by simp⟩⟩
    · intro hb
      obtain ⟨b', hb', hmem⟩ := mem_iUnion₂.1 hb
      obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.1 hmem
      obtain ⟨k1, hk1, y', hy', h⟩ := Set.mem_smul.1 hb'
      refine Set.mem_smul.2 ⟨k⁻¹ * k1, (KSO Q₀).mul_mem ((KSO Q₀).inv_mem hk) hk1, y', hy', ?_⟩
      show (k⁻¹ * k1) • y' = (b' * k)⁻¹ • b₀
      rw [_root_.mul_inv_rev, mul_smul, mul_smul, h]
  rw [hSeq]
  exact isOpen_biUnion fun b _ => (isOpen_KSO Q₀).smul b

theorem orb_measurableSet_orbit (y : Fin r → Fin (r + n') → AF) :
    MeasurableSet {p : D.T | ((splitFrame ∘ D.τ) p).2 ∈ (KSO Q₀ : Set (SOAf Q₀)) • ({y} : Set (Fin r → Fin (r + n') → AF))} := by
  have h1 : Measurable fun p : D.T => ((frameCprod Q₀ hQ T₀ Ξ D).coord (p, 1)).2 :=
    measurable_snd.comp ((frameCprod Q₀ hQ T₀ Ξ D).coord.measurable.comp (measurable_id.prodMk measurable_const))
  have h2 := (orb_isOpen_orbitSet Q₀ (ratFT Q₀ T₀ Ξ) y).measurableSet
  have h3 : {p : D.T | ((splitFrame ∘ D.τ) p).2 ∈ (KSO Q₀ : Set (SOAf Q₀)) • ({y} : Set (Fin r → Fin (r + n') → AF))} =
      (fun p : D.T => ((frameCprod Q₀ hQ T₀ Ξ D).coord (p, 1)).2) ⁻¹'
        {b : SOAf Q₀ | b⁻¹ • ratFT Q₀ T₀ Ξ ∈ (KSO Q₀ : Set (SOAf Q₀)) • ({y} : Set (Fin r → Fin (r + n') → AF))} := by
    ext p
    simp only [mem_setOf_eq, mem_preimage]
    rw [τ_snd_eq (frameCprod Q₀ hQ T₀ Ξ D) p]
  rw [h3]
  exact h1 h2

theorem orb_measurable_projA : Measurable (projA (frameCprod Q₀ hQ T₀ Ξ D)) := by
  refine Measurable.subtype_mk ?_
  have h : (fun p : D.T => ((splitFrame ∘ D.τ) p).1) =
      fun p => ((frameCprod Q₀ hQ T₀ Ξ D).coord (p, 1)).1⁻¹ • ratAT Q₀ T₀ Ξ :=
    funext fun p => congrArg Prod.fst ((frameCprod Q₀ hQ T₀ Ξ D).orbit p 1).symm
  show Measurable fun p : D.T => ((splitFrame ∘ D.τ) p).1
  rw [h]
  exact (measurable_inv_smul_ratAT Q₀ T₀ Ξ).comp (measurable_fst.comp
    ((frameCprod Q₀ hQ T₀ Ξ D).coord.measurable.comp (measurable_id.prodMk measurable_const)))

theorem orb_rep_mem (O : FinOrbit Q₀ T₀ Ξ) :
    finOrbitRep Q₀ T₀ Ξ O • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + n') r := (Quotient.out O).2

theorem orb_disjoint : Pairwise fun i j : FinOrbit Q₀ T₀ Ξ =>
    Disjoint ((KSO Q₀ : Set (SOAf Q₀)) • ({finOrbitRep Q₀ T₀ Ξ i • ratFT Q₀ T₀ Ξ} : Set (Fin r → Fin (r + n') → AF)))
      ((KSO Q₀ : Set (SOAf Q₀)) • ({finOrbitRep Q₀ T₀ Ξ j • ratFT Q₀ T₀ Ξ} : Set (Fin r → Fin (r + n') → AF))) := by
  intro i j hij
  rw [Set.disjoint_left]
  rintro z ⟨k, hk, y, hy, rfl⟩ ⟨k', hk', y', hy', hz⟩
  rw [Set.mem_singleton_iff] at hy hy'
  subst hy hy'
  apply hij
  have hrel : (finOrbitSetoid Q₀ T₀ Ξ) (Quotient.out i) (Quotient.out j) := by
    refine Set.mem_smul.2 ⟨k'⁻¹ * k, (KSO Q₀).mul_mem ((KSO Q₀).inv_mem hk') hk, _, rfl, ?_⟩
    show (k'⁻¹ * k) • finOrbitRep Q₀ T₀ Ξ i • ratFT Q₀ T₀ Ξ = finOrbitRep Q₀ T₀ Ξ j • ratFT Q₀ T₀ Ξ
    rw [mul_smul]
    have : k • finOrbitRep Q₀ T₀ Ξ i • ratFT Q₀ T₀ Ξ = k' • finOrbitRep Q₀ T₀ Ξ j • ratFT Q₀ T₀ Ξ := hz.symm
    rw [this, inv_smul_smul]
  rw [← Quotient.out_eq i, ← Quotient.out_eq j]
  exact Quotient.sound hrel

theorem orb_cover (p : D.T) :
    ((splitFrame ∘ D.τ) p).2 ∈ latHatT F (r + n') r ↔
      ∃ i : FinOrbit Q₀ T₀ Ξ, ((splitFrame ∘ D.τ) p).2 ∈ (KSO Q₀ : Set (SOAf Q₀)) •
        ({finOrbitRep Q₀ T₀ Ξ i • ratFT Q₀ T₀ Ξ} : Set (Fin r → Fin (r + n') → AF)) := by
  constructor
  · intro h
    have hτ := τ_snd_eq (frameCprod Q₀ hQ T₀ Ξ D) p
    set b : SOAf Q₀ := ((frameCprod Q₀ hQ T₀ Ξ D).coord (p, 1)).2⁻¹ with hb
    have hmem : b • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + n') r := by
      rw [← hτ]
      exact h
    refine ⟨Quotient.mk (finOrbitSetoid Q₀ T₀ Ξ) ⟨b, hmem⟩, ?_⟩
    have hrel := Quotient.mk_out (s := finOrbitSetoid Q₀ T₀ Ξ) (⟨b, hmem⟩ : {b : SOAf Q₀ // b • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + n') r})
    rw [hτ]
    exact hrel
  · rintro ⟨i, k, hk, y, hy, hz⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [← hz]
    exact (latHatT_stable Q₀ k hk _).2 (orb_rep_mem Q₀ T₀ Ξ i)

end Concrete

/-- **The adelic integral of the test function**: $\int(\Phi\otimes1_{\hat L^r})\circ\tau\,d\sigma = \texttt{frameOrbitSum}\cdot
\int\Phi\,d\sigma_A$. -/
theorem lintegral_testFnT_eq (hn' : 3 ≤ n') {Φ : (Fin r → VInf F (r + n')) → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ p, testFnT Φ (D.τ p) ∂D.σ = frameOrbitSum Q₀ hQ T₀ Ξ D * ∫⁻ t, Φ t.1 ∂frameσA Q₀ hQ T₀ Ξ D := by
  classical
  have hn : 0 < n' := by omega
  have hN : 3 ≤ r + n' := by omega
  haveI := D.sFinite
  haveI := sigmaFinite_frameσA Q₀ hQ T₀ Ξ D
  haveI := isMulRightInvariant_muFin D.Q'' D.hQ'' hn
  haveI := isMulRightInvariant_muArchTamSO D.Q'' D.hQ''
  have hfib : (muArchTamSO Q₀ hQ).prod (muFin Q₀ fun _ => 1) =
      (D.σ.prod ((muArchTamSO D.Q'' D.hQ'').prod (muFin D.Q'' fun _ => 1))).map
        (frameCprod Q₀ hQ T₀ Ξ D).coord := D.fib
  have hA := frameσA_fib Q₀ hQ T₀ Ξ D
  have hU := exists_refSetInf Q₀ hQ T₀ Ξ D
  have hK : MeasurableSet (KSO Q₀ : Set (SOAf Q₀)) := (isOpen_KSO Q₀).measurableSet
  have hK0 : muFin Q₀ (fun _ => 1) (KSO Q₀ : Set (SOAf Q₀)) ≠ 0 := by
    rw [muFin_KSO]
    refine (ENNReal.ofReal_pos.2 ?_).ne'
    rw [finFactor_one Q₀ hQ]
    exact tprod_siegelDensity_pos hN Q₀ hQ
  have hKt : muFin Q₀ (fun _ => 1) (KSO Q₀ : Set (SOAf Q₀)) ≠ ⊤ := by
    rw [muFin_KSO]; exact ENNReal.ofReal_ne_top
  obtain ⟨X, hXm, hX0, hXt⟩ := orb_exists_X (frameCA Q₀ hQ T₀ Ξ D) (muArchTamSO Q₀ hQ) (muArchTamSO D.Q'' D.hQ'')
    (frameσA Q₀ hQ T₀ Ξ D) hA (frameσA_ne_zero Q₀ hQ T₀ Ξ D) hU
  have hKO : ∀ i : FinOrbit Q₀ T₀ Ξ, muFin D.Q'' (fun _ => 1) (orbitStab D.ιFin (KSO Q₀) (finOrbitRep Q₀ T₀ Ξ i)) ≠ 0 ∧
      muFin D.Q'' (fun _ => 1) (orbitStab D.ιFin (KSO Q₀) (finOrbitRep Q₀ T₀ Ξ i)) ≠ ⊤ := fun i =>
    orb_orbStab_ne (frameCprod Q₀ hQ T₀ Ξ D) (stabIn_frameCprod Q₀ hQ T₀ Ξ D) (muArchTamSO Q₀ hQ)
      (muFin Q₀ fun _ => 1) (muArchTamSO D.Q'' D.hQ'') (muFin D.Q'' fun _ => 1) D.σ hfib (KSO Q₀) hK
      (finOrbitRep Q₀ T₀ Ξ i) hXm hX0 hXt hK0 hKt D.measurable_ιInf
      (orb_measurableSet_orbit Q₀ hQ T₀ Ξ D _)
  have key := lintegral_testFn_orbits (frameCprod Q₀ hQ T₀ Ξ D) (stabIn_frameCprod Q₀ hQ T₀ Ξ D) (muArchTamSO Q₀ hQ)
    (muFin Q₀ fun _ => 1) (muArchTamSO D.Q'' D.hQ'') (muFin D.Q'' fun _ => 1) D.σ hfib
    (frameCA Q₀ hQ T₀ Ξ D) (frameσA Q₀ hQ T₀ Ξ D) hA (orb_measurable_projA Q₀ hQ T₀ Ξ D) (KSO Q₀) hK
    (finOrbitRep Q₀ T₀ Ξ) (fun i => orb_measurableSet_orbit Q₀ hQ T₀ Ξ D _) (fun i => (hKO i).1)
    (fun i => (hKO i).2) hU (latHatT F (r + n') r) (orb_disjoint Q₀ T₀ Ξ) (orb_cover Q₀ hQ T₀ Ξ D) Φ hΦ
  refine key.trans ?_
  rw [frameOrbitSum, ENNReal.tsum_mul_right]

/-! ### Siegel's formula in Weil's form -/

/-- **Siegel's formula for frames, Weil's form** (Weil 1965; Siegel 1935/1936 for indefinite forms): given
$\tau(SO(V)) = \tau(SO(Q'')) = 2$,
$$\sum_i\rho^{\mathrm{Tam}}(M_i, T_0) = \texttt{frameOrbitSum}\cdot\sum_iv(M_i),$$
$\rho^{\mathrm{Tam}}$ the measures of representations with the Tamagawa measures on the stabilizers (`frameArchFibTam`). -/
theorem siegelFormsWeil (hT : T₀.Nondegenerate) (hn' : 3 ≤ n') (hτ : TamagawaNumberTwoAdelic Q₀ hQ)
    (hτ' : TamagawaNumberTwoAdelic D.Q'' D.hQ'') :
    ∑' i, repMeasureT Q₀ T₀ hQ (frameArchFibTam Q₀ hQ T₀ Ξ D) i =
      frameOrbitSum Q₀ hQ T₀ Ξ D * ∑' i, unitVolume Q₀ hQ i := by
  have := countable_GammaSOAdele Q₀
  have := discreteTopology_GammaSOAdele Q₀
  haveI := sigmaFinite_frameσA Q₀ hQ T₀ Ξ D
  obtain ⟨E, hE⟩ := exists_measurableSet_forall_existsUnique_smul_mem (GammaSOAdele Q₀)
  have hEf : IsFundamentalDomain (GammaSOAdele Q₀) E (muTam Q₀ hQ fun _ => 1) :=
    IsFundamentalDomain.mk' hE.1.nullMeasurableSet hE.2
  have hn1 : 1 ≤ n' := by omega
  -- a test function with `0 < ∫ Φ dσA < ∞`
  obtain ⟨S, hSm, hS0, hSt⟩ := OrbitSection.exists_pos_lt_top (frameσA Q₀ hQ T₀ Ξ D)
    (frameσA_ne_zero Q₀ hQ T₀ Ξ D)
  obtain ⟨A, hAm, hAS⟩ := MeasurableSpace.measurableSet_comap.1 hSm
  set Φ : (Fin r → VInf F (r + n')) → ℝ≥0∞ := A.indicator 1 with hΦdef
  have hΦ : Measurable Φ := measurable_one.indicator hAm
  have hI : ∫⁻ t, Φ t.1 ∂frameσA Q₀ hQ T₀ Ξ D = frameσA Q₀ hQ T₀ Ξ D S := by
    have : (fun t : factorT (splitFrame ∘ D.τ) (ratFT Q₀ T₀ Ξ) => Φ t.1) = S.indicator 1 := by
      funext t
      rw [← hAS]; rfl
    rw [this, lintegral_indicator_one hSm]
  have hP : ∀ X : RatFrame Q₀ T₀, ratAT Q₀ T₀ X ∈ Set.range fun a : GInfSO Q₀ => a • ratAT Q₀ T₀ Ξ := by
    intro X
    obtain ⟨γ, rfl⟩ := exists_smul_eq_ratFrame Q₀ hQ T₀ Ξ D hT hn1 X
    exact ⟨(γ : SOAdele Q₀).1, (ratAT_smul Q₀ T₀ γ Ξ).symm⟩
  have h1 := lintegral_theta_classicalT Q₀ T₀ hQ (frameArchFibTam Q₀ hQ T₀ Ξ D) hP Φ hΦ
    (hΦ.comp measurable_subtype_coe) hEf
  rw [lintegral_theta_frame Q₀ hQ T₀ Ξ D hT hn1 hΦ hEf, lintegral_testFnT_eq Q₀ hQ T₀ Ξ D hn' hΦ] at h1
  have hG : covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) = 2 := hτ
  have hH : covolume (GammaSOAdele D.Q'') (SOAdele D.Q'') (muTam D.Q'' D.hQ'' fun _ => 1) = 2 := hτ'
  have hV := covolume_eq_muFin_mul_tsum_unitVolume Q₀ hQ
  rw [hG] at hV
  rw [hH] at h1
  have hK0 : muFin Q₀ (fun _ => 1) (KSO Q₀) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hV; exact two_ne_zero hV
  have hKt : muFin Q₀ (fun _ => 1) (KSO Q₀) ≠ ⊤ := by
    intro ht
    have hV0 : ∑' i, unitVolume Q₀ hQ i ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hV; exact two_ne_zero hV
    rw [ht, ENNReal.top_mul hV0] at hV; exact ENNReal.ofNat_ne_top hV
  rw [hI] at h1
  set I := frameσA Q₀ hQ T₀ Ξ D S
  set mK := muFin Q₀ (fun _ => 1) (KSO Q₀)
  set ρ := ∑' i, repMeasureT Q₀ T₀ hQ (frameArchFibTam Q₀ hQ T₀ Ξ D) i
  set V := ∑' i, unitVolume Q₀ hQ i
  set Sum := frameOrbitSum Q₀ hQ T₀ Ξ D
  have h2 : (mK * I) * (Sum * V) = (mK * I) * ρ := by
    calc (mK * I) * (Sum * V) = (mK * V) * (Sum * I) := by ring
      _ = 2 * (Sum * I) := by rw [← hV]
      _ = mK * 1 * ρ * I := h1
      _ = (mK * I) * ρ := by ring
  exact ((ENNReal.mul_right_inj (mul_ne_zero hK0 hS0) (ENNReal.mul_ne_top hKt hSt)).mp h2).symm

end QuadFormsKB.Tamagawa.Indefinite
