/-
# The measures of representations of the forms headlines at $r = 1$, class by class

**Layer:** number fields. $F$ a number field, $Q_0$ nondegenerate over $\mathcal O_F$ in $N$ variables (any signature),
$m\in\mathcal O_F$, $m\ne0$, $T_0 = \langle m\rangle$ (`DVR.unary m`), $\Xi$ a rational $1$-frame of $\langle m\rangle$ (a rational
vector $\xi$ with $Q_0(\xi) = m$), classes $M_i$ of the genus of $L = \mathcal O_F^N$ (`DC Q₀`).

The forms headlines measure the representations of $T_0$ with stabilizer measures built from the frame
data of $\Xi$ (`frameArchFibrationNF`, `frameArchFibrationRank2`, `isoStabMeasure`); the numbers headlines with those
of the sphere fibration `archFibrationNF`. Until now only the totals $\sum_i\rho(M_i,\cdot)$ were compared (for $N\ge4$). Here
they are identified **class by class**.

**Defines**
* `stabFrameVecME X`: for a $1$-frame $X$, $H_X = H_{X_0}$ (stabilizer of the frame = stabilizer of its vector);
* `splitMat ξ C` $= [\xi\mid C]$ in $N = k+1$ variables, and `FrameTowerAlg.toSplitDataInf`: the frame data at infinity
  (`SplitDataInf`) of algebraic frame data `FrameTowerAlg` of a $1$-frame;
* `repsFrameVec`: $R(M_i,\langle m\rangle)\cong R(M_i,m)$, $X\mapsto X_0$, $\Gamma_i$-equivariant.

**Proves** (unconditional)
* `repMeasureOf_congr`: measures of representations agree under an equivariant bijection with matching terms;
* **`repMeasureT_frameArchFibrationRank2_unary`** (rank 2, anisotropic complement, ternary $Q_0$): the
  $\rho(M_i,\langle m\rangle)$ = $\rho(M_i, m)$ for `archFibrationNF`, for every class $i$;
* **`siegelIndefinite_ternary_sphere_uncond`**: the ternary numbers headline (`siegelIndefinite_ternary_uncond`) with
  the stabilizer measures of `archFibrationNF`
  measures of representations, derived from the forms headline `siegelIndefiniteForms_rank2_uncond` at $r = 1$;
* **`isoStabMeasure_unary_eq`** (rank 2, isotropic complement, ternary $Q_0$): the norm-one stabilizer measure at $X$ is
  the stabilizer measure of `archFibrationNF` at $X_0$ restricted to the norm-one shell; hence
  (`repMeasureIso_unary_eq`) the
  $\rho^1(M_i,\langle m\rangle)$ is the norm-one measure of representations of $m$ in the normalization of
  `archFibrationNF`.
-/
import QuadFormsKB.Tamagawa.Indefinite.StabCompareNF
import QuadFormsKB.Tamagawa.Indefinite.IsoMeasures

open MeasureTheory Measure Matrix MulAction Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.Weil LocalDensity

/-! ### Frames of rank one and their vectors -/

section FrameVec

variable {G : Type*} [Group G] {V : Type*} [MulAction G V]

theorem mem_stabilizer_frame_one {X : Fin 1 → V} {g : G} : g ∈ stabilizer G X ↔ g ∈ stabilizer G (X 0) := by
  rw [mem_stabilizer_iff, mem_stabilizer_iff]
  constructor
  · intro h
    exact congrFun h 0
  · intro h
    funext i
    rw [Subsingleton.elim i 0]
    exact h

/-- **The stabilizer of a $1$-frame is the stabilizer of its vector**: $H_X = H_{X_0}$. -/
def stabFrameVec (X : Fin 1 → V) : stabilizer G X ≃* stabilizer G (X 0) :=
  MulEquiv.subgroupCongr (Subgroup.ext fun _ => mem_stabilizer_frame_one)

theorem coe_stabFrameVec (X : Fin 1 → V) (g : stabilizer G X) : ((stabFrameVec X g : stabilizer G (X 0)) : G) = g :=
  rfl

variable [MeasurableSpace G]

/-- `stabFrameVec` as a measurable equivalence. -/
def stabFrameVecME (X : Fin 1 → V) : stabilizer G X ≃ᵐ stabilizer G (X 0) where
  toEquiv := (stabFrameVec X).toEquiv
  measurable_toFun := measurable_subtype_coe.subtype_mk
  measurable_invFun := measurable_subtype_coe.subtype_mk

end FrameVec

/-! ### Measures of representations under an equivariant bijection -/

section Congr

variable {A : Type*} [Group A] [MeasurableSpace A] {Y Y' : Type*} [MulAction A Y] [MulAction A Y']

/-- **Measures of representations agree under an equivariant bijection** $e : S\cong S'$ if the terms match
($\operatorname{vol}(\Gamma'_s\backslash H_s, \mu_s) = \operatorname{vol}(\Gamma'_{e(s)}\backslash H_{e(s)}, \mu'_{e(s)})$) and the
terms on the target side are constant on $\Gamma'$-orbits. -/
theorem repMeasureOf_congr (Γ' : Subgroup A) (S : SubMulAction Γ' Y) (S' : SubMulAction Γ' Y') (e : S ≃ S')
    (he : ∀ (γ : Γ') (s : S), e (γ • s) = γ • e s) (μ : (y : Y) → Measure (stabilizer A y))
    (μ' : (y : Y') → Measure (stabilizer A y))
    (hterm : ∀ s : S, covolume (stabArith Γ' (s : Y)) (stabilizer A (s : Y)) (μ s) =
      covolume (stabArith Γ' (e s : Y')) (stabilizer A (e s : Y')) (μ' (e s)))
    (hinv : ∀ (s : S') (γ : Γ'), covolume (stabArith Γ' ((γ • s : S') : Y')) (stabilizer A ((γ • s : S') : Y'))
      (μ' (γ • s : S')) = covolume (stabArith Γ' (s : Y')) (stabilizer A (s : Y')) (μ' s)) :
    repMeasureOf Γ' S μ = repMeasureOf Γ' S' μ' := by
  have he' : ∀ a b : S, (orbitRel Γ' S) a b ↔ (orbitRel Γ' S') (e a) (e b) := by
    intro a b
    rw [orbitRel_apply, orbitRel_apply, MulAction.mem_orbit_iff, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨γ, hγ⟩
      exact ⟨γ, by rw [← he, hγ]⟩
    · rintro ⟨γ, hγ⟩
      refine ⟨γ, e.injective ?_⟩
      rw [he, hγ]
  let E : orbitRel.Quotient Γ' S ≃ orbitRel.Quotient Γ' S' := Quotient.congr e he'
  unfold repMeasureOf
  refine Eq.trans ?_ (E.tsum_eq _)
  refine tsum_congr fun q => ?_
  have hq : E q = Quotient.mk _ (e q.out) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  have hrel : (orbitRel Γ' S') ((E q).out : S') (e q.out) := by
    rw [hq]
    exact Quotient.mk_out (s := orbitRel Γ' S') (e q.out)
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (orbitRel_apply.mp hrel)
  have key : ∀ (s : S') (γ : Γ') (s' : S'), γ • s = s' →
      covolume (stabArith Γ' (s' : Y')) (stabilizer A (s' : Y')) (μ' s') =
        covolume (stabArith Γ' (s : Y')) (stabilizer A (s : Y')) (μ' s) := by
    intro s γ s' h
    subst h
    exact hinv s γ
  exact (hterm q.out).trans (key _ γ _ hγ).symm

end Congr

/-! ### Frame data at infinity from algebraic frame data of a $1$-frame -/

section Adapter

open QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {F : Type} [Field F] [NumberField F] {k : ℕ}

/-- **The matrix $[\xi\mid C]$** in $k+1$ variables: column $0$ is $\xi$, columns $1,\dots,k$ are those of $C$. -/
def splitMat (ξ : Fin (k + 1) → F) (C : Matrix (Fin (k + 1)) (Fin k) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F :=
  Matrix.of fun i j => Fin.cases (ξ i) (fun b => C i b) j

theorem splitMat_zero_apply (ξ : Fin (k + 1) → F) (C : Matrix (Fin (k + 1)) (Fin k) F) (i : Fin (k + 1)) :
    splitMat ξ C i 0 = ξ i := rfl

theorem splitMat_succ_apply (ξ : Fin (k + 1) → F) (C : Matrix (Fin (k + 1)) (Fin k) F) (i : Fin (k + 1))
    (b : Fin k) : splitMat ξ C i b.succ = C i b := rfl

theorem map_splitMat {K : Type} [CommRing K] (f : F →+* K) (ξ : Fin (k + 1) → F)
    (C : Matrix (Fin (k + 1)) (Fin k) F) :
    (splitMat ξ C).map f = splitMat (fun j => f (ξ j)) (C.map f) := by
  ext i j
  refine Fin.cases ?_ (fun b => ?_) j <;> rfl

theorem mul_splitMat {K : Type} [CommRing K] (M : Matrix (Fin (k + 1)) (Fin (k + 1)) K) (ξ : Fin (k + 1) → K)
    (C : Matrix (Fin (k + 1)) (Fin k) K) : M * splitMat ξ C = splitMat (M *ᵥ ξ) (M * C) := by
  ext i j
  refine Fin.cases ?_ (fun b => ?_) j
  · simp [splitMat, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · simp [splitMat, Matrix.mul_apply]

theorem splitMat_mul_cornerMat {K : Type} [CommRing K] (ξ : Fin (k + 1) → K) (C : Matrix (Fin (k + 1)) (Fin k) K)
    (B : Matrix (Fin k) (Fin k) K) : splitMat ξ C * cornerMat 1 B = splitMat ξ (C * B) := by
  ext i j
  refine Fin.cases ?_ (fun b => ?_) j
  · simp [splitMat, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp [splitMat, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The Gram matrix of $[\xi\mid C]$: $\operatorname{diag}(\xi^{\mathsf T}H\xi, C^{\mathsf T}HC)$ if $C\perp\xi$. -/
theorem splitMat_gram (H : Matrix (Fin (k + 1)) (Fin (k + 1)) F) (hH : Hᵀ = H) (ξ : Fin (k + 1) → F)
    (C : Matrix (Fin (k + 1)) (Fin k) F) (c : F) (hξ : ξ ⬝ᵥ (H *ᵥ ξ) = c) (hC : (Cᵀ * H) *ᵥ ξ = 0) :
    (splitMat ξ C)ᵀ * H * splitMat ξ C = cornerMat c (Cᵀ * H * C) := by
  have hcx : ∀ b : Fin k, (fun l => C l b) ⬝ᵥ (H *ᵥ ξ) = 0 := by
    intro b
    have := congrFun hC b
    rw [← Matrix.mulVec_mulVec] at this
    simpa [Matrix.mulVec, dotProduct] using this
  ext i j
  rw [DVR.transpose_mul_mul_apply₂ H (splitMat ξ C) (splitMat ξ C)]
  refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
  · exact hξ
  · have h := bH_comm hH ξ (fun l => C l b)
    simp only [bH] at h
    show ξ ⬝ᵥ (H *ᵥ fun l => C l b) = 0
    rw [h, hcx]
  · exact hcx a
  · exact (DVR.transpose_mul_mul_apply₂ H C C a b).symm

theorem mul_cornerMat_conj {K : Type} [Field K] (f : F →+* K) (ξ : Fin (k + 1) → F)
    (C : Matrix (Fin (k + 1)) (Fin k) F) (g : GL (Fin (k + 1)) F) (hg : (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F) =
      splitMat ξ C) (M : Matrix (Fin (k + 1)) (Fin (k + 1)) K) (Hh : Matrix (Fin k) (Fin k) K)
    (hC : M * C.map f = C.map f * Hh) (hξ : M *ᵥ (fun j => f (ξ j)) = fun j => f (ξ j)) :
    M = (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F).map f * cornerMat 1 Hh *
      ((g⁻¹ : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F).map f := by
  have h1 : M * (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F).map f =
      (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F).map f * cornerMat 1 Hh := by
    rw [hg, map_splitMat, mul_splitMat, splitMat_mul_cornerMat, hξ, hC]
  have h2 : (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F).map f *
      ((g⁻¹ : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F).map f = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one f (map_zero f) (map_one f)]
  calc M = M * ((g : Matrix (Fin (k + 1)) (Fin (k + 1)) F).map f *
        ((g⁻¹ : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F).map f) := by rw [h2, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, h1]

variable {Q₀ : QuadForm (𝓞 F) (k + 1)} {hQ : Q₀.Nondegenerate} {Ξ : Fin 1 → Fin (k + 1) → F}

theorem FrameTowerAlg.splitMat_gram_eq (D : FrameTowerAlg Q₀ hQ k Ξ) {m : F}
    (hξ : (Q₀.map (algebraMap (𝓞 F) F)).eval (Ξ 0) = m) :
    (splitMat (Ξ 0) D.Cm)ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian * splitMat (Ξ 0) D.Cm =
      cornerMat (2 * m) (D.Q''.map (algebraMap (𝓞 F) F)).hessian := by
  rw [← D.hCH]
  refine splitMat_gram _ (witt_hessian_symm _) _ _ _ ?_ (D.hΞC 0)
  have h := qH_hessian Q₀ (Ξ 0)
  rw [show qF Q₀ (Ξ 0) = m from hξ] at h
  exact h

theorem FrameTowerAlg.isUnit_det_splitMat (D : FrameTowerAlg Q₀ hQ k Ξ) {m : F} (hm : m ≠ 0)
    (hξ : (Q₀.map (algebraMap (𝓞 F) F)).eval (Ξ 0) = m) : IsUnit (splitMat (Ξ 0) D.Cm).det := by
  have h := congrArg Matrix.det (D.splitMat_gram_eq hξ)
  rw [det_cornerMat, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  have hH := witt_nd Q₀ hQ
  have hH'' := witt_nd _ D.hQ''
  unfold QuadForm.Nondegenerate at hH hH''
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0] at h
  have : (2 * m) * (D.Q''.map (algebraMap (𝓞 F) F)).hessian.det = 0 := by rw [← h]; ring
  rcases mul_eq_zero.1 this with h3 | h3
  · rcases mul_eq_zero.1 h3 with h4 | h4
    · exact two_ne_zero h4
    · exact hm h4
  · exact hH'' h3

theorem FrameTowerAlg.mulVec_ξ_real (D : FrameTowerAlg Q₀ hQ k Ξ) (h : GInfSO D.Q'')
    (w : {w : InfinitePlace F // w.IsReal}) :
    (ArchSO.incl _ ((D.ιInf h).1 w) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) *ᵥ (fun j => σR w (Ξ 0 j)) =
      fun j => σR w (Ξ 0 j) := by
  have e := D.fix ((h, 1) : SOAdele D.Q'')
  have hd : ∀ c : F, (diag F c).1.1 w = σR w c := fun c => mixedEmbedding.mixedEmbedding_apply_isReal F c w
  funext i
  have h1 : ((ArchSO.incl _ ((D.ιInf h).1 w) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) *ᵥ
      fun j => (diag F (Ξ 0 j)).1.1 w) i = (diag F (Ξ 0 i)).1.1 w :=
    congrArg (fun y => (y 0 i).1.1 w) e
  simpa only [hd] using h1

theorem FrameTowerAlg.mulVec_ξ_complex (D : FrameTowerAlg Q₀ hQ k Ξ) (h : GInfSO D.Q'')
    (w : {w : InfinitePlace F // w.IsComplex}) :
    (ArchSOC.incl _ ((D.ιInf h).2 w) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) *ᵥ (fun j => σC w (Ξ 0 j)) =
      fun j => σC w (Ξ 0 j) := by
  have e := D.fix ((h, 1) : SOAdele D.Q'')
  have hd : ∀ c : F, (diag F c).1.2 w = σC w c := fun c => mixedEmbedding.mixedEmbedding_apply_isComplex F c w
  funext i
  have h1 : ((ArchSOC.incl _ ((D.ιInf h).2 w) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) *ᵥ
      fun j => (diag F (Ξ 0 j)).1.2 w) i = (diag F (Ξ 0 i)).1.2 w :=
    congrArg (fun y => (y 0 i).1.2 w) e
  simpa only [hd] using h1

/-- **The frame data at infinity of a $1$-frame** $\Xi = (\xi)$ with $Q_0(\xi) = m\ne0$, from algebraic frame data: $g = [\xi\mid C]$,
$Q'' = $ `D.Q''`, $\iota = $ `D.ιInf`. -/
def FrameTowerAlg.toSplitDataInf (D : FrameTowerAlg Q₀ hQ k Ξ) {m : F} (hm : m ≠ 0)
    (hξ : (Q₀.map (algebraMap (𝓞 F) F)).eval (Ξ 0) = m) : SplitDataInf Q₀ m (Ξ 0) where
  Q'' := D.Q''
  hQ'' := D.hQ''
  g := Matrix.nonsingInvUnit _ (D.isUnit_det_splitMat hm hξ)
  hess := by
    show (splitForm m (D.Q''.map (algebraMap (𝓞 F) F))).hessian =
      (splitMat (Ξ 0) D.Cm)ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian * splitMat (Ξ 0) D.Cm
    rw [hessian_splitForm, D.splitMat_gram_eq hξ]
  base := by
    show splitMat (Ξ 0) D.Cm *ᵥ Pi.single 0 1 = Ξ 0
    funext i
    simp [splitMat, Matrix.mulVec, dotProduct, Pi.single_apply]
  ι := D.ιInf
  measurable_ι := D.measurable_ιInf
  matR_ι := fun h w =>
    mul_cornerMat_conj (σR w) (Ξ 0) D.Cm (Matrix.nonsingInvUnit _ (D.isUnit_det_splitMat hm hξ)) rfl _ _
      (D.hCR ((h, 1) : SOAdele D.Q'') w) (D.mulVec_ξ_real h w)
  matC_ι := fun h w =>
    mul_cornerMat_conj (σC w) (Ξ 0) D.Cm (Matrix.nonsingInvUnit _ (D.isUnit_det_splitMat hm hξ)) rfl _ _
      (D.hCC ((h, 1) : SOAdele D.Q'') w) (D.mulVec_ξ_complex h w)

theorem FrameTowerAlg.toSplitDataInf_g (D : FrameTowerAlg Q₀ hQ k Ξ) {m : F} (hm : m ≠ 0)
    (hξ : (Q₀.map (algebraMap (𝓞 F) F)).eval (Ξ 0) = m) :
    ((D.toSplitDataInf hm hξ).g : Matrix (Fin (k + 1)) (Fin (k + 1)) F) = splitMat (Ξ 0) D.Cm := rfl

/-- The archimedean point of the column of a rational $1$-frame is `ξInf` of the column. -/
theorem ratAT_zero_eq_ξInf {r : ℕ} (T₀ : QuadForm (𝓞 F) r) (Ξ' : RatFrame Q₀ T₀) (j : Fin r) :
    ratAT Q₀ T₀ Ξ' j = ξInf (cols Ξ'.1 j) := by
  refine Prod.ext (funext fun w => funext fun i => ?_) (funext fun w => funext fun i => ?_)
  · obtain ⟨w, hw⟩ := w
    simp only [ratAT, ratFrameA, archVec, diagVec_apply, diag_fst, mixedEmbedding.mixedEmbedding_apply_isReal, ξInf,
      cols, σR]
  · obtain ⟨w, hw⟩ := w
    simp only [ratAT, ratFrameA, archVec, diagVec_apply, diag_fst, mixedEmbedding.mixedEmbedding_apply_isComplex, ξInf,
      cols, σC]

/-- For $N = 3$ ($1 + 2 = 2 + 1$), $[\Xi\mid C]$ (`wittG`) is `splitMat`. -/
theorem wittG_eq_splitMat_three (Ξ' : Matrix (Fin (1 + 2)) (Fin 1) F) (C : Matrix (Fin (1 + 2)) (Fin 2) F) :
    wittG Ξ' C = splitMat (k := 2) (fun i => Ξ' i 0) C := by
  ext i j
  fin_cases j <;> rfl

end Adapter

/-! ### Representations of $\langle m\rangle$ and of $m$ -/

section Reps

variable {F : Type} [Field F] [NumberField F] {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (m : 𝓞 F)

open scoped Pointwise

theorem compMat_unary_iff_gen (X : Matrix (Fin N) (Fin 1) F) :
    (Q₀.map (algebraMap (𝓞 F) F)).compMat X = (DVR.unary m).map (algebraMap (𝓞 F) F) ↔
      qF Q₀ (fun i => X i 0) = algebraMap (𝓞 F) F m := by
  refine QuadForm.ext_iff.trans ?_
  refine (Matrix.ext_iff (m := Fin 1) (n := Fin 1)).symm.trans ?_
  simp only [Fin.forall_fin_one, QuadForm.compMat_coeff]
  simp [DVR.unary, QuadForm.map, QuadForm.diag, qF]

/-- The rational frames of $\langle m\rangle$ are the rational vectors of value $m$ (any number of variables). -/
def ratFrameSph : RatFrame Q₀ (DVR.unary m) ≃ RatSphere Q₀ (m : F) where
  toFun X := ⟨fun i => X.1 i 0, (compMat_unary_iff_gen Q₀ m X.1).1 X.2⟩
  invFun η := ⟨Matrix.of fun i _ => η.1 i, (compMat_unary_iff_gen Q₀ m _).2 η.2⟩
  left_inv X := Subtype.ext (by ext i j; rw [Subsingleton.elim j 0]; rfl)
  right_inv η := rfl

theorem ratAT_ratFrameSph (Ξ' : RatFrame Q₀ (DVR.unary m)) (j : Fin 1) :
    ratAT Q₀ (DVR.unary m) Ξ' j = ratA Q₀ (m : F) (ratFrameSph Q₀ m Ξ') := by
  rw [Subsingleton.elim j 0]
  rfl

theorem ratFT_ratFrameSph (Ξ' : RatFrame Q₀ (DVR.unary m)) (j : Fin 1) :
    ratFT Q₀ (DVR.unary m) Ξ' j = ratF Q₀ (m : F) (ratFrameSph Q₀ m Ξ') := by
  rw [Subsingleton.elim j 0]
  rfl

/-- **The representations of $\langle m\rangle$ and of $m$ by a class correspond**: $X\mapsto X_0$,
$R(M_i,\langle m\rangle)\cong R(M_i, m)$. -/
def repsFrameVec (i : DC Q₀) : repsT Q₀ (DVR.unary m) i ≃ reps Q₀ (m : F) i where
  toFun X := ⟨X.1 0, by
    have hX : X.1 ∈ ratAT Q₀ (DVR.unary m) '' {Ξ' | ratFT Q₀ (DVR.unary m) Ξ' ∈ dcRep Q₀ i • latHatT F N 1} := X.2
    obtain ⟨Ξ', hΞ', h⟩ := hX
    rw [← h]
    refine ⟨ratFrameSph Q₀ m Ξ', ?_, (ratAT_ratFrameSph Q₀ m Ξ' 0).symm⟩
    obtain ⟨Z, hZ, hZe⟩ := Set.mem_smul_set.mp hΞ'
    refine Set.mem_smul_set.mpr ⟨Z 0, hZ 0, ?_⟩
    rw [(ratFT_ratFrameSph Q₀ m Ξ' 0).symm, ← hZe]
    rfl⟩
  invFun y := ⟨fun _ => y.1, by
    have hy : y.1 ∈ ratA Q₀ (m : F) '' {η | ratF Q₀ (m : F) η ∈ dcRep Q₀ i • latHat F N} := y.2
    obtain ⟨η, hη, h⟩ := hy
    refine ⟨(ratFrameSph Q₀ m).symm η, ?_, funext fun j => ?_⟩
    · obtain ⟨z, hz, hze⟩ := Set.mem_smul_set.mp hη
      refine Set.mem_smul_set.mpr ⟨fun _ => z, fun _ => hz, funext fun j => ?_⟩
      rw [ratFT_ratFrameSph Q₀ m, Equiv.apply_symm_apply, ← hze]
      rfl
    · rw [ratAT_ratFrameSph Q₀ m, Equiv.apply_symm_apply, h]⟩
  left_inv X := Subtype.ext (funext fun j => by rw [Subsingleton.elim j 0])
  right_inv y := Subtype.ext rfl

theorem repsFrameVec_apply (i : DC Q₀) (X : repsT Q₀ (DVR.unary m) i) :
    ((repsFrameVec Q₀ m i X : reps Q₀ (m : F) i) : VInf F N) = (X : Fin 1 → VInf F N) 0 := rfl

theorem repsFrameVec_smul (i : DC Q₀) (γ : unitGroup Q₀ i) (X : repsT Q₀ (DVR.unary m) i) :
    repsFrameVec Q₀ m i (γ • X) = γ • repsFrameVec Q₀ m i X := rfl

/-- Every representation of $\langle m\rangle$ is the image of a rational frame. -/
theorem exists_ratFrame_of_mem_repsT (i : DC Q₀) (X : repsT Q₀ (DVR.unary m) i) :
    ∃ Ξ' : RatFrame Q₀ (DVR.unary m), ratAT Q₀ (DVR.unary m) Ξ' = X := by
  have hX : X.1 ∈ ratAT Q₀ (DVR.unary m) '' {Ξ' | ratFT Q₀ (DVR.unary m) Ξ' ∈ dcRep Q₀ i • latHatT F N 1} := X.2
  obtain ⟨Ξ', _, h⟩ := hX
  exact ⟨Ξ', h⟩

end Reps

end QuadFormsKB.Tamagawa.Indefinite
