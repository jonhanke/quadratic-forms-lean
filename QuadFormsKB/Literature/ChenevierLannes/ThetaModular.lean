/-
# Chenevier–Lannes §5.1: the Siegel theta series of an even unimodular lattice is a Siegel modular form

Proves `SiegelThetaModular` (Siegel, Freitag Kap. I): for an even unimodular lattice $L$ of dimension $n$ and every
genus $g$, $\vartheta_g(L) \in M_{n/2}(\mathrm{Sp}_{2g}(\mathbb{Z}))$.

*Route* (a bridge, not a re-proof). The transformation law is `WeilRep.Genus.thetaG_sp_uncond` (generation of
$\mathrm{Sp}_{2g}(\mathbb{Z})$ by translations and the inversion, plus theta inversion); `siegelTheta g Q` is
`thetaG` of the Gram matrix $H$ of $Q$ (`siegelTheta_eq_thetaG`). Holomorphy is the term-by-term differentiation of
the series (`hasFDerivAt_tsum_of_isPreconnected`) with Gaussian majorants, and boundedness is the bound
$|e^{\pi i\,\mathrm{tr}(AZ)}| = e^{-\pi\,\mathrm{tr}(A\,\mathrm{Im} Z)} \le e^{-\pi\,\mathrm{tr}A}$ for $\mathrm{Im} Z \ge 1$.
-/
import QuadFormsKB.Literature.ChenevierLannes.Theta
import QuadFormsKB.Weil.Genus.EightDvd
import Mathlib.Algebra.Order.Chebyshev

open Matrix Complex Filter
open scoped Real

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Lattices

variable {n g : ℕ}

/-! ### The bridge to `WeilRep.Genus.thetaG` and the transformation law -/

/-- **`siegelTheta` is `thetaG` of the Gram matrix.** $\vartheta_g(L)(Z) = \Theta_H(Z)$ for $H$ the Hessian of $Q$. -/
theorem siegelTheta_eq_thetaG (Q : QuadForm ℤ n) (Z : Matrix (Fin g) (Fin g) ℂ) :
    siegelTheta g Q Z = WeilRep.Genus.thetaG (Q.hessian.map ((↑) : ℤ → ℝ)) Z := by
  unfold siegelTheta WeilRep.Genus.thetaG
  refine tsum_congr fun X => ?_
  unfold WeilRep.Genus.thetaArg
  rw [WeilRep.Genus.cZ_quad]

/-- The Hessian of an even unimodular form is a real positive definite matrix. -/
theorem hessianR_posDef {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) :
    (Q.hessian.map ((↑) : ℤ → ℝ)).PosDef := by
  have h := (gramMatrix_posDef hQ.posDef).smul (show (0 : ℝ) < 2 by norm_num)
  convert h using 1
  unfold gramMatrix
  rw [smul_smul]
  norm_num

/-- The dimension of an even unimodular lattice is even. -/
theorem exists_two_mul_of_isEvenUnimodular {Q : QuadForm ℤ n} (hQ : IsEvenUnimodular Q) : ∃ k, n = 2 * k := by
  obtain ⟨m, hm⟩ := eight_dvd_of_isEvenUnimodular hQ
  exact ⟨4 * m, by omega⟩

/-- **The transformation law** of $\vartheta_g(L)$ (weight $k = n/2$), from `WeilRep.Genus.thetaG_sp_uncond`. -/
theorem siegelTheta_modular_aux (k : ℕ) {Q : QuadForm ℤ (2 * k)} (hQ : IsEvenUnimodular Q) :
    ∀ γ ∈ sp2gZ g, ∀ Z ∈ siegelUpper g, siegelTheta g Q (spAct γ Z) = spJ γ Z ^ k * siegelTheta g Q Z := by
  intro γ hγ Z hZ
  have h := WeilRep.Genus.thetaG_sp_uncond (g := g) k (S := Q.hessian) (hessian_isSymm Q).eq
    (fun i => hessian_evenDiag Q i) (hessianR_posDef hQ) hQ.det_one ⟨γ, hγ⟩ (Z := Z) hZ
  rw [siegelTheta_eq_thetaG, siegelTheta_eq_thetaG]
  exact h.2.2

/-! ### Coercivity and a trace bound -/

/-- **Coercivity:** a real positive definite $Y$ has $w^{\mathsf T}Yw \ge c\,w^{\mathsf T}w$ for some $c > 0$ (minimum of
the continuous function $w \mapsto w^{\mathsf T}Yw$ on the compact unit sphere). -/
theorem tm_exists_coercive {r : ℕ} {Y : Matrix (Fin r) (Fin r) ℝ} (hY : Y.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ w : Fin r → ℝ, c * (w ⬝ᵥ w) ≤ w ⬝ᵥ Y *ᵥ w := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨1, one_pos, fun w => by simp [dotProduct]⟩
  set S : Set (Fin r → ℝ) := {w | w ⬝ᵥ w = 1}
  have hcont : Continuous fun w : Fin r → ℝ => w ⬝ᵥ Y *ᵥ w := by
    simp only [dotProduct, mulVec]; fun_prop
  have hsq : ∀ (w : Fin r → ℝ) i, w i ^ 2 ≤ w ⬝ᵥ w := by
    intro w i
    have := Finset.single_le_sum (f := fun j => w j * w j) (fun j _ => mul_self_nonneg (w j))
      (Finset.mem_univ i)
    simpa [dotProduct, sq] using this
  have hSc : IsCompact S := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact isClosed_eq (by simp only [dotProduct]; fun_prop) continuous_const
    · refine (Metric.isBounded_closedBall (x := (0 : Fin r → ℝ)) (r := 1)).subset fun w hw => ?_
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      have h1 := hsq w i
      have hw' : w ⬝ᵥ w = 1 := hw
      rw [Real.norm_eq_abs]
      nlinarith [sq_abs (w i), abs_nonneg (w i)]
  have hS : S.Nonempty := ⟨Pi.single ⟨0, hr⟩ 1, by simp [S, dotProduct, Pi.single_apply]⟩
  obtain ⟨w0, hw0, hmin⟩ := hSc.exists_isMinOn hS hcont.continuousOn
  have hw0ne : w0 ≠ 0 := by
    rintro rfl
    simp [S, dotProduct] at hw0
  have hc : 0 < w0 ⬝ᵥ Y *ᵥ w0 := by simpa using hY.dotProduct_mulVec_pos hw0ne
  refine ⟨_, hc, fun w => ?_⟩
  by_cases hw : w = 0
  · subst hw; simp
  have hpos : 0 < w ⬝ᵥ w := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
    have := hsq w i
    have hi' : w i ≠ 0 := hi
    have : 0 < w i ^ 2 := by positivity
    linarith
  set t := Real.sqrt (w ⬝ᵥ w)
  have ht : 0 < t := Real.sqrt_pos.mpr hpos
  have htt : t * t = w ⬝ᵥ w := Real.mul_self_sqrt hpos.le
  have hu : t⁻¹ • w ∈ S := by
    show (t⁻¹ • w) ⬝ᵥ (t⁻¹ • w) = 1
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← htt]
    field_simp
  have h := hmin hu
  simp only [Set.mem_ofPred_eq] at h
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h
  rw [← htt]
  have e : t⁻¹ * (t⁻¹ * (w ⬝ᵥ Y *ᵥ w)) * (t * t) = w ⬝ᵥ Y *ᵥ w := by field_simp
  calc w0 ⬝ᵥ Y *ᵥ w0 * (t * t) ≤ t⁻¹ * (t⁻¹ * (w ⬝ᵥ Y *ᵥ w)) * (t * t) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = w ⬝ᵥ Y *ᵥ w := e

theorem tm_sum_gram_aux {m r : ℕ} (W : Matrix (Fin m) (Fin r) ℝ) (Y : Matrix (Fin r) (Fin r) ℝ) :
    ∑ i, ∑ j, (Wᵀ * W) i j * Y i j = ∑ a, (fun j => W a j) ⬝ᵥ Y *ᵥ (fun j => W a j) := by
  simp only [mul_apply, transpose_apply, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
  ring

/-! ### The summands -/

section Analytic

variable (Q : QuadForm ℤ n)

/-- The summand $e^{\pi i\,\mathrm{tr}(X^{\mathsf T}HXZ)}$ of `siegelTheta`. -/
noncomputable def thTerm (X : Matrix (Fin n) (Fin g) ℤ) (Z : Matrix (Fin g) (Fin g) ℂ) : ℂ :=
  Complex.exp (Real.pi * I * ((Xᵀ * Q.hessian * X).map (Int.cast : ℤ → ℂ) * Z).trace)

theorem siegelTheta_eq_tsum (Z : Matrix (Fin g) (Fin g) ℂ) :
    siegelTheta g Q Z = ∑' X : Matrix (Fin n) (Fin g) ℤ, thTerm Q X Z := rfl

/-- The real matrix $C X$, for $H = C^{\mathsf T}C$. -/
def pmat (C : Matrix (Fin n) (Fin n) ℝ) (X : Matrix (Fin n) (Fin g) ℤ) : Matrix (Fin n) (Fin g) ℝ :=
  C * X.map ((↑) : ℤ → ℝ)

/-- $t_X = \operatorname{tr}(X^{\mathsf T}HX) = \sum_{a,i}(CX)_{a i}^2$. -/
def tsz (C : Matrix (Fin n) (Fin n) ℝ) (X : Matrix (Fin n) (Fin g) ℤ) : ℝ := ∑ a, ∑ i, pmat C X a i ^ 2

variable {Q} {C : Matrix (Fin n) (Fin n) ℝ} (hC : Q.hessian.map ((↑) : ℤ → ℝ) = Cᵀ * C)
include hC

theorem gram_eq (X : Matrix (Fin n) (Fin g) ℤ) :
    ((Xᵀ * Q.hessian * X).map ((↑) : ℤ → ℝ)) = (pmat C X)ᵀ * pmat C X := by
  have h1 : (Xᵀ * Q.hessian * X).map ((↑) : ℤ → ℝ) =
      (X.map ((↑) : ℤ → ℝ))ᵀ * Q.hessian.map ((↑) : ℤ → ℝ) * X.map ((↑) : ℤ → ℝ) := by
    have := Matrix.map_mul (f := Int.castRingHom ℝ) (L := Xᵀ * Q.hessian) (M := X)
    have h2 := Matrix.map_mul (f := Int.castRingHom ℝ) (L := Xᵀ) (M := Q.hessian)
    simp only [Int.coe_castRingHom] at this h2
    rw [this, h2, Matrix.transpose_map]
  rw [h1, hC]
  simp only [pmat, Matrix.transpose_mul, Matrix.mul_assoc]

theorem trace_gram (X : Matrix (Fin n) (Fin g) ℤ) :
    ∑ i, ((Xᵀ * Q.hessian * X).map ((↑) : ℤ → ℝ)) i i = tsz C X := by
  rw [gram_eq hC]
  simp only [tsz, mul_apply, transpose_apply, sq]
  rw [Finset.sum_comm]

omit hC in
theorem tsz_nonneg (X : Matrix (Fin n) (Fin g) ℤ) : 0 ≤ tsz C X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- $\|e^{\pi i\,\mathrm{tr}(AZ)}\| = e^{-\pi\sum_{ij}A_{ij}\operatorname{Im}Z_{ij}}$ for symmetric $Z$ and real $A$. -/
theorem norm_thTerm (X : Matrix (Fin n) (Fin g) ℤ) {Z : Matrix (Fin g) (Fin g) ℂ} (hZ : Zᵀ = Z) :
    ‖thTerm Q X Z‖ = Real.exp (-Real.pi * ∑ i, ∑ j, ((pmat C X)ᵀ * pmat C X) i j * (Z i j).im) := by
  rw [thTerm, Complex.norm_exp]
  congr 1
  have hM : (Xᵀ * Q.hessian * X).map (Int.cast : ℤ → ℂ) =
      ((Xᵀ * Q.hessian * X).map ((↑) : ℤ → ℝ)).map (Complex.ofReal) := by
    ext i j; simp
  rw [hM, gram_eq hC]
  generalize ((pmat C X)ᵀ * pmat C X) = G
  have hre : ∀ w : ℂ, (↑Real.pi * I * w).re = -Real.pi * w.im := by
    intro w; simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.im_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hzz : Z j i = Z i j := congrFun (congrFun hZ i) j
  rw [hzz, Complex.im_ofReal_mul]

/-- The Gaussian majorant $u_c(X) = e^{-\pi c\,t_X}$. -/
noncomputable def gaussU (C : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (X : Matrix (Fin n) (Fin g) ℤ) : ℝ :=
  Real.exp (-Real.pi * (c * tsz C X))

/-- **Domination by the majorant.** If $w^{\mathsf T}Yw \ge c\,w^{\mathsf T}w$ for $Y = \operatorname{Im}Z$, then
$\|e^{\pi i\,\mathrm{tr}(X^{\mathsf T}HXZ)}\| \le e^{-\pi c\,t_X}$. -/
theorem norm_thTerm_le (X : Matrix (Fin n) (Fin g) ℤ) {Z : Matrix (Fin g) (Fin g) ℂ} (hZ : Zᵀ = Z) {c : ℝ}
    (hc : ∀ w : Fin g → ℝ, c * (w ⬝ᵥ w) ≤ w ⬝ᵥ (Z.map Complex.im) *ᵥ w) :
    ‖thTerm Q X Z‖ ≤ gaussU C c X := by
  rw [norm_thTerm hC X hZ, gaussU]
  apply Real.exp_le_exp.mpr
  have h1 : ∑ i, ∑ j, ((pmat C X)ᵀ * pmat C X) i j * (Z i j).im =
      ∑ a, (fun j => pmat C X a j) ⬝ᵥ (Z.map Complex.im) *ᵥ (fun j => pmat C X a j) :=
    tm_sum_gram_aux (pmat C X) (Z.map Complex.im)
  have h2 : c * tsz C X ≤ ∑ i, ∑ j, ((pmat C X)ᵀ * pmat C X) i j * (Z i j).im := by
    rw [h1, tsz, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    have := hc (fun j => pmat C X a j)
    simpa [dotProduct, sq, Finset.mul_sum] using this
  nlinarith [Real.pi_pos]

omit hC in
theorem thetaArg_eq (X : Matrix (Fin n) (Fin g) ℤ) (Z : Matrix (Fin g) (Fin g) ℂ) :
    WeilRep.Genus.thetaArg (Q.hessian.map ((↑) : ℤ → ℝ)) Z (WeilRep.Genus.cZ X) =
      Real.pi * I * ((Xᵀ * Q.hessian * X).map (Int.cast : ℤ → ℂ) * Z).trace := by
  unfold WeilRep.Genus.thetaArg
  rw [WeilRep.Genus.cZ_quad]

omit hC in
/-- **Absolute convergence** of the series defining `siegelTheta` on $\mathbb{H}_g$. -/
theorem summable_norm_thTerm (hQ : IsEvenUnimodular Q) {Z : Matrix (Fin g) (Fin g) ℂ} (hZ : Z ∈ siegelUpper g) :
    Summable fun X : Matrix (Fin n) (Fin g) ℤ => ‖thTerm Q X Z‖ :=
  (WeilRep.Genus.summable_thetaG (hessianR_posDef hQ) hZ).congr fun X => by
    rw [thTerm, thetaArg_eq]

/-- The scalar point $c\,i \cdot 1 \in \mathbb{H}_g$. -/
noncomputable def scalarZ (g : ℕ) (c : ℝ) : Matrix (Fin g) (Fin g) ℂ := ((c : ℂ) * I) • (1 : Matrix (Fin g) (Fin g) ℂ)

omit hC in
theorem scalarZ_symm (c : ℝ) : (scalarZ g c)ᵀ = scalarZ g c := by
  simp [scalarZ]

omit hC in
theorem scalarZ_im (c : ℝ) : (scalarZ g c).map Complex.im = c • (1 : Matrix (Fin g) (Fin g) ℝ) := by
  ext i j
  by_cases h : i = j <;> simp [scalarZ, Matrix.one_apply, h]

omit hC in
theorem scalarZ_mem {c : ℝ} (hc : 0 < c) : scalarZ g c ∈ siegelUpper g :=
  ⟨scalarZ_symm c, by rw [scalarZ_im]; exact Matrix.PosDef.one.smul hc⟩

theorem summable_gaussU (hQ : IsEvenUnimodular Q) {c : ℝ} (hc : 0 < c) :
    Summable (gaussU C c : Matrix (Fin n) (Fin g) ℤ → ℝ) := by
  refine (summable_norm_thTerm hQ (scalarZ_mem (g := g) hc)).congr fun X => ?_
  rw [norm_thTerm hC X (scalarZ_symm c), gaussU]
  congr 2
  have : ∀ i j : Fin g, (scalarZ g c i j).im = if i = j then c else 0 := by
    intro i j; by_cases h : i = j <;> simp [scalarZ, Matrix.one_apply, h]
  simp only [this, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← gram_eq hC X, ← Finset.sum_mul, trace_gram hC X, mul_comm]

omit hC in
/-- **Boundedness** of $\vartheta_g(L)$ on $\{\operatorname{Im}Z \ge 1\}$. -/
theorem exists_bound_siegelTheta (hQ : IsEvenUnimodular Q) :
    ∃ B : ℝ, ∀ Z ∈ siegelUpper g, (Z.map Complex.im - 1).PosSemidef → ‖siegelTheta g Q Z‖ ≤ B := by
  obtain ⟨C, hC, -⟩ := WeilRep.Genus.exists_eq_transpose_mul (hessianR_posDef hQ)
  refine ⟨∑' X : Matrix (Fin n) (Fin g) ℤ, gaussU C 1 X, fun Z hZ hpsd => ?_⟩
  rw [siegelTheta_eq_tsum]
  refine tsum_of_norm_bounded (summable_gaussU hC hQ one_pos).hasSum fun X => norm_thTerm_le hC X hZ.1 ?_
  intro w
  have h := hpsd.dotProduct_mulVec_nonneg w
  simp only [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, star_trivial] at h
  linarith

end Analytic

/-! ### Holomorphy -/

section Holo

variable {Q : QuadForm ℤ n}

/-- The space of functions $\{0,\dots,g-1\}^2 \to \mathbb{C}$ with the sup norm: the same space as
$M_g(\mathbb{C})$ (which carries no global norm), used to apply the series-differentiation theorem. -/
abbrev EM (g : ℕ) := Fin g → Fin g → ℂ

/-- The symmetrization $W \mapsto \tfrac12(W + W^{\mathsf T})$. -/
noncomputable def symmM (W : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g) ℂ := (1 / 2 : ℂ) • (W + Wᵀ)

theorem norm_symm_entry_le (W : EM g) (i j : Fin g) : ‖symmM (Matrix.of W) i j‖ ≤ ‖W‖ := by
  have h1 : ‖W i j‖ ≤ ‖W‖ := (norm_le_pi_norm (W i) j).trans (norm_le_pi_norm W i)
  have h2 : ‖W j i‖ ≤ ‖W‖ := (norm_le_pi_norm (W j) i).trans (norm_le_pi_norm W j)
  simp only [symmM, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul, norm_mul]
  calc ‖(1 / 2 : ℂ)‖ * ‖W i j + W j i‖ ≤ ‖(1 / 2 : ℂ)‖ * (‖W i j‖ + ‖W j i‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ ≤ ‖W‖ := by
        have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
        rw [this]; linarith

/-- The matrix of the summand: $M_X = X^{\mathsf T}HX$ (as a complex matrix). -/
noncomputable def mC (Q : QuadForm ℤ n) (X : Matrix (Fin n) (Fin g) ℤ) : Matrix (Fin g) (Fin g) ℂ :=
  (Xᵀ * Q.hessian * X).map (Int.cast : ℤ → ℂ)

/-- The exponent $L_X(W) = \pi i\,\mathrm{tr}(M_X\,\mathrm{symmM}(W))$ as a $\mathbb{C}$-linear map. -/
noncomputable def linL (Q : QuadForm ℤ n) (X : Matrix (Fin n) (Fin g) ℤ) : EM g →ₗ[ℂ] ℂ where
  toFun W := Real.pi * I * (mC Q X * symmM (Matrix.of W)).trace
  map_add' W V := by
    show Real.pi * I * (mC Q X * symmM (Matrix.of (W + V))).trace = _
    have e : Matrix.of (W + V) = Matrix.of W + Matrix.of V := rfl
    rw [e]
    simp only [symmM, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, Matrix.transpose_add, smul_add, mul_add,
      Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    ring
  map_smul' c W := by
    show Real.pi * I * (mC Q X * symmM (Matrix.of (c • W))).trace = _
    have e : Matrix.of (c • W) = c • Matrix.of W := rfl
    rw [e]
    simp only [symmM, Matrix.transpose_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ← smul_add,
      RingHom.id_apply, Matrix.mul_add, Matrix.trace_add, smul_add, mul_add]
    ring

/-- The bound constant $K_X = \pi\sum_{i,j}|(M_X)_{ij}|$. -/
noncomputable def kConst (Q : QuadForm ℤ n) (X : Matrix (Fin n) (Fin g) ℤ) : ℝ :=
  Real.pi * ∑ i, ∑ j, ‖mC Q X i j‖

theorem norm_linL_le (X : Matrix (Fin n) (Fin g) ℤ) (W : EM g) :
    ‖linL Q X W‖ ≤ kConst Q X * ‖W‖ := by
  show ‖(Real.pi : ℂ) * I * (mC Q X * symmM (Matrix.of W)).trace‖ ≤ _
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_of_nonneg Real.pi_pos.le]
  rw [kConst, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  calc ‖∑ i, ∑ j, mC Q X i j * symmM (Matrix.of W) j i‖
        ≤ ∑ i, ‖∑ j, mC Q X i j * symmM (Matrix.of W) j i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖mC Q X i j * symmM (Matrix.of W) j i‖ :=
        Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖mC Q X i j‖ * ‖W‖ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_symm_entry_le W j i) (norm_nonneg _)
    _ = (∑ i, ∑ j, ‖mC Q X i j‖) * ‖W‖ := by simp only [Finset.sum_mul]

/-- The continuous linear exponent. -/
noncomputable def linC (Q : QuadForm ℤ n) (X : Matrix (Fin n) (Fin g) ℤ) : EM g →L[ℂ] ℂ :=
  (linL Q X).mkContinuous (kConst Q X) (norm_linL_le X)

theorem linC_apply (X : Matrix (Fin n) (Fin g) ℤ) (W : EM g) :
    linC Q X W = Real.pi * I * (mC Q X * symmM (Matrix.of W)).trace := rfl

theorem kConst_nonneg (X : Matrix (Fin n) (Fin g) ℤ) : 0 ≤ kConst Q X :=
  mul_nonneg Real.pi_pos.le (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)

theorem norm_linC_le (X : Matrix (Fin n) (Fin g) ℤ) : ‖linC Q X‖ ≤ kConst Q X :=
  LinearMap.mkContinuous_norm_le _ (kConst_nonneg X) _

theorem thTerm_eq (X : Matrix (Fin n) (Fin g) ℤ) (W : EM g) :
    thTerm Q X (symmM (Matrix.of W)) = Complex.exp (linC Q X W) := rfl

variable {C : Matrix (Fin n) (Fin n) ℝ} (hC : Q.hessian.map ((↑) : ℤ → ℝ) = Cᵀ * C)
include hC

/-- $\sum_{i,j}|(M_X)_{ij}| \le g\,t_X$ (Cauchy–Schwarz for the Gram matrix $M_X = (CX)^{\mathsf T}(CX)$). -/
theorem sum_norm_mC_le (X : Matrix (Fin n) (Fin g) ℤ) : ∑ i, ∑ j, ‖mC Q X i j‖ ≤ g * tsz C X := by
  have hm : ∀ i j, ‖mC Q X i j‖ ≤ ∑ a, (pmat C X a i ^ 2 + pmat C X a j ^ 2) / 2 := by
    intro i j
    have h := congrFun (congrFun (gram_eq hC X) i) j
    have h' : mC Q X i j = (((pmat C X)ᵀ * pmat C X) i j : ℝ) := by
      simp only [mC, Matrix.map_apply]
      have := h
      simp only [Matrix.map_apply] at this
      rw [← this]; simp
    rw [h', Complex.norm_real, Real.norm_eq_abs, Matrix.mul_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    simp only [Matrix.transpose_apply, abs_mul]
    nlinarith [sq_abs (pmat C X a i), sq_abs (pmat C X a j), sq_nonneg (|pmat C X a i| - |pmat C X a j|)]
  calc ∑ i, ∑ j, ‖mC Q X i j‖ ≤ ∑ i, ∑ j, ∑ a, (pmat C X a i ^ 2 + pmat C X a j ^ 2) / 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hm i j
    _ = g * tsz C X := by
        simp only [add_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, tsz]
        have hs : ∑ x, ∑ x1, pmat C X x1 x ^ 2 = ∑ a, ∑ i, pmat C X a i ^ 2 := Finset.sum_comm
        simp only [← Finset.sum_div, ← Finset.mul_sum, hs]
        ring

omit hC in
/-- **Stability of coercivity.** If $\operatorname{Im}\,\mathrm{symm}(W_0)$ has coercivity constant $c_0$, then for $W$ within
$c_0/(2(g+1))$ of $W_0$, $\operatorname{Im}\,\mathrm{symm}(W)$ has coercivity constant $c_0/2$. -/
theorem coercive_nbhd {W0 : EM g} {c0 : ℝ} (hc0 : 0 < c0)
    (h0 : ∀ w : Fin g → ℝ, c0 * (w ⬝ᵥ w) ≤ w ⬝ᵥ ((symmM (Matrix.of W0)).map Complex.im) *ᵥ w) {W : EM g}
    (hW : ‖W - W0‖ < c0 / (2 * (g + 1))) :
    ∀ w : Fin g → ℝ, (c0 / 2) * (w ⬝ᵥ w) ≤ w ⬝ᵥ ((symmM (Matrix.of W)).map Complex.im) *ᵥ w := by
  intro w
  set δ := ‖W - W0‖ with hδ
  have hD : ∀ i j, |((symmM (Matrix.of W)).map Complex.im) i j - ((symmM (Matrix.of W0)).map Complex.im) i j| ≤ δ := by
    intro i j
    have h1 := norm_symm_entry_le (W - W0) i j
    have e : symmM (Matrix.of (W - W0)) i j = symmM (Matrix.of W) i j - symmM (Matrix.of W0) i j := by
      simp only [symmM, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
      show (1 / 2 : ℂ) * ((W i j - W0 i j) + (W j i - W0 j i)) = (1 / 2 : ℂ) * (W i j + W j i) - (1 / 2 : ℂ) * (W0 i j + W0 j i)
      ring
    rw [e] at h1
    simp only [Matrix.map_apply]
    rw [← Complex.sub_im]
    exact (Complex.abs_im_le_norm _).trans h1
  have hq : ∀ Y : Matrix (Fin g) (Fin g) ℝ, w ⬝ᵥ Y *ᵥ w = ∑ i, ∑ j, w i * Y i j * w j := by
    intro Y
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  set Y := (symmM (Matrix.of W)).map Complex.im
  set Y0 := (symmM (Matrix.of W0)).map Complex.im
  have hdiff : |∑ i, ∑ j, w i * (Y i j - Y0 i j) * w j| ≤ δ * (g * (w ⬝ᵥ w)) := by
    calc |∑ i, ∑ j, w i * (Y i j - Y0 i j) * w j| ≤ ∑ i, ∑ j, |w i * (Y i j - Y0 i j) * w j| :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i, ∑ j, |w i| * δ * |w j| := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hD i j) (abs_nonneg _)) (abs_nonneg _)
      _ = δ * (∑ i, |w i|) ^ 2 := by
          rw [sq, Finset.sum_mul_sum]
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ ≤ δ * (g * (w ⬝ᵥ w)) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |w i|)
          simpa [dotProduct, sq, Finset.card_univ, sq_abs] using this
  have hsplit : w ⬝ᵥ Y *ᵥ w = w ⬝ᵥ Y0 *ᵥ w + ∑ i, ∑ j, w i * (Y i j - Y0 i j) * w j := by
    rw [hq, hq]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hww : 0 ≤ w ⬝ᵥ w := by
    simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hδg : δ * g ≤ c0 / 2 := by
    have : δ * (2 * (g + 1)) ≤ c0 := by
      have := mul_le_mul_of_nonneg_right hW.le (show (0:ℝ) ≤ 2 * (g + 1) by positivity)
      rwa [div_mul_cancel₀ _ (by positivity)] at this
    nlinarith [norm_nonneg (W - W0), (Nat.cast_nonneg g : (0:ℝ) ≤ g)]
  have := h0 w
  have h3 := neg_abs_le (∑ i, ∑ j, w i * (Y i j - Y0 i j) * w j)
  nlinarith [mul_le_mul_of_nonneg_right hδg hww]

omit hC in
/-- Elementary: $t\,e^{-2at} \le e^{-at}/a$ for $a > 0$, $t \ge 0$. -/
theorem mul_exp_le {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    t * Real.exp (-(2 * a) * t) ≤ Real.exp (-a * t) / a := by
  rw [le_div_iff₀ ha]
  have h1 : a * t ≤ Real.exp (a * t) := by linarith [Real.add_one_le_exp (a * t)]
  have h2 : Real.exp (a * t) * Real.exp (-(2 * a) * t) = Real.exp (-a * t) := by
    rw [← Real.exp_add]; congr 1; ring
  calc t * Real.exp (-(2 * a) * t) * a = (a * t) * Real.exp (-(2 * a) * t) := by ring
    _ ≤ Real.exp (a * t) * Real.exp (-(2 * a) * t) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = _ := h2

omit hC in
theorem symmM_transpose (W : Matrix (Fin g) (Fin g) ℂ) : (symmM W)ᵀ = symmM W := by
  simp [symmM, add_comm]

omit hC in
theorem exists_coercive_symm {W0 : EM g} (h : symmM (Matrix.of W0) ∈ siegelUpper g) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ w : Fin g → ℝ, c0 * (w ⬝ᵥ w) ≤ w ⬝ᵥ ((symmM (Matrix.of W0)).map Complex.im) *ᵥ w :=
  tm_exists_coercive h.2

omit hC in
/-- **Holomorphy** of $\vartheta_g(L)$ at one point (complex Fréchet differentiability of the function
$W \mapsto \vartheta_g(L)(\tfrac12(W + W^{\mathsf T}))$ on $\mathbb{C}^{g \times g}$), by termwise differentiation. -/
theorem differentiableAt_siegelTheta (hQ : IsEvenUnimodular Q) {W0 : EM g}
    (hW0 : symmM (Matrix.of W0) ∈ siegelUpper g) :
    DifferentiableAt ℂ (fun W : EM g => siegelTheta g Q (symmM (Matrix.of W))) W0 := by
  obtain ⟨C, hC, -⟩ := WeilRep.Genus.exists_eq_transpose_mul (hessianR_posDef hQ)
  obtain ⟨c0, hc0, h0⟩ := exists_coercive_symm hW0
  set δ : ℝ := c0 / (2 * (g + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  set c' : ℝ := c0 / 2 with hc'
  have hc'pos : 0 < c' := by positivity
  set a : ℝ := Real.pi * c' / 2 with ha
  have hapos : 0 < a := by positivity
  let u : Matrix (Fin n) (Fin g) ℤ → ℝ := fun X => Real.pi * g / a * gaussU C (c' / 2) X
  have hu : Summable u := (summable_gaussU hC hQ (by positivity : 0 < c' / 2)).mul_left _
  have hf : ∀ X : Matrix (Fin n) (Fin g) ℤ, ∀ W ∈ Metric.ball W0 δ,
      HasFDerivAt (fun W : EM g => Complex.exp (linC Q X W)) (Complex.exp (linC Q X W) • linC Q X) W :=
    fun X W _ => (linC Q X).hasFDerivAt.cexp
  have hf' : ∀ X : Matrix (Fin n) (Fin g) ℤ, ∀ W ∈ Metric.ball W0 δ,
      ‖Complex.exp (linC Q X W) • linC Q X‖ ≤ u X := by
    intro X W hW
    rw [Metric.mem_ball, dist_eq_norm] at hW
    have hco := coercive_nbhd hc0 h0 hW
    have hterm : ‖Complex.exp (linC Q X W)‖ ≤ gaussU C c' X := by
      have := norm_thTerm_le hC X (symmM_transpose (Matrix.of W)) hco
      exact this
    have hk : kConst Q X ≤ Real.pi * g * tsz C X := by
      rw [kConst, mul_assoc]
      exact mul_le_mul_of_nonneg_left (sum_norm_mC_le hC X) Real.pi_pos.le
    calc ‖Complex.exp (linC Q X W) • linC Q X‖ = ‖Complex.exp (linC Q X W)‖ * ‖linC Q X‖ := norm_smul _ _
      _ ≤ gaussU C c' X * (Real.pi * g * tsz C X) :=
          mul_le_mul hterm ((norm_linC_le X).trans hk) (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ u X := by
          have hm := mul_exp_le hapos (tsz_nonneg X : 0 ≤ tsz C X)
          have e1 : gaussU C c' X = Real.exp (-(2 * a) * tsz C X) := by
            simp only [gaussU, ha]; congr 1; ring
          have e2 : gaussU C (c' / 2) X = Real.exp (-a * tsz C X) := by
            simp only [gaussU, ha]; congr 1; ring
          simp only [u]
          rw [e1, e2]
          have : Real.exp (-(2 * a) * tsz C X) * (Real.pi * g * tsz C X) =
              Real.pi * g * (tsz C X * Real.exp (-(2 * a) * tsz C X)) := by ring
          rw [this]
          calc Real.pi * g * (tsz C X * Real.exp (-(2 * a) * tsz C X)) ≤ Real.pi * g * (Real.exp (-a * tsz C X) / a) :=
                mul_le_mul_of_nonneg_left hm (by positivity)
            _ = _ := by ring
  have hf0 : Summable fun X : Matrix (Fin n) (Fin g) ℤ => Complex.exp (linC Q X W0) :=
    (summable_norm_thTerm hQ hW0).of_norm
  have key := hasFDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball (convex_ball W0 δ).isPreconnected hf hf'
    (Metric.mem_ball_self hδpos) hf0 (Metric.mem_ball_self hδpos)
  have hfun : (fun W : EM g => siegelTheta g Q (symmM (Matrix.of W))) =
      fun W => ∑' X : Matrix (Fin n) (Fin g) ℤ, Complex.exp (linC Q X W) := by
    funext W; exact siegelTheta_eq_tsum Q _
  rw [hfun]
  exact key.differentiableAt

end Holo

/-! ### The theorem -/

/-- **Siegel's theorem, proved** (Chenevier–Lannes, §5.1, p. 123; Freitag, Kap. I, §0 and Anhang): for an even unimodular
lattice $L$ of dimension $n$ (given by the integral form $Q$) and every genus $g$, the Siegel theta series
$\vartheta_g(L)$ is a Siegel modular form of weight $n/2$ for $\mathrm{Sp}_{2g}(\mathbb{Z})$. Unconditional.
*Proof:* the transformation law is `WeilRep.Genus.thetaG_sp_uncond` (generation of $\mathrm{Sp}_{2g}(\mathbb{Z})$ by
translations and the inversion, plus Poisson summation); holomorphy is termwise differentiation of the series with
Gaussian majorants (`differentiableAt_siegelTheta`); boundedness on $\operatorname{Im}Z \ge 1$ is
`exists_bound_siegelTheta`. -/
@[kb "chenevierlannes2019" "§5.1, p. 123 (ϑ_g(L) ∈ M_{n/2}(Sp_2g(Z)))"]
theorem siegelThetaModular_of_evenUnimodular {n : ℕ} (Q : QuadForm ℤ n) (hQ : IsEvenUnimodular Q) (g : ℕ) :
    IsSiegelModularForm ((n / 2 : ℕ) : ℤ) g (siegelTheta g Q) := by
  refine ⟨?_, ?_, exists_bound_siegelTheta hQ⟩
  · intro W hW
    exact (differentiableAt_siegelTheta hQ (W0 := W) hW).differentiableWithinAt
  · obtain ⟨k, rfl⟩ := exists_two_mul_of_isEvenUnimodular hQ
    rw [Nat.mul_div_cancel_left k two_pos]
    exact siegelTheta_modular_aux k hQ

/-- **`SiegelThetaModular` holds** (unconditional): the named statement of `Theta.lean` is a theorem. -/
@[kb "chenevierlannes2019" "§5.1, p. 123 (ϑ_g(L) ∈ M_{n/2}(Sp_2g(Z)))"]
theorem siegelThetaModular : SiegelThetaModular :=
  fun _ Q hQ g _ => siegelThetaModular_of_evenUnimodular Q hQ g

end QuadFormsKB.ChenevierLannes
