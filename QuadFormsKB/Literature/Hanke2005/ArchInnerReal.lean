/-
# Hanke 2005, §4.2: the first $q$ columns over a fixed negative frame

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Setting.** $\varphi = \mathrm{diag}[1_q, -1_r]$ on $\mathbb R^{q+r}$ (`phiQR q r`). Fix $r$ vectors $u_2 = (u_c)_{c<r}$
whose Gram matrix $T = ({}^tu_c\varphi u_d)_{cd}$ (`gramMat`) is negative definite. Then $u_2^{\perp}$ is positive definite:
the vectors $E_a = e_a - \sum_d (T^{-1}U_a)_d\,u_d$ ($U_{ad} = (u_d)_a$, $a < q$) satisfy ${}^tE_a\varphi u_c = 0$ and
${}^tE_a\varphi E_b = H_{ab}$, $H = 1 - UT^{-1}{}^tU$ positive definite.

**Proves** `lintegral_inner`: for every $\varepsilon$,
$$\int_{X_1\in\mathbb R^{(q+r)\times q}}\big[\det(X_1, u_2) > 0,\ G_\varphi(X_1)\in\mathrm{boxD}_q(\varepsilon),\
{}^tX_1\varphi u_2\in\mathrm{box}_{12}(\varepsilon)\big]\,dX_1 = \frac{|\det T|^{-q/2}}2\,J_\varepsilon(T),$$
by the substitution $X_1 = M\begin{bmatrix}B\\A\end{bmatrix}$, $M = (E\mid u_2)$, ${}^tM\varphi M = \mathrm{diag}(H, T)$,
$|\det M|^2 = \det H\,|\det T|$; then $G_\varphi(X_1) = G_H(B) + G_T(A)$, ${}^tX_1\varphi u_2 = TA$ and
$\det(X_1, u_2) = \det M\det B$; the $B$-integral is the weighted Gram formula with sign (`lintegral_gramH_det_pos`)
and $A\mapsto TA$ has Jacobian $|\det T|^q$.
-/
import QuadFormsKB.Literature.Hanke2005.ArchLimitReal
import QuadFormsKB.Literature.Hanke2005.ArchMeasAux

open MeasureTheory Matrix Set
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.ArchReal

open QuadFormsKB.Tamagawa.ArchVol

variable {q r : ℕ}

/-- The signs $(1_q, -1_r)$. -/
def sgnQR (q r : ℕ) : Fin (q + r) → ℝ := fun i => Fin.addCases (motive := fun _ => ℝ) (fun _ => 1) (fun _ => -1) i

/-- $\varphi = \mathrm{diag}[1_q, -1_r]$. -/
def phiQR (q r : ℕ) : Matrix (Fin (q + r)) (Fin (q + r)) ℝ := diagonal (sgnQR q r)

/-- The Gram matrix $({}^tX_cHX_d)_{cd}$ of a family of vectors. -/
def gramMat {k m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (X : Fin k → Fin m → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun c d => X c ⬝ᵥ (H *ᵥ X d)

theorem phiQR_transpose : (phiQR q r)ᵀ = phiQR q r := diagonal_transpose _

theorem gramMat_transpose {k m : ℕ} {H : Matrix (Fin m) (Fin m) ℝ} (hH : Hᵀ = H) (X : Fin k → Fin m → ℝ) :
    (gramMat H X)ᵀ = gramMat H X := by
  ext c d
  simp only [gramMat, transpose_apply, of_apply]
  rw [dotProduct_mulVec, ← mulVec_transpose, hH, dotProduct_comm]

/-! ### The complementary frame -/

section Frame

variable (u : Fin r → Fin (q + r) → ℝ)

/-- $U_{ad} = (u_d)_a$, the first $q$ coordinates of the frame. -/
def topU : Matrix (Fin q) (Fin r) ℝ := Matrix.of fun a d => u d (Fin.castAdd r a)

/-- $E_a = e_a - \sum_d (T^{-1}U_a)_d\,u_d$. -/
def compE (a : Fin q) : Fin (q + r) → ℝ :=
  Pi.single (Fin.castAdd r a) 1 - ∑ d, ((gramMat (phiQR q r) u)⁻¹ *ᵥ (topU u a)) d • u d

/-- $H = 1 - UT^{-1}{}^tU$. -/
def compH : Matrix (Fin q) (Fin q) ℝ := 1 - topU u * (gramMat (phiQR q r) u)⁻¹ * (topU u)ᵀ

/-- $M = (E\mid u_2)$ (columns). -/
def frameM : Matrix (Fin (q + r)) (Fin (q + r)) ℝ := Matrix.of fun i j => Fin.append (compE u) u j i

theorem phiQR_mulVec_single (a : Fin q) :
    phiQR q r *ᵥ Pi.single (Fin.castAdd r a) 1 = Pi.single (Fin.castAdd r a) 1 := by
  funext i
  rw [phiQR, mulVec_diagonal]
  by_cases h : i = Fin.castAdd r a
  · subst h; simp [sgnQR]
  · simp [Pi.single_apply, h]

theorem single_dot_phiQR (a : Fin q) (x : Fin (q + r) → ℝ) :
    Pi.single (Fin.castAdd r a) 1 ⬝ᵥ (phiQR q r *ᵥ x) = x (Fin.castAdd r a) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, phiQR_transpose, phiQR_mulVec_single, dotProduct_comm,
    dotProduct_single, mul_one]

variable {u}

theorem T_symm : (gramMat (phiQR q r) u)ᵀ = gramMat (phiQR q r) u := gramMat_transpose phiQR_transpose u

theorem inv_T_symm : ((gramMat (phiQR q r) u)⁻¹)ᵀ = (gramMat (phiQR q r) u)⁻¹ := by
  rw [transpose_nonsing_inv, T_symm]

theorem dot_phi_comm (x y : Fin (q + r) → ℝ) : x ⬝ᵥ (phiQR q r *ᵥ y) = y ⬝ᵥ (phiQR q r *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, phiQR_transpose, dotProduct_comm]

variable (hT : (-(gramMat (phiQR q r) u)).PosDef)
include hT

theorem isUnit_det_T : IsUnit (gramMat (phiQR q r) u).det := by
  have h := hT.det_pos
  rw [det_neg] at h
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, mul_zero] at h; exact lt_irrefl _ h

theorem compE_dot_u (a : Fin q) (c : Fin r) : compE u a ⬝ᵥ (phiQR q r *ᵥ u c) = 0 := by
  set T := gramMat (phiQR q r) u
  rw [compE, sub_dotProduct, single_dot_phiQR, sum_dotProduct]
  simp only [smul_dotProduct]
  have h1 : ∀ d, u d ⬝ᵥ (phiQR q r *ᵥ u c) = T d c := fun d => rfl
  simp only [h1, smul_eq_mul]
  have h2 : ∑ d, (T⁻¹ *ᵥ topU u a) d * T d c = (T *ᵥ (T⁻¹ *ᵥ topU u a)) c := by
    rw [mulVec, dotProduct]
    have hs : ∀ i j, T i j = T j i := fun i j => (congrFun (congrFun (T_symm (u := u)) j) i)
    rw [show (fun x => (T⁻¹ *ᵥ topU u a) x * T x c) = fun x => T c x * (T⁻¹ *ᵥ topU u a) x from by
      funext x; rw [mul_comm, hs]]
  rw [h2, mulVec_mulVec, mul_nonsing_inv _ (isUnit_det_T hT), one_mulVec]
  simp [topU]

theorem compE_dot_compE (a b : Fin q) : compE u a ⬝ᵥ (phiQR q r *ᵥ compE u b) = compH u a b := by
  set T := gramMat (phiQR q r) u
  rw [dot_phi_comm, compE, sub_dotProduct, single_dot_phiQR, sum_dotProduct]
  simp only [smul_dotProduct, dot_phi_comm (u _) (compE u a), compE_dot_u hT, smul_zero, Finset.sum_const_zero,
    sub_zero]
  rw [compE]
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, compH, Matrix.sub_apply, one_apply]
  rw [Pi.single_apply]
  simp only [Fin.castAdd_inj, Matrix.mul_apply, transpose_apply, topU, of_apply]
  congr 1
  · by_cases h : b = a
    · simp [h]
    · simp [h, Ne.symm h]
  · simp only [mulVec, dotProduct, of_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
    have := congrFun (congrFun (inv_T_symm (u := u)) c) d
    simp only [transpose_apply] at this
    rw [this]; ring

theorem compH_posDef : (compH u).PosDef := by
  set T := gramMat (phiQR q r) u
  have h1 : (-T)⁻¹.PosDef := hT.inv
  have h2 : (topU u * (-T)⁻¹ * (topU u)ᵀ).PosSemidef := by
    have := h1.posSemidef.mul_mul_conjTranspose_same (topU u)
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  have hneg : (-T)⁻¹ = -T⁻¹ := Matrix.inv_eq_left_inv (by
    rw [neg_mul_neg, nonsing_inv_mul _ (isUnit_det_T hT)])
  have h3 : compH u = 1 + topU u * (-T)⁻¹ * (topU u)ᵀ := by
    rw [compH, hneg, Matrix.mul_neg, Matrix.neg_mul, sub_eq_add_neg]
  rw [h3]
  exact PosDef.one.add_posSemidef h2

end Frame

/-! ### The matrix $M = (E\mid u_2)$ -/

section M

variable {u : Fin r → Fin (q + r) → ℝ}

/-- The block diagonal matrix $\mathrm{diag}(H, T)$, indexed by `Fin (q + r)`. -/
def blockHT (H : Matrix (Fin q) (Fin q) ℝ) (T : Matrix (Fin r) (Fin r) ℝ) : Matrix (Fin (q + r)) (Fin (q + r)) ℝ :=
  Matrix.of fun i j => Fin.addCases (motive := fun _ => ℝ)
    (fun a => Fin.addCases (motive := fun _ => ℝ) (fun b => H a b) (fun _ => 0) j)
    (fun c => Fin.addCases (motive := fun _ => ℝ) (fun _ => 0) (fun d => T c d) j) i

theorem blockHT_reindex (H : Matrix (Fin q) (Fin q) ℝ) (T : Matrix (Fin r) (Fin r) ℝ) :
    (blockHT H T).submatrix finSumFinEquiv finSumFinEquiv = fromBlocks H 0 0 T := by
  ext (a | c) (b | d) <;> simp [blockHT, fromBlocks]

theorem det_blockHT (H : Matrix (Fin q) (Fin q) ℝ) (T : Matrix (Fin r) (Fin r) ℝ) :
    (blockHT H T).det = H.det * T.det := by
  rw [← det_submatrix_equiv_self finSumFinEquiv, blockHT_reindex, det_fromBlocks_zero₂₁]

theorem det_phiQR : (phiQR q r).det = (-1) ^ r := by
  rw [phiQR, det_diagonal, Fin.prod_univ_add]
  simp [sgnQR]

theorem dot_blockHT_append (β β' : Fin q → ℝ) (α α' : Fin r → ℝ) (H : Matrix (Fin q) (Fin q) ℝ)
    (T : Matrix (Fin r) (Fin r) ℝ) :
    Fin.append β α ⬝ᵥ (blockHT H T *ᵥ Fin.append β' α') = β ⬝ᵥ (H *ᵥ β') + α ⬝ᵥ (T *ᵥ α') := by
  simp only [dotProduct, mulVec, Fin.sum_univ_add, blockHT, of_apply, Fin.addCases_left, Fin.addCases_right,
    Fin.append_left, Fin.append_right, zero_mul, Finset.sum_const_zero, add_zero, zero_add]

theorem frameM_col (j : Fin (q + r)) : (fun i => frameM u i j) = Fin.append (compE u) u j := rfl

variable (hT : (-(gramMat (phiQR q r) u)).PosDef)
include hT

theorem frameM_gram : (frameM u)ᵀ * phiQR q r * frameM u = blockHT (compH u) (gramMat (phiQR q r) u) := by
  ext i j
  have h : ((frameM u)ᵀ * phiQR q r * frameM u) i j =
      Fin.append (compE u) u i ⬝ᵥ (phiQR q r *ᵥ Fin.append (compE u) u j) := by
    simp only [Matrix.mul_apply, transpose_apply, dotProduct, mulVec, frameM, of_apply, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [h]
  refine Fin.addCases (fun a => ?_) (fun c => ?_) i <;> refine Fin.addCases (fun b => ?_) (fun d => ?_) j
  · simp [blockHT, compE_dot_compE hT]
  · simp [blockHT, compE_dot_u hT]
  · simp [blockHT, dot_phi_comm (u c) (compE u b), compE_dot_u hT]
  · simp [blockHT, gramMat]

theorem sq_det_frameM : (frameM u).det ^ 2 = (compH u).det * |(gramMat (phiQR q r) u).det| := by
  set T := gramMat (phiQR q r) u
  have h1 := congrArg Matrix.det (frameM_gram hT)
  rw [det_mul, det_mul, det_transpose, det_phiQR, det_blockHT] at h1
  have hneg : (-T).det = (-1) ^ r * T.det := by rw [det_neg, Fintype.card_fin]
  have hpos : 0 < (-1) ^ r * T.det := hneg ▸ hT.det_pos
  have habs : |T.det| = (-1) ^ r * T.det := by
    have : |T.det| = |(-1) ^ r * T.det| := by rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [this, abs_of_pos hpos]
  rw [habs]
  have hs : ((-1 : ℝ) ^ r) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  calc (frameM u).det ^ 2 = (frameM u).det ^ 2 * ((-1) ^ r) ^ 2 := by rw [hs, mul_one]
    _ = ((frameM u).det * (-1) ^ r * (frameM u).det) * (-1) ^ r := by ring
    _ = (compH u).det * ((-1) ^ r * T.det) := by rw [h1]; ring

theorem det_frameM_ne_zero : (frameM u).det ≠ 0 := by
  intro h0
  have h := sq_det_frameM hT
  rw [h0] at h
  have hH := (compH_posDef hT).det_pos
  have hT0 : 0 < |(gramMat (phiQR q r) u).det| := abs_pos.mpr (isUnit_det_T hT).ne_zero
  nlinarith [mul_pos hH hT0]

theorem frameM_mulVec_single (c : Fin r) : frameM u *ᵥ Pi.single (Fin.natAdd q c) 1 = u c := by
  funext i
  simp [frameM, mulVec, dotProduct, Pi.single_apply]

/-- $(My)\cdot\varphi(My') = y\cdot\mathrm{diag}(H, T)\,y'$. -/
theorem frameM_dot (y y' : Fin (q + r) → ℝ) :
    (frameM u *ᵥ y) ⬝ᵥ (phiQR q r *ᵥ (frameM u *ᵥ y')) =
      y ⬝ᵥ (blockHT (compH u) (gramMat (phiQR q r) u) *ᵥ y') := by
  rw [← frameM_gram hT, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

end M

/-! ### The inner integral -/

theorem const_inner {h τ : ℝ} (hh : 0 < h) (hτ : 0 < τ) (q : ℕ) :
    (h ^ (1 / 2 : ℝ) * τ ^ (1 / 2 : ℝ)) ^ q * (h ^ (-(q : ℝ) / 2) / 2) * τ⁻¹ ^ q = τ ^ (-(q : ℝ) / 2) / 2 := by
  rw [mul_pow, ← Real.rpow_natCast (h ^ (1 / 2 : ℝ)), ← Real.rpow_natCast (τ ^ (1 / 2 : ℝ)),
    ← Real.rpow_mul hh.le, ← Real.rpow_mul hτ.le, inv_pow, ← Real.rpow_natCast τ, ← Real.rpow_neg hτ.le]
  have e1 : h ^ ((1 / 2 : ℝ) * q) * h ^ (-(q : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hh]; ring_nf; exact Real.rpow_zero h
  have e2 : τ ^ ((1 / 2 : ℝ) * q) * τ ^ (-(q : ℝ)) = τ ^ (-(q : ℝ) / 2) := by
    rw [← Real.rpow_add hτ]; ring_nf
  calc h ^ ((1 / 2 : ℝ) * q) * τ ^ ((1 / 2 : ℝ) * q) * (h ^ (-(q : ℝ) / 2) / 2) * τ ^ (-(q : ℝ))
      = (h ^ ((1 / 2 : ℝ) * q) * h ^ (-(q : ℝ) / 2)) * (τ ^ ((1 / 2 : ℝ) * q) * τ ^ (-(q : ℝ))) / 2 := by ring
    _ = τ ^ (-(q : ℝ) / 2) / 2 := by rw [e1, e2, one_mul]

section Inner

variable {u : Fin r → Fin (q + r) → ℝ}

theorem castAdd_ne_natAdd (a : Fin q) (c : Fin r) : (Fin.castAdd r a : Fin (q + r)) ≠ Fin.natAdd q c := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem single_natAdd_eq_append (c : Fin r) :
    (Pi.single (Fin.natAdd q c) 1 : Fin (q + r) → ℝ) = Fin.append (0 : Fin q → ℝ) (Pi.single c 1) := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun d => ?_) i
  · simp [Pi.single_apply, castAdd_ne_natAdd]
  · by_cases h : d = c
    · subst h; simp
    · simp [Pi.single_apply, h]

/-- The measurable function $h\mapsto\int\rho_q(s)\,[s + h\in\mathrm{boxD}_q(\varepsilon)]\,ds$. -/
def shiftInt (q : ℕ) (ε : ℝ) (h : UIdx q → ℝ) : ℝ≥0∞ := ∫⁻ s, densR q s * (boxD q ε).indicator 1 (s + h)

theorem measurable_shiftInt (q : ℕ) (ε : ℝ) : Measurable (shiftInt q ε) := by
  have hm : Measurable fun p : (UIdx q → ℝ) × (UIdx q → ℝ) => densR q p.2 * (boxD q ε).indicator 1 (p.2 + p.1) :=
    ((measurable_densR q).comp measurable_snd).mul
      ((measurable_one.indicator (measurableSet_boxD q ε)).comp (measurable_snd.add measurable_fst))
  exact hm.lintegral_prod_right'

theorem Jint_eq (ε : ℝ) (T : Matrix (Fin r) (Fin r) ℝ) :
    Jint q r ε T = ∫⁻ A, (box12 q r ε).indicator (fun A => shiftInt q ε (gramH T⁻¹ A)) A := rfl

theorem continuous_gramH {k m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) :
    Continuous (gramH (k := k) H) := by
  refine continuous_pi fun p => ?_
  simp only [gramH, dotProduct, mulVec]
  fun_prop

variable (hT : (-(gramMat (phiQR q r) u)).PosDef)
include hT

theorem det_append_frame (β : Fin q → Fin q → ℝ) (α : Fin q → Fin r → ℝ) :
    (Matrix.of (Fin.append (fun a => frameM u *ᵥ Fin.append (β a) (α a)) u)).det =
      (Matrix.of β).det * (frameM u).det := by
  set W : Matrix (Fin (q + r)) (Fin (q + r)) ℝ :=
    Matrix.of (Fin.append (fun a => Fin.append (β a) (α a)) fun c => Pi.single (Fin.natAdd q c) 1)
  have hW : Matrix.of (Fin.append (fun a => frameM u *ᵥ Fin.append (β a) (α a)) u) = W * (frameM u)ᵀ := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [transpose_apply]
    refine Fin.addCases (fun a => ?_) (fun c => ?_) i
    · simp only [of_apply, Fin.append_left, W, mulVec, dotProduct]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    · simp only [of_apply, Fin.append_right, W]
      rw [← frameM_mulVec_single hT c]
      simp only [mulVec, dotProduct]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hdetW : W.det = (Matrix.of β).det := by
    rw [← det_submatrix_equiv_self finSumFinEquiv]
    have : W.submatrix finSumFinEquiv finSumFinEquiv = fromBlocks (Matrix.of β) (Matrix.of α) 0 1 := by
      ext (a | c) (b | d)
      · simp [W]
      · simp [W]
      · simp [W, Pi.single_apply, (castAdd_ne_natAdd _ _).symm]
      · by_cases h : c = d
        · subst h; simp [W]
        · simp [W, Pi.single_apply, Ne.symm h, h]
    rw [this, det_fromBlocks_zero₂₁, det_one, mul_one]
  rw [hW, det_mul, det_transpose, hdetW]

theorem gramH_frame (β : Fin q → Fin q → ℝ) (α : Fin q → Fin r → ℝ) :
    gramH (phiQR q r) (fun a => frameM u *ᵥ Fin.append (β a) (α a)) =
      gramH (compH u) β + gramH (gramMat (phiQR q r) u) α := by
  funext p
  simp only [gramH, Pi.add_apply, frameM_dot hT, dot_blockHT_append]

theorem cross_frame (β : Fin q → Fin q → ℝ) (α : Fin q → Fin r → ℝ) :
    (fun a c => (frameM u *ᵥ Fin.append (β a) (α a)) ⬝ᵥ (phiQR q r *ᵥ u c)) =
      fun a c => (gramMat (phiQR q r) u *ᵥ α a) c := by
  funext a c
  rw [← frameM_mulVec_single hT c, frameM_dot hT, single_natAdd_eq_append, dot_blockHT_append]
  simp only [mulVec_zero, dotProduct_zero, zero_add]
  rw [mulVec_single_one, dotProduct_comm]
  have hs : ∀ i j, gramMat (phiQR q r) u i j = gramMat (phiQR q r) u j i := fun i j =>
    (congrFun (congrFun (T_symm (u := u)) j) i)
  simp only [mulVec, dotProduct, col_apply]
  exact Finset.sum_congr rfl fun d _ => by rw [hs, mul_comm]

theorem gramH_mulVec_inv (α : Fin q → Fin r → ℝ) :
    gramH (gramMat (phiQR q r) u) α = gramH (gramMat (phiQR q r) u)⁻¹ (fun a => gramMat (phiQR q r) u *ᵥ α a) := by
  funext p
  simp only [gramH]
  rw [mulVec_mulVec, nonsing_inv_mul _ (isUnit_det_T hT), one_mulVec, dotProduct_mulVec]
  congr 1
  conv_lhs => rw [← T_symm (u := u)]
  rw [vecMul_transpose]

/-- **The inner integral over the first $q$ columns.** -/
theorem lintegral_inner (hq : 1 ≤ q) (ε : ℝ) :
    ∫⁻ X1 : Fin q → Fin (q + r) → ℝ,
        {X1 : Fin q → Fin (q + r) → ℝ | 0 < (Matrix.of (Fin.append X1 u)).det ∧
          gramH (phiQR q r) X1 ∈ boxD q ε ∧
          (fun a c => X1 a ⬝ᵥ (phiQR q r *ᵥ u c)) ∈ box12 q r ε}.indicator 1 X1 =
      ENNReal.ofReal (|(gramMat (phiQR q r) u).det| ^ (-(q : ℝ) / 2) / 2) * Jint q r ε (gramMat (phiQR q r) u) := by
  classical
  set T := gramMat (phiQR q r) u with hTdef
  set M := frameM u
  set H := compH u
  have hMd : M.det ≠ 0 := det_frameM_ne_zero hT
  have hTd : T.det ≠ 0 := (isUnit_det_T hT).ne_zero
  have hHpos := compH_posDef hT
  set S := {X1 : Fin q → Fin (q + r) → ℝ | 0 < (Matrix.of (Fin.append X1 u)).det ∧
          gramH (phiQR q r) X1 ∈ boxD q ε ∧ (fun a c => X1 a ⬝ᵥ (phiQR q r *ᵥ u c)) ∈ box12 q r ε}
  have hSm : MeasurableSet S := by
    have hdet : Continuous fun X1 : Fin q → Fin (q + r) → ℝ => (Matrix.of (Fin.append X1 u)).det := by
      refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
      refine Fin.addCases (fun a => ?_) (fun c => ?_) i
      · simp only [of_apply, Fin.append_left]; fun_prop
      · simp only [of_apply, Fin.append_right]; fun_prop
    have hcross : Continuous fun X1 : Fin q → Fin (q + r) → ℝ => fun a c => X1 a ⬝ᵥ (phiQR q r *ᵥ u c) := by
      simp only [dotProduct]; fun_prop
    exact (measurableSet_lt measurable_const hdet.measurable).inter
      (((measurableSet_boxD q ε).preimage (continuous_gramH _).measurable).inter
        ((measurableSet_box12 q r ε).preimage hcross.measurable))
  set F : (Fin q → Fin (q + r) → ℝ) → ℝ≥0∞ := S.indicator 1
  have hF : Measurable F := measurable_one.indicator hSm
  -- step 1: substitute X1 = M Y
  have h1 := lintegral_comp_mulVec_rect M hMd hF
  have hstep1 : ∫⁻ X1, F X1 = ENNReal.ofReal |M.det| ^ q * ∫⁻ Y : Fin q → Fin (q + r) → ℝ, F (fun a => M *ᵥ Y a) := by
    rw [h1, ← mul_assoc, ← mul_pow, ← ENNReal.ofReal_mul (abs_nonneg _),
      mul_inv_cancel₀ (abs_pos.mpr hMd).ne', ENNReal.ofReal_one, one_pow, one_mul]
  -- step 2: split Y = (B; A)
  have hFM : Measurable fun Y : Fin q → Fin (q + r) → ℝ => F (fun a => M *ᵥ Y a) :=
    hF.comp (measurable_pi_iff.mpr fun a => (Matrix.toLin' M).continuous_of_finiteDimensional.measurable.comp
      (measurable_pi_apply a))
  rw [hstep1, lintegral_pi_finAppend hFM]
  -- step 3: the integrand in (B, A)
  set c₀ := ENNReal.ofReal (H.det ^ (-(q : ℝ) / 2) / 2)
  have hinner : ∀ α : Fin q → Fin r → ℝ, ∫⁻ β : Fin q → Fin q → ℝ, F (fun a => M *ᵥ Fin.append (β a) (α a)) =
      c₀ * (box12 q r ε).indicator (fun A => shiftInt q ε (gramH T⁻¹ A)) (fun a => T *ᵥ α a) := by
    intro α
    have hpt : ∀ β : Fin q → Fin q → ℝ, F (fun a => M *ᵥ Fin.append (β a) (α a)) =
        (box12 q r ε).indicator 1 (fun a => T *ᵥ α a) *
          {β : Fin q → Fin q → ℝ | 0 < M.det * (Matrix.of β).det}.indicator
            (fun β => (boxD q ε).indicator 1 (gramH H β + gramH T α)) β := by
      intro β
      have hmem : (fun a => M *ᵥ Fin.append (β a) (α a)) ∈ S ↔
          ((fun a => T *ᵥ α a) ∈ box12 q r ε ∧ 0 < M.det * (Matrix.of β).det ∧
            gramH H β + gramH T α ∈ boxD q ε) := by
        change (0 < (Matrix.of (Fin.append (fun a => frameM u *ᵥ Fin.append (β a) (α a)) u)).det ∧
          gramH (phiQR q r) (fun a => frameM u *ᵥ Fin.append (β a) (α a)) ∈ boxD q ε ∧
          (fun a c => (frameM u *ᵥ Fin.append (β a) (α a)) ⬝ᵥ (phiQR q r *ᵥ u c)) ∈ box12 q r ε) ↔ _
        rw [det_append_frame hT, gramH_frame hT, cross_frame hT, mul_comm (Matrix.of β).det]
        tauto
      have hF1 : F (fun a => M *ᵥ Fin.append (β a) (α a)) =
          if ((fun a => T *ᵥ α a) ∈ box12 q r ε ∧ 0 < M.det * (Matrix.of β).det ∧
            gramH H β + gramH T α ∈ boxD q ε) then 1 else 0 := by
        by_cases h : (fun a => M *ᵥ Fin.append (β a) (α a)) ∈ S
        · simp only [F]; rw [Set.indicator_of_mem h, if_pos (hmem.mp h)]; rfl
        · simp only [F]; rw [Set.indicator_of_notMem h, if_neg (fun h' => h (hmem.mpr h'))]
      rw [hF1]
      by_cases h1 : (fun a => T *ᵥ α a) ∈ box12 q r ε
      · rw [Set.indicator_of_mem h1, Pi.one_apply, one_mul]
        by_cases h2 : 0 < M.det * (Matrix.of β).det
        · rw [Set.indicator_of_mem (show β ∈ {β : Fin q → Fin q → ℝ | 0 < M.det * (Matrix.of β).det} from h2)]
          by_cases h3 : gramH H β + gramH T α ∈ boxD q ε
          · rw [if_pos ⟨h1, h2, h3⟩, Set.indicator_of_mem h3, Pi.one_apply]
          · rw [if_neg (fun h => h3 h.2.2), Set.indicator_of_notMem h3]
        · rw [if_neg (fun h => h2 h.2.1),
            Set.indicator_of_notMem (show β ∉ {β : Fin q → Fin q → ℝ | 0 < M.det * (Matrix.of β).det} from h2)]
      · rw [if_neg (fun h => h1 h.1), Set.indicator_of_notMem h1, zero_mul]
    simp_rw [hpt]
    rw [lintegral_const_mul' _ _ (by unfold Set.indicator; split_ifs <;> simp)]
    have hf : Measurable fun s : UIdx q → ℝ => (boxD q ε).indicator (1 : (UIdx q → ℝ) → ℝ≥0∞) (s + gramH T α) :=
      (measurable_one.indicator (measurableSet_boxD q ε)).comp (measurable_id.add_const _)
    rw [lintegral_gramH_det_pos hq hHpos hMd hf]
    by_cases hb : (fun a => T *ᵥ α a) ∈ box12 q r ε
    · simp only [Set.indicator_of_mem hb, Pi.one_apply, one_mul, shiftInt]
      rw [← gramH_mulVec_inv hT α]
    · simp [Set.indicator_of_notMem hb]
  simp_rw [hinner]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- step 4: substitute A = T α
  have hΨ : Measurable fun A : Fin q → Fin r → ℝ => (box12 q r ε).indicator (fun A => shiftInt q ε (gramH T⁻¹ A)) A :=
    ((measurable_shiftInt q ε).comp (continuous_gramH _).measurable).indicator (measurableSet_box12 q r ε)
  rw [lintegral_comp_mulVec_rect T hTd hΨ, ← Jint_eq]
  -- step 5: constants
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  have hsq := sq_det_frameM hT
  have hH0 : 0 < H.det := hHpos.det_pos
  have hT0 : 0 < |T.det| := abs_pos.mpr hTd
  have hM : |M.det| = H.det ^ (1 / 2 : ℝ) * |T.det| ^ (1 / 2 : ℝ) := by
    rw [← Real.mul_rpow hH0.le hT0.le, ← hsq, ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
  rw [hM, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  exact const_inner hH0 hT0 q

end Inner

end QuadFormsKB.Hanke2005.ArchReal
