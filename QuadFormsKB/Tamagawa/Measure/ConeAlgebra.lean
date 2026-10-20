import QuadFormsKB.Tamagawa.OrbitOpenness

/-!
# The parabolic subgroup fixing an isotropic vector: explicit matrices

Field-generic algebra (any field $K$ of characteristic $0$; used for $K = \mathbb R$ and $K = \mathbb C$). Let
$Q' $ be a form in $k$ variables and $c \ne 0$. The **cone form** (`coneForm c Q'`) is
$$Q = \langle c\rangle \perp \langle -c\rangle \perp Q',\qquad Q(x_0, x_1, x') = c x_0^2 - c x_1^2 + Q'(x')
  = c\,pq + Q'(x'),\quad p = x_0 + x_1,\ q = x_0 - x_1,$$
i.e. $V = H \perp V'$ with $H$ a hyperbolic plane (the **hyperbolic split**). The vector $e = e_0 + e_1$ (`eV`) is
isotropic. We define, as linear maps and matrices:

* `dL a` ($a \ne 0$): $p \mapsto ap$, $q \mapsto a^{-1}q$, identity on $V'$ (the torus $A$ of the parabolic; $d(a)e = ae$);
* `nL c Q' w` ($w \in K^k$): the **Eichler transformation**
  $n(w)(x) = x + \delta(x)\,e + (x_0 - x_1)\,\tilde w$, $\delta(x) = -\big((H'w)\cdot x' + (x_0 - x_1)Q'(w)\big)/(2c)$,
  $\tilde w = (0, 0, w)$; it fixes $e$ (the unipotent radical $N \cong V'$ of the stabilizer of $e$);
* `mM M` = $\mathrm{diag}(1, 1, M)$ (the Levi part $SO(V')$).

and prove: $Q\circ d(a) = Q$, $Q \circ n(w) = Q$ (so they are isometries, `isometry_dM`, `isometry_nM`), determinant $1$,
$n(w)n(w') = n(w + w')$, $d(a)d(b) = d(ab)$, $d(a)\,n(w)\,d(a)^{-1} = n(aw)$, $\mathrm{diag}(1,1,M)\,n(w) =
n(Mw)\,\mathrm{diag}(1,1,M)$ for $M \in O(Q')$, and the values on $e$, $e_0$.
-/

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.ConeAlgebra

open QuadFormsKB QuadFormsKB.Tamagawa QuadForm

variable {K : Type*} [Field K] [CharZero K] {k : ℕ}

/-! ### Coordinates $(x_0, x_1, x')$ -/

/-- The vector $(a, b, y) \in K^{k+2}$. -/
def v3 (a b : K) (y : Fin k → K) : Fin (k + 1 + 1) → K := Fin.cons a (Fin.cons b y)

/-- The last $k$ coordinates $x'$ of $x \in K^{k+2}$. -/
def tl (x : Fin (k + 1 + 1) → K) : Fin k → K := fun i => x i.succ.succ

@[simp] theorem v3_zero' (a b : K) (y : Fin k → K) : v3 a b y 0 = a := rfl
@[simp] theorem v3_one' (a b : K) (y : Fin k → K) : v3 a b y 1 = b := rfl
@[simp] theorem tl_v3 (a b : K) (y : Fin k → K) : tl (v3 a b y) = y := rfl

theorem v3_eta (x : Fin (k + 1 + 1) → K) : v3 (x 0) (x 1) (tl x) = x := by
  ext i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  rfl

theorem v3_add (a b a' b' : K) (y y' : Fin k → K) : v3 a b y + v3 a' b' y' = v3 (a + a') (b + b') (y + y') := by
  ext i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  rfl

theorem v3_smul (r a b : K) (y : Fin k → K) : r • v3 a b y = v3 (r * a) (r * b) (r • y) := by
  ext i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  rfl

theorem v3_inj {a b a' b' : K} {y y' : Fin k → K} : v3 a b y = v3 a' b' y' ↔ a = a' ∧ b = b' ∧ y = y' := by
  constructor
  · intro h
    refine ⟨congrFun h 0, congrFun h 1, ?_⟩
    have := congrArg tl h
    simpa using this
  · rintro ⟨rfl, rfl, rfl⟩; rfl

theorem v3_congr {a b a' b' : K} {y y' : Fin k → K} (ha : a = a') (hb : b = b') (hy : y = y') :
    v3 a b y = v3 a' b' y' := by rw [ha, hb, hy]

theorem tl_add (x y : Fin (k + 1 + 1) → K) : tl (x + y) = tl x + tl y := rfl
theorem tl_smul (r : K) (x : Fin (k + 1 + 1) → K) : tl (r • x) = r • tl x := rfl

/-- $e_0 = (1, 0, 0)$. -/
theorem e₀_eq_v3 : (e₀ : Fin (k + 1 + 1) → K) = v3 1 0 0 := by
  ext i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  rfl

/-- **The isotropic vector** $e = e_0 + e_1$. -/
def eV : Fin (k + 1 + 1) → K := v3 1 1 0

/-- $f = e_0 - e_1$ (isotropic, $B(e, f) = 2c$). -/
def fV : Fin (k + 1 + 1) → K := v3 1 (-1) 0

/-- $\tilde w = (0, 0, w)$. -/
def lift (w : Fin k → K) : Fin (k + 1 + 1) → K := v3 0 0 w

/-! ### The cone form -/

/-- **The cone form** $Q = \langle c\rangle \perp \langle -c\rangle \perp Q'$, $Q(x_0, x_1, x') = cx_0^2 - cx_1^2 + Q'(x')$. -/
abbrev coneForm (c : K) (Q' : QuadForm K k) : QuadForm K (k + 1 + 1) := splitForm c (splitForm (-c) Q')

theorem eval_coneForm_v3 (c : K) (Q' : QuadForm K k) (a b : K) (y : Fin k → K) :
    (coneForm c Q').eval (v3 a b y) = c * a ^ 2 - c * b ^ 2 + Q'.eval y := by
  rw [coneForm, v3, eval_splitForm_cons, eval_splitForm_cons]; ring

theorem eval_coneForm (c : K) (Q' : QuadForm K k) (x : Fin (k + 1 + 1) → K) :
    (coneForm c Q').eval x = c * x 0 ^ 2 - c * x 1 ^ 2 + Q'.eval (tl x) := by
  conv_lhs => rw [← v3_eta x]
  rw [eval_coneForm_v3]

theorem eval_eV (c : K) (Q' : QuadForm K k) : (coneForm c Q').eval eV = 0 := by
  rw [eV, eval_coneForm_v3]
  have : Q'.eval (0 : Fin k → K) = 0 := by
    have := eval_smul_gen Q' 0 0; simpa using this
  rw [this]; ring

/-! ### Isometries from value preservation -/

/-- **A matrix preserving the values of $Q$ preserves its Hessian**: $Q(Mx) = Q(x)$ for all $x$ implies
$M^{\mathsf T}HM = H$ (polarization). -/
theorem transpose_mul_hessian_mul_of_eval {n : ℕ} (Q : QuadForm K n) (M : Matrix (Fin n) (Fin n) K)
    (h : ∀ x, Q.eval (M *ᵥ x) = Q.eval x) : Mᵀ * Q.hessian * M = Q.hessian := by
  have key : ∀ x y : Fin n → K, x ⬝ᵥ ((Mᵀ * Q.hessian * M) *ᵥ y) = x ⬝ᵥ (Q.hessian *ᵥ y) := by
    intro x y
    have h1 := eval_polar Q (M *ᵥ x) (M *ᵥ y)
    rw [← mulVec_add, h, h, h] at h1
    rw [← eval_polar Q x y, h1, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  ext i j
  have := key (Pi.single i 1) (Pi.single j 1)
  simpa [mulVec, dotProduct, Pi.single_apply] using this

/-- **Conversely**, $M^{\mathsf T}HM = H$ implies $Q(Mx) = Q(x)$ (characteristic $0$). -/
theorem eval_mulVec_of_isometry {n : ℕ} (Q : QuadForm K n) {M : Matrix (Fin n) (Fin n) K}
    (h : Mᵀ * Q.hessian * M = Q.hessian) (x : Fin n → K) : Q.eval (M *ᵥ x) = Q.eval x := by
  have h1 := dotProduct_hessian_self Q (M *ᵥ x)
  have h2 := dotProduct_hessian_self Q x
  have e : (M *ᵥ x) ⬝ᵥ (Q.hessian *ᵥ (M *ᵥ x)) = x ⬝ᵥ ((Mᵀ * Q.hessian * M) *ᵥ x) := by
    rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x Mᵀ, vecMul_transpose]
  rw [e, h] at h1
  have h3 : (2 : K) * Q.eval (M *ᵥ x) = 2 * Q.eval x := by rw [← h1, ← h2]
  exact mul_left_cancel₀ two_ne_zero h3

/-- **An isometry of a nondegenerate form has $\det^2 = 1$.** -/
theorem det_sq_of_isometry {n : ℕ} {H M : Matrix (Fin n) (Fin n) K} (hH : H.det ≠ 0) (h : Mᵀ * H * M = H) :
    M.det ^ 2 = 1 := by
  have := congrArg Matrix.det h
  rw [det_mul, det_mul, det_transpose] at this
  have h2 : (M.det ^ 2 - 1) * H.det = 0 := by linear_combination this
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hH)

/-- Matrices with the same action on vectors are equal. -/
theorem mat_ext {n : ℕ} {A B : Matrix (Fin n) (Fin n) K} (h : ∀ x, A *ᵥ x = B *ᵥ x) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun x => by simp only [Matrix.toLin'_apply, h])

/-! ### The torus $d(a)$ -/

/-- Coordinate functionals. -/
def p0L : (Fin (k + 1 + 1) → K) →ₗ[K] K := LinearMap.proj 0
def p1L : (Fin (k + 1 + 1) → K) →ₗ[K] K := LinearMap.proj 1

/-- **The torus element** $d(a)$: $x \mapsto x + \tfrac{a-1}2(x_0 + x_1)\,e + \tfrac{a^{-1}-1}2(x_0 - x_1)\,f$, i.e.
$p \mapsto ap$, $q \mapsto a^{-1}q$. -/
def dL (a : K) : (Fin (k + 1 + 1) → K) →ₗ[K] (Fin (k + 1 + 1) → K) :=
  LinearMap.id + LinearMap.smulRight (((a - 1) / 2) • (p0L (K := K) (k := k) + p1L)) eV +
    LinearMap.smulRight (((a⁻¹ - 1) / 2) • (p0L (K := K) (k := k) - p1L)) fV

theorem dL_v3 (a x0 x1 : K) (y : Fin k → K) :
    dL a (v3 x0 x1 y) = v3 (x0 + (a - 1) / 2 * (x0 + x1) + (a⁻¹ - 1) / 2 * (x0 - x1))
      (x1 + (a - 1) / 2 * (x0 + x1) - (a⁻¹ - 1) / 2 * (x0 - x1)) y := by
  simp only [dL, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, p0L, p1L, LinearMap.proj_apply, v3_zero', v3_one', eV, fV, v3_smul, v3_add, smul_eq_mul]
  refine v3_congr (by ring) (by ring) (by simp)

/-- The matrix of $d(a)$. -/
def dM (a : K) : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) K := LinearMap.toMatrix' (dL a)

theorem dM_mulVec (a : K) (x : Fin (k + 1 + 1) → K) : dM a *ᵥ x = dL a x := LinearMap.toMatrix'_mulVec _ _

theorem dM_mulVec_v3 (a x0 x1 : K) (y : Fin k → K) :
    dM a *ᵥ v3 x0 x1 y = v3 (x0 + (a - 1) / 2 * (x0 + x1) + (a⁻¹ - 1) / 2 * (x0 - x1))
      (x1 + (a - 1) / 2 * (x0 + x1) - (a⁻¹ - 1) / 2 * (x0 - x1)) y := by
  rw [dM_mulVec, dL_v3]

theorem dM_mulVec_eV {a : K} (ha : a ≠ 0) : dM a *ᵥ (eV : Fin (k + 1 + 1) → K) = a • eV := by
  rw [eV, dM_mulVec_v3, v3_smul]
  refine v3_congr (by ring) (by ring) (by simp)

theorem eval_dM (c : K) (Q' : QuadForm K k) {a : K} (ha : a ≠ 0) (x : Fin (k + 1 + 1) → K) :
    (coneForm c Q').eval (dM a *ᵥ x) = (coneForm c Q').eval x := by
  rw [← v3_eta x, dM_mulVec_v3, eval_coneForm_v3, eval_coneForm_v3]
  field_simp
  ring

theorem dM_mul (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) : dM (k := k) a * dM b = dM (a * b) := by
  refine mat_ext fun x => ?_
  rw [← mulVec_mulVec, ← v3_eta x, dM_mulVec_v3, dM_mulVec_v3, dM_mulVec_v3]
  refine v3_congr ?_ ?_ rfl <;> field_simp <;> ring

theorem dM_one : dM (k := k) (1 : K) = 1 := by
  refine mat_ext fun x => ?_
  rw [one_mulVec, ← v3_eta x, dM_mulVec_v3]
  refine v3_congr ?_ ?_ rfl <;> simp

theorem dM_mul_inv {a : K} (ha : a ≠ 0) : dM (k := k) a * dM a⁻¹ = 1 := by
  rw [dM_mul _ _ ha (inv_ne_zero ha), mul_inv_cancel₀ ha, dM_one]

theorem dM_inv_mul {a : K} (ha : a ≠ 0) : dM (k := k) a⁻¹ * dM a = 1 := by
  rw [dM_mul _ _ (inv_ne_zero ha) ha, inv_mul_cancel₀ ha, dM_one]

/-! ### The unipotent radical $n(w)$ -/

/-- The functional $\delta(x) = -\big((H'w)\cdot x' + (x_0 - x_1)Q'(w)\big)/(2c)$. -/
def delL (c : K) (Q' : QuadForm K k) (w : Fin k → K) : (Fin (k + 1 + 1) → K) →ₗ[K] K where
  toFun x := -(((Q'.hessian *ᵥ w) ⬝ᵥ tl x) + (x 0 - x 1) * Q'.eval w) / (2 * c)
  map_add' x y := by
    simp only [tl_add, dotProduct_add, Pi.add_apply]; ring
  map_smul' r x := by
    simp only [tl_smul, dotProduct_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- **The Eichler transformation** $n(w)(x) = x + \delta(x)\,e + (x_0 - x_1)\,\tilde w$. -/
def nL (c : K) (Q' : QuadForm K k) (w : Fin k → K) : (Fin (k + 1 + 1) → K) →ₗ[K] (Fin (k + 1 + 1) → K) :=
  LinearMap.id + (delL c Q' w).smulRight eV + LinearMap.smulRight (p0L (K := K) (k := k) - p1L) (lift w)

theorem nL_v3 (c : K) (Q' : QuadForm K k) (w : Fin k → K) (a b : K) (y : Fin k → K) :
    nL c Q' w (v3 a b y) = v3 (a - ((Q'.hessian *ᵥ w) ⬝ᵥ y + (a - b) * Q'.eval w) / (2 * c))
      (b - ((Q'.hessian *ᵥ w) ⬝ᵥ y + (a - b) * Q'.eval w) / (2 * c)) (y + (a - b) • w) := by
  simp only [nL, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply, LinearMap.sub_apply,
    p0L, p1L, LinearMap.proj_apply, v3_zero', v3_one', eV, lift, v3_smul, v3_add, delL, LinearMap.coe_mk,
    AddHom.coe_mk, tl_v3, smul_eq_mul]
  refine v3_congr (by ring) (by ring) (by simp)

/-- The matrix of $n(w)$. -/
def nM (c : K) (Q' : QuadForm K k) (w : Fin k → K) : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) K :=
  LinearMap.toMatrix' (nL c Q' w)

variable (c : K) (Q' : QuadForm K k)

theorem nM_mulVec_v3 (w : Fin k → K) (a b : K) (y : Fin k → K) :
    nM c Q' w *ᵥ v3 a b y = v3 (a - ((Q'.hessian *ᵥ w) ⬝ᵥ y + (a - b) * Q'.eval w) / (2 * c))
      (b - ((Q'.hessian *ᵥ w) ⬝ᵥ y + (a - b) * Q'.eval w) / (2 * c)) (y + (a - b) • w) := by
  rw [nM, LinearMap.toMatrix'_mulVec, nL_v3]

theorem eval_zero' : Q'.eval (0 : Fin k → K) = 0 := by
  have := eval_smul_gen Q' 0 0; simpa using this

theorem nM_mulVec_eV (w : Fin k → K) : nM c Q' w *ᵥ (eV : Fin (k + 1 + 1) → K) = eV := by
  rw [eV, nM_mulVec_v3]
  refine v3_congr (by simp) (by simp) (by simp)

theorem nM_mulVec_e₀ (hc : c ≠ 0) (w : Fin k → K) :
    nM c Q' w *ᵥ (e₀ : Fin (k + 1 + 1) → K) = v3 (1 - Q'.eval w / (2 * c)) (-(Q'.eval w / (2 * c))) w := by
  rw [e₀_eq_v3, nM_mulVec_v3]
  refine v3_congr (by simp) (by simp) (by simp)

theorem eval_nM (hc : c ≠ 0) (w : Fin k → K) (x : Fin (k + 1 + 1) → K) :
    (coneForm c Q').eval (nM c Q' w *ᵥ x) = (coneForm c Q').eval x := by
  rw [← v3_eta x, nM_mulVec_v3, eval_coneForm_v3, eval_coneForm_v3]
  set a := x 0
  set b := x 1
  set y := tl x
  have h1 : Q'.eval (y + (a - b) • w) = Q'.eval y + (a - b) * ((Q'.hessian *ᵥ y) ⬝ᵥ w) + (a - b) ^ 2 * Q'.eval w :=
    eval_add_smul_gen Q' y w (a - b)
  have h2 : (Q'.hessian *ᵥ y) ⬝ᵥ w = (Q'.hessian *ᵥ w) ⬝ᵥ y := hess_dot_comm Q' y w
  rw [h1, h2]
  field_simp
  ring

theorem nM_mul (hc : c ≠ 0) (w w' : Fin k → K) : nM c Q' w * nM c Q' w' = nM c Q' (w + w') := by
  refine mat_ext fun x => ?_
  rw [← mulVec_mulVec, ← v3_eta x, nM_mulVec_v3, nM_mulVec_v3, nM_mulVec_v3]
  set a := x 0
  set b := x 1
  set y := tl x
  have hq : Q'.eval (w + w') = Q'.eval w + (Q'.hessian *ᵥ w) ⬝ᵥ w' + Q'.eval w' := by
    have := eval_add_smul_gen Q' w w' 1
    simpa using this
  have hs : (Q'.hessian *ᵥ w) ⬝ᵥ w' = (Q'.hessian *ᵥ w') ⬝ᵥ w := hess_dot_comm Q' w w'
  refine v3_congr ?_ ?_ ?_
  · simp only [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_smul, smul_eq_mul, hq]
    rw [hs]; field_simp; ring
  · simp only [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_smul, smul_eq_mul, hq]
    rw [hs]; field_simp; ring
  · have : a - ((Q'.hessian *ᵥ w') ⬝ᵥ y + (a - b) * Q'.eval w') / (2 * c) -
        (b - ((Q'.hessian *ᵥ w') ⬝ᵥ y + (a - b) * Q'.eval w') / (2 * c)) = a - b := by ring
    rw [this, smul_add, add_assoc, add_comm ((a - b) • w') ((a - b) • w)]

theorem nM_zero : nM c Q' (0 : Fin k → K) = 1 := by
  refine mat_ext fun x => ?_
  rw [one_mulVec, ← v3_eta x, nM_mulVec_v3]
  refine v3_congr (by simp [eval_zero']) (by simp [eval_zero']) (by simp)

theorem nM_mul_neg (hc : c ≠ 0) (w : Fin k → K) : nM c Q' w * nM c Q' (-w) = 1 := by
  rw [nM_mul c Q' hc, add_neg_cancel, nM_zero]

theorem nM_neg_mul (hc : c ≠ 0) (w : Fin k → K) : nM c Q' (-w) * nM c Q' w = 1 := by
  rw [nM_mul c Q' hc, neg_add_cancel, nM_zero]

/-- **Conjugation by the torus**: $d(a)\,n(w) = n(aw)\,d(a)$. -/
theorem dM_mul_nM (hc : c ≠ 0) {a : K} (ha : a ≠ 0) (w : Fin k → K) :
    dM a * nM c Q' w = nM c Q' (a • w) * dM a := by
  refine mat_ext fun x => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, ← v3_eta x, nM_mulVec_v3, dM_mulVec_v3, dM_mulVec_v3, nM_mulVec_v3]
  have hq : Q'.eval (a • w) = a ^ 2 * Q'.eval w := eval_smul_gen Q' a w
  refine v3_congr ?_ ?_ ?_
  · simp only [mulVec_smul, smul_dotProduct, smul_eq_mul, hq]; field_simp; ring
  · simp only [mulVec_smul, smul_dotProduct, smul_eq_mul, hq]; field_simp; ring
  · rw [smul_smul]; congr 2; field_simp; ring

/-! ### The Levi factor $\mathrm{diag}(1, 1, M)$ -/

/-- $\mathrm{diag}(1, 1, M)$. -/
def mM (M : Matrix (Fin k) (Fin k) K) : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) K := cornerMat 1 (cornerMat 1 M)

theorem mM_mulVec_v3 (M : Matrix (Fin k) (Fin k) K) (a b : K) (y : Fin k → K) :
    mM M *ᵥ v3 a b y = v3 a b (M *ᵥ y) := by
  rw [mM, v3, cornerMat_mulVec, cornerMat_mulVec, one_mul, one_mul]; rfl

theorem mM_mul (M M' : Matrix (Fin k) (Fin k) K) : mM M * mM M' = mM (M * M') := by
  simp only [mM, cornerMat_mul, one_mul]

theorem mM_one : mM (1 : Matrix (Fin k) (Fin k) K) = 1 := by rw [mM, cornerMat_one, cornerMat_one]

theorem mM_mulVec_eV (M : Matrix (Fin k) (Fin k) K) : mM M *ᵥ (eV : Fin (k + 1 + 1) → K) = eV := by
  rw [eV, mM_mulVec_v3, mulVec_zero]

theorem mM_mul_dM (M : Matrix (Fin k) (Fin k) K) (a : K) : mM M * dM a = dM a * mM M := by
  refine mat_ext fun x => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, ← v3_eta x, dM_mulVec_v3, mM_mulVec_v3, mM_mulVec_v3, dM_mulVec_v3]

/-- **The Levi factor normalizes $N$**: $\mathrm{diag}(1,1,M)\,n(w) = n(Mw)\,\mathrm{diag}(1,1,M)$ for
$M^{\mathsf T}H'M = H'$. -/
theorem mM_mul_nM {M : Matrix (Fin k) (Fin k) K} (hM : Mᵀ * Q'.hessian * M = Q'.hessian) (w : Fin k → K) :
    mM M * nM c Q' w = nM c Q' (M *ᵥ w) * mM M := by
  refine mat_ext fun x => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, ← v3_eta x, nM_mulVec_v3, mM_mulVec_v3, mM_mulVec_v3, nM_mulVec_v3]
  have hq : Q'.eval (M *ᵥ w) = Q'.eval w := eval_mulVec_of_isometry Q' hM w
  have hb : (Q'.hessian *ᵥ (M *ᵥ w)) ⬝ᵥ (M *ᵥ tl x) = (Q'.hessian *ᵥ w) ⬝ᵥ tl x := by
    rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, mulVec_mulVec, hM]
  rw [hq, hb, mulVec_add, mulVec_smul]

/-! ### Isometry and determinant -/

theorem isometry_dM {a : K} (ha : a ≠ 0) : (dM a)ᵀ * (coneForm c Q').hessian * dM a = (coneForm c Q').hessian :=
  transpose_mul_hessian_mul_of_eval _ _ (eval_dM c Q' ha)

theorem isometry_nM (hc : c ≠ 0) (w : Fin k → K) :
    (nM c Q' w)ᵀ * (coneForm c Q').hessian * nM c Q' w = (coneForm c Q').hessian :=
  transpose_mul_hessian_mul_of_eval _ _ (eval_nM c Q' hc w)

theorem isometry_mM {M : Matrix (Fin k) (Fin k) K} (hM : Mᵀ * Q'.hessian * M = Q'.hessian) :
    (mM M)ᵀ * (coneForm c Q').hessian * mM M = (coneForm c Q').hessian := by
  refine transpose_mul_hessian_mul_of_eval _ _ fun x => ?_
  rw [← v3_eta x, mM_mulVec_v3, eval_coneForm_v3, eval_coneForm_v3, eval_mulVec_of_isometry Q' hM]

theorem det_mM (M : Matrix (Fin k) (Fin k) K) : (mM M).det = M.det := by
  rw [mM, det_cornerMat, det_cornerMat, one_mul, one_mul]

theorem det_nM (hc : c ≠ 0) (hQ : (coneForm c Q').hessian.det ≠ 0) (w : Fin k → K) : (nM c Q' w).det = 1 := by
  have h2 : nM c Q' w = nM c Q' ((1 / 2 : K) • w) * nM c Q' ((1 / 2 : K) • w) := by
    rw [nM_mul c Q' hc, ← add_smul]; norm_num
  rw [h2, det_mul, ← sq]
  exact det_sq_of_isometry hQ (isometry_nM c Q' hc _)

theorem dM_neg_one : dM (k := k) (-1 : K) = diagonal (v3 (-1) (-1) 1) := by
  refine mat_ext fun x => ?_
  rw [← v3_eta x, dM_mulVec_v3]
  ext i
  rw [mulVec_diagonal]
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
  · simp [v3]; ring
  · simp [v3]; ring
  · simp [v3]

theorem det_dM_neg_one : (dM (k := k) (-1 : K)).det = 1 := by
  rw [dM_neg_one, det_diagonal, v3, Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp

/-- $\det d(a) = 1$ whenever $a$ or $-a$ is a square (always over $\mathbb R$ and $\mathbb C$). -/
theorem det_dM (hQ : (coneForm c Q').hessian.det ≠ 0) {a : K} (ha : a ≠ 0) (hsq : ∃ b, b ^ 2 = a ∨ b ^ 2 = -a) :
    (dM (k := k) a).det = 1 := by
  obtain ⟨b, hb | hb⟩ := hsq
  · have hb0 : b ≠ 0 := by rintro rfl; apply ha; linear_combination -hb
    rw [← hb, sq, ← dM_mul _ _ hb0 hb0, det_mul, ← sq]
    exact det_sq_of_isometry hQ (isometry_dM c Q' hb0)
  · have hb0 : b ≠ 0 := by rintro rfl; apply ha; linear_combination hb
    have : a = -1 * (b * b) := by rw [← sq, hb]; ring
    rw [this, ← dM_mul _ _ (by norm_num) (mul_ne_zero hb0 hb0), det_mul, det_dM_neg_one, one_mul,
      ← dM_mul _ _ hb0 hb0, det_mul, ← sq]
    exact det_sq_of_isometry hQ (isometry_dM c Q' hb0)


/-! ### The stabilizer of $e$ -/

theorem dotProduct_v3 (a b a' b' : K) (y y' : Fin k → K) :
    v3 a b y ⬝ᵥ v3 a' b' y' = a * a' + b * b' + y ⬝ᵥ y' := by
  simp only [dotProduct, v3, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]; ring

theorem hessian_coneForm_mulVec_v3 (a b : K) (y : Fin k → K) :
    (coneForm c Q').hessian *ᵥ v3 a b y = v3 (2 * c * a) (2 * -c * b) (Q'.hessian *ᵥ y) := by
  rw [coneForm, v3, hessian_splitForm, cornerMat_mulVec, hessian_splitForm, cornerMat_mulVec]; rfl

/-- An isometry preserves the polar form $x^{\mathsf T}Hy$. -/
theorem hess_dot_of_isometry {n : ℕ} {H M : Matrix (Fin n) (Fin n) K} (h : Mᵀ * H * M = H) (u v : Fin n → K) :
    (H *ᵥ (M *ᵥ u)) ⬝ᵥ (M *ᵥ v) = (H *ᵥ u) ⬝ᵥ v := by
  rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, mulVec_mulVec, h]

/-- **Shape of an isometry fixing $e_0$** (any form $\langle a\rangle \perp Q_1$, $a \ne 0$): $M = \mathrm{diag}(1, M_1)$ with
$M_1$ an isometry of $Q_1$. -/
theorem shape_of_fix_e₀ {n : ℕ} {a : K} (ha : a ≠ 0) (Q₁ : QuadForm K n) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hM : Mᵀ * (splitForm a Q₁).hessian * M = (splitForm a Q₁).hessian) (h0 : M *ᵥ (e₀ : Fin (n + 1) → K) = e₀) :
    M = cornerMat 1 (M.submatrix Fin.succ Fin.succ) ∧
      (M.submatrix Fin.succ Fin.succ)ᵀ * Q₁.hessian * M.submatrix Fin.succ Fin.succ = Q₁.hessian := by
  have hcol : ∀ i, M i 0 = (e₀ : Fin (n + 1) → K) i := fun i => by
    have := congrFun h0 i
    rw [← this]; simp [mulVec, dotProduct, Fin.sum_univ_succ]
  have hrow : ∀ j : Fin n, M 0 j.succ = 0 := by
    intro j
    have := hess_dot_of_isometry hM (e₀ : Fin (n + 1) → K) (Pi.single j.succ 1)
    rw [h0, hessian_splitForm, e₀, cornerMat_mulVec] at this
    simp only [mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Pi.single_apply,
      Fin.succ_ne_zero, ite_false, mul_zero, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero,
      mul_one] at this
    simp only [Fin.succ_inj, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      zero_add] at this
    have h2 : (2 : K) * a ≠ 0 := mul_ne_zero two_ne_zero ha
    have r := (mul_eq_zero.mp this).resolve_left h2
    simpa [(Fin.succ_ne_zero j).symm] using r
  have hshape : M = cornerMat 1 (M.submatrix Fin.succ Fin.succ) := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hcol 0
    · simpa using hrow j
    · simpa using hcol i.succ
    · rfl
  refine ⟨hshape, ?_⟩
  have := hM
  rw [hshape, hessian_splitForm, cornerMat_transpose, cornerMat_mul, cornerMat_mul] at this
  exact cornerMat_injective_right this

/-- **The stabilizer of the isotropic vector $e$** in $O(Q)$: every isometry $g$ of the cone form with $ge = e$ is
$g = n(w)\,\mathrm{diag}(1, 1, M)$ with $w = (ge_0)'$ and $M$ an isometry of $Q'$ ($P = N \rtimes O(V')$). -/
theorem eq_nM_mul_mM_of_fix (hc : c ≠ 0) (g : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) K)
    (hg : gᵀ * (coneForm c Q').hessian * g = (coneForm c Q').hessian) (he : g *ᵥ (eV : Fin (k + 1 + 1) → K) = eV) :
    ∃ M : Matrix (Fin k) (Fin k) K, Mᵀ * Q'.hessian * M = Q'.hessian ∧ g = nM c Q' (tl (g *ᵥ e₀)) * mM M := by
  set x := g *ᵥ (e₀ : Fin (k + 1 + 1) → K)
  have hB : (coneForm c Q').hessian *ᵥ x ⬝ᵥ eV = (coneForm c Q').hessian *ᵥ e₀ ⬝ᵥ eV := by
    have := hess_dot_of_isometry hg (e₀ : Fin (k + 1 + 1) → K) eV
    rwa [he] at this
  have hQ : (coneForm c Q').eval x = c := by
    rw [eval_mulVec_of_isometry _ hg, e₀_eq_v3, eval_coneForm_v3, eval_zero']; ring
  rw [← v3_eta x, hessian_coneForm_mulVec_v3, eV, dotProduct_v3, e₀_eq_v3, hessian_coneForm_mulVec_v3,
    dotProduct_v3] at hB
  simp only [dotProduct_zero, mulVec_zero, add_zero, mul_one, mul_zero] at hB
  have h1 : x 0 - x 1 = 1 := by
    have : 2 * c * (x 0 - x 1 - 1) = 0 := by linear_combination hB
    have := (mul_eq_zero.mp this).resolve_left (mul_ne_zero two_ne_zero hc)
    linear_combination this
  rw [eval_coneForm] at hQ
  have hx : nM c Q' (tl x) *ᵥ (e₀ : Fin (k + 1 + 1) → K) = x := by
    rw [nM_mulVec_e₀ c Q' hc, ← v3_eta x]
    simp only [tl_v3, v3_zero', v3_one']
    have hQ' : Q'.eval (tl x) = c - c * (x 0 + x 1) := by linear_combination hQ - c * (x 0 + x 1) * h1
    have hd : Q'.eval (tl x) / (2 * c) = (1 - (x 0 + x 1)) / 2 := by
      rw [hQ', div_eq_div_iff (mul_ne_zero two_ne_zero hc) two_ne_zero]; ring
    rw [hd]
    refine v3_congr ?_ ?_ rfl
    · linear_combination (-1 / 2 : K) * h1
    · linear_combination (1 / 2 : K) * h1
  set g' := nM c Q' (-tl x) * g
  have hg' : g'ᵀ * (coneForm c Q').hessian * g' = (coneForm c Q').hessian := by
    simp only [g', transpose_mul]
    rw [show gᵀ * (nM c Q' (-tl x))ᵀ * (coneForm c Q').hessian * (nM c Q' (-tl x) * g) =
      gᵀ * ((nM c Q' (-tl x))ᵀ * (coneForm c Q').hessian * nM c Q' (-tl x)) * g by
        simp only [Matrix.mul_assoc], isometry_nM c Q' hc, hg]
  have he₀ : g' *ᵥ (e₀ : Fin (k + 1 + 1) → K) = e₀ := by
    have key : nM c Q' (-tl x) *ᵥ (nM c Q' (tl x) *ᵥ (e₀ : Fin (k + 1 + 1) → K)) = e₀ := by
      rw [mulVec_mulVec, nM_mul c Q' hc, neg_add_cancel, nM_zero, one_mulVec]
    rw [hx] at key
    rw [← mulVec_mulVec]; exact key
  have heV : g' *ᵥ (eV : Fin (k + 1 + 1) → K) = eV := by
    rw [← mulVec_mulVec, he, nM_mulVec_eV]
  obtain ⟨hs1, hi1⟩ := shape_of_fix_e₀ hc (splitForm (-c) Q') g' hg' he₀
  set g₁ := g'.submatrix Fin.succ Fin.succ
  have he₁ : g₁ *ᵥ (e₀ : Fin (k + 1) → K) = e₀ := by
    have := heV
    rw [hs1, eV, v3, cornerMat_mulVec, one_mul] at this
    have := congrArg (fun v : Fin (k + 1 + 1) → K => (fun i : Fin (k + 1) => v i.succ)) this
    simpa [e₀] using this
  obtain ⟨hs2, hi2⟩ := shape_of_fix_e₀ (neg_ne_zero.mpr hc) Q' g₁ hi1 he₁
  refine ⟨g₁.submatrix Fin.succ Fin.succ, hi2, ?_⟩
  have : g = nM c Q' (tl x) * g' := by
    simp only [g', ← Matrix.mul_assoc, nM_mul c Q' hc, add_neg_cancel, nM_zero, Matrix.one_mul]
  rw [this, hs1, hs2]
  rfl

end QuadFormsKB.Tamagawa.Measure.ConeAlgebra
