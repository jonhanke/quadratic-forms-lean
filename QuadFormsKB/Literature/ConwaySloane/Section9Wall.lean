/-
# Wall's formula for the spinor norm

**Layer.** $V = K^n$ with the form $Q$ = `Q : QuadForm F n` over a field $K \supseteq F$ of characteristic $0$ (as in
`Lattices/SpinorNorm.lean`); $H$ = `Q.hessian.map (algebraMap F K)`, so the bilinear form is
$B(x, y) = x^{\mathsf T} H y$ with $B(x, x) = 2Q(x)$ (`qbil`), and $\sigma \in O(V)(K)$ is a matrix $S$ with
$S^{\mathsf T} H S = H$.

For $\sigma \in O(V)$ put $T = 1 - S$ and $V_\sigma = T V$. The **Wall form** of $\sigma$ is the bilinear form
$\chi_\sigma(x, y) = B(x, z)$ on $V_\sigma$, where $y = Tz$; it is well defined because $V_\sigma$ is $B$-orthogonal
to $\ker T$. In coordinates: a **Wall frame** of $S$ (`IsWallFrame`) is a pair of $n \times m$ matrices $P, R$ with
$TR = P$, the columns of $P$ linearly independent and spanning $V_\sigma$; the Gram matrix of $\chi_\sigma$ in the basis
$P$ is $P^{\mathsf T} H R$.

**Proves**
* `wall_formula` (**Wall's formula**, G. E. Wall 1959, H. Zassenhaus 1962): for nondegenerate $Q$, every Wall frame
  $(P, R)$ of $\sigma$ (size $m$) satisfies $\theta(\sigma) = \det(P^{\mathsf T} H R)\,K^{\times 2}$ and
  $\det \sigma = (-1)^m$;
* `exists_wallFrame`: every $\sigma \in O(V)$ has a Wall frame.

*Proof.* Frames are unique up to $P \mapsto PU$, $R \mapsto RU + Y$ with $TY = 0$, which changes the determinant by
$\det(U)^2$ (`wallFrame_size_eq`, `sqClassOf_wallDet_eq`). For a symmetry $\tau_v$ and $\rho = \tau_v\sigma$: if some
$f \in \ker T$ has $B(v, f) \ne 0$, then $(P \mid v)$ with the explicit $R'$ of `wallFrame_extend` is a Wall frame of
$\rho$ whose Gram matrix is block triangular with corner $Q(v)$, so the determinant gets multiplied by $Q(v)$
(`wallFrame_extend`); otherwise $v = Tu$ ($V_\sigma = (\ker T)^\perp$, `mem_range_of_orth_ker`), and then $u$ is fixed
by $\rho$ with $B(v, u) = Q(v) \ne 0$, so the first case applies to $\rho$ and $\tau_v\rho = \sigma$. Induction over a
factorization of $\sigma$ into symmetries (Cartan–Dieudonné, `exists_symmProd_eq`) gives the formula, since both sides
are multiplied by $Q(v)$ at each step.

This file is the linear algebra used for the $2$-adic upper bound of `Section9EvenUnimodular.lean` (Conway–Sloane,
Ch. 15, §9.5–9.6).
-/
import QuadFormsKB.Lattices.SpinorNorm

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane.Wall

open Lattices

variable {F : Type*} [Field F] [NumberField F] {n : ℕ}
variable (Q : QuadForm F n) (K : Type*) [Field K] [Algebra F K] [CharZero K]

local notation "Hk" => Q.hessian.map (algebraMap F K)

/-- The matrix of an element of $O(V)(K)$. -/
abbrev mat (σ : orthGroup Q K) : Matrix (Fin n) (Fin n) K := ((σ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

/-- A **Wall frame** of $S$: $n \times m$ matrices $P, R$ with $(1 - S)R = P$, the columns of $P$ linearly
independent, and every vector $(1 - S)z$ a combination of the columns of $P$. -/
def IsWallFrame (S : Matrix (Fin n) (Fin n) K) {m : ℕ} (P R : Matrix (Fin n) (Fin m) K) : Prop :=
  (1 - S) * R = P ∧ (∀ c : Fin m → K, P *ᵥ c = 0 → c = 0) ∧ ∀ z : Fin n → K, ∃ c, (1 - S) *ᵥ z = P *ᵥ c

/-- The Gram matrix $P^{\mathsf T} H R$ of the Wall form in a frame. -/
def wallGram {m : ℕ} (P R : Matrix (Fin n) (Fin m) K) : Matrix (Fin m) (Fin m) K := Pᵀ * Hk * R

variable {Q K}

theorem mat_orth (σ : orthGroup Q K) : (mat Q K σ)ᵀ * Hk * mat Q K σ = Hk := (mem_orthGroup Q).mp σ.2

/-- $V_\sigma \perp \ker T$: $B(Tz, y) = 0$ when $Sy = y$. -/
theorem orth_ker (σ : orthGroup Q K) (z y : Fin n → K) (hy : mat Q K σ *ᵥ y = y) :
    ((1 - mat Q K σ) *ᵥ z) ⬝ᵥ (Hk *ᵥ y) = 0 := by
  have e : (mat Q K σ *ᵥ z) ⬝ᵥ (Hk *ᵥ y) = z ⬝ᵥ (Hk *ᵥ y) := by
    conv_lhs => rw [← hy]
    exact bilin_orth Q K σ z y
  rw [sub_mulVec, one_mulVec, sub_dotProduct, e, sub_self]

/-- $B(Tu, u) = Q(Tu)$ (the Wall form is $Q$ on the diagonal). -/
theorem wall_diag (σ : orthGroup Q K) (u : Fin n → K) :
    ((1 - mat Q K σ) *ᵥ u) ⬝ᵥ (Hk *ᵥ u) = Q.evalIn K ((1 - mat Q K σ) *ᵥ u) := by
  have h := mat_orth σ
  set S := mat Q K σ
  have hb : (S *ᵥ u) ⬝ᵥ (Hk *ᵥ (S *ᵥ u)) = u ⬝ᵥ (Hk *ᵥ u) := bilin_orth Q K σ u u
  have hsym : (S *ᵥ u) ⬝ᵥ (Hk *ᵥ u) = u ⬝ᵥ (Hk *ᵥ (S *ᵥ u)) := by
    have := qbil_comm Q K (S *ᵥ u) u
    simpa [qbil] using this
  have h2 : (2 : K) * Q.evalIn K ((1 - S) *ᵥ u) = ((1 - S) *ᵥ u) ⬝ᵥ (Hk *ᵥ ((1 - S) *ᵥ u)) := by
    rw [two_mul_evalIn]
  have h2' : (2 : K) ≠ 0 := two_ne_zero
  apply mul_left_cancel₀ h2'
  rw [h2]
  simp only [sub_mulVec, one_mulVec, mulVec_sub, sub_dotProduct, dotProduct_sub]
  rw [hb, hsym]
  ring

/-! ### Matrix helpers -/

theorem mulVec_eq_sum_cols {m : ℕ} (P : Matrix (Fin n) (Fin m) K) (c : Fin m → K) :
    P *ᵥ c = ∑ j, c j • (fun i => P i j) := by
  ext i
  simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem mul_apply_col {m k : ℕ} (M : Matrix (Fin n) (Fin k) K) (R : Matrix (Fin k) (Fin m) K) (i : Fin n)
    (j : Fin m) : (M * R) i j = (M *ᵥ fun k => R k j) i := by
  simp [Matrix.mul_apply, mulVec, dotProduct]

theorem gram_apply {m m' : ℕ} (P : Matrix (Fin n) (Fin m) K) (R : Matrix (Fin n) (Fin m') K) (i : Fin m)
    (j : Fin m') : (Pᵀ * Hk * R) i j = (fun k => P k i) ⬝ᵥ (Hk *ᵥ fun k => R k j) := by
  simp only [Matrix.mul_apply, transpose_apply, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem sqClassOf_sq_mul' {u d : K} (hu : u ≠ 0) : sqClassOf (u ^ 2 * d) = sqClassOf d := by
  by_cases hd : d = 0
  · simp [hd]
  rw [sqClassOf_mul (pow_ne_zero 2 hu) hd, (sqClassOf_eq_one_iff (pow_ne_zero 2 hu)).mpr ⟨u, sq u⟩, one_mul]

/-! ### Frames: size and uniqueness -/

/-- The size of a Wall frame is the rank of $1 - S$. -/
theorem wallFrame_size {S : Matrix (Fin n) (Fin n) K} {m : ℕ} {P R : Matrix (Fin n) (Fin m) K}
    (hf : IsWallFrame K S P R) : m = Module.finrank K (LinearMap.range (Matrix.toLin' (1 - S))) := by
  obtain ⟨hTR, hinj, hspan⟩ := hf
  have hr : LinearMap.range (Matrix.toLin' P) = LinearMap.range (Matrix.toLin' (1 - S)) := by
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      refine ⟨R *ᵥ c, ?_⟩
      simp only [Matrix.toLin'_apply, mulVec_mulVec, hTR]
    · rintro _ ⟨z, rfl⟩
      obtain ⟨c, hc⟩ := hspan z
      exact ⟨c, by simp only [Matrix.toLin'_apply]; exact hc.symm⟩
  have hi : Function.Injective (Matrix.toLin' P) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    exact hinj c (by simpa using hc)
  rw [← hr, LinearMap.finrank_range_of_inj hi, Module.finrank_fin_fun]

theorem wallFrame_size_eq {S : Matrix (Fin n) (Fin n) K} {m m' : ℕ} {P R : Matrix (Fin n) (Fin m) K}
    {P' R' : Matrix (Fin n) (Fin m') K} (hf : IsWallFrame K S P R) (hf' : IsWallFrame K S P' R') : m = m' :=
  (wallFrame_size hf).trans (wallFrame_size hf').symm

/-- Two Wall frames of the same $\sigma$ and size: the determinants differ by a nonzero square factor. -/
theorem wallDet_eq (σ : orthGroup Q K) {m : ℕ} {P R P' R' : Matrix (Fin n) (Fin m) K}
    (hf : IsWallFrame K (mat Q K σ) P R) (hf' : IsWallFrame K (mat Q K σ) P' R') :
    ∃ u : K, u ≠ 0 ∧ (wallGram Q K P' R').det = u ^ 2 * (wallGram Q K P R).det := by
  obtain ⟨hTR, hinj, hspan⟩ := hf
  obtain ⟨hTR', hinj', hspan'⟩ := hf'
  set S := mat Q K σ
  have hcol : ∀ j, ∃ c : Fin m → K, (fun i => P' i j) = P *ᵥ c := by
    intro j
    obtain ⟨c, hc⟩ := hspan (fun k => R' k j)
    refine ⟨c, ?_⟩
    rw [← hc]
    ext i
    rw [← mul_apply_col, hTR']
  choose c hc using hcol
  set U : Matrix (Fin m) (Fin m) K := Matrix.of fun i j => c j i
  have hPU : P * U = P' := by
    ext i j
    rw [mul_apply_col]
    exact (congrFun (hc j) i).symm
  set Y := R' - R * U
  have hY : ∀ j, S *ᵥ (fun k => Y k j) = fun k => Y k j := by
    intro j
    have h0 : (1 - S) * Y = 0 := by
      simp only [Y, Matrix.mul_sub, hTR', ← Matrix.mul_assoc, hTR, hPU, sub_self]
    have e : (1 - S) *ᵥ (fun k => Y k j) = 0 := by
      ext k; rw [← mul_apply_col, h0]; rfl
    rw [sub_mulVec, one_mulVec, sub_eq_zero] at e
    exact e.symm
  have hPY : Pᵀ * Hk * Y = 0 := by
    ext i j
    rw [gram_apply]
    have : (fun k => P k i) = (1 - S) *ᵥ (fun k => R k i) := by
      ext k; rw [← mul_apply_col, hTR]
    rw [this, orth_ker σ _ _ (hY j)]
    rfl
  have hR' : R' = R * U + Y := by simp [Y]
  have hG : wallGram Q K P' R' = Uᵀ * wallGram Q K P R * U := by
    simp only [wallGram, ← hPU, hR', Matrix.mul_add, transpose_mul]
    rw [show Uᵀ * Pᵀ * Hk * Y = Uᵀ * (Pᵀ * Hk * Y) by simp only [Matrix.mul_assoc], hPY, Matrix.mul_zero,
      add_zero]
    simp only [Matrix.mul_assoc]
  have hU : U.det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hx0
    apply hinj' x
    rw [← hPU, ← mulVec_mulVec, hx, mulVec_zero]
  refine ⟨U.det, hU, ?_⟩
  rw [hG, det_mul, det_mul, det_transpose]
  ring

theorem sqClassOf_wallDet_eq (σ : orthGroup Q K) {m : ℕ} {P R P' R' : Matrix (Fin n) (Fin m) K}
    (hf : IsWallFrame K (mat Q K σ) P R) (hf' : IsWallFrame K (mat Q K σ) P' R') :
    sqClassOf (wallGram Q K P' R').det = sqClassOf (wallGram Q K P R).det ∧
      ((wallGram Q K P' R').det ≠ 0 ↔ (wallGram Q K P R).det ≠ 0) := by
  obtain ⟨u, hu, h⟩ := wallDet_eq σ hf hf'
  refine ⟨by rw [h, sqClassOf_sq_mul' hu], ?_⟩
  rw [h]
  constructor
  · intro h1 h2; exact h1 (by rw [h2, mul_zero])
  · intro h1; exact mul_ne_zero (pow_ne_zero 2 hu) h1

/-! ### Matrix versions (any symmetric Gram matrix $G$ with $S^{\mathsf T} G S = G$) -/

section MatrixVersion

variable {G S : Matrix (Fin n) (Fin n) K}

theorem orth_ker_mat (hS : Sᵀ * G * S = G) (z y : Fin n → K) (hy : S *ᵥ y = y) :
    ((1 - S) *ᵥ z) ⬝ᵥ (G *ᵥ y) = 0 := by
  have e : (S *ᵥ z) ⬝ᵥ (G *ᵥ y) = z ⬝ᵥ (G *ᵥ y) := by
    conv_lhs => rw [← hy]
    rw [← vecMul_transpose S z, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hS]
  rw [sub_mulVec, one_mulVec, sub_dotProduct, e, sub_self]

/-- Two Wall frames of the same size: the Gram determinants $\det(P^{\mathsf T} G R)$ differ by a nonzero square. -/
theorem wallDet_eq_mat (hS : Sᵀ * G * S = G) {m : ℕ} {P R P' R' : Matrix (Fin n) (Fin m) K}
    (hf : IsWallFrame K S P R) (hf' : IsWallFrame K S P' R') :
    ∃ u : K, u ≠ 0 ∧ (P'ᵀ * G * R').det = u ^ 2 * (Pᵀ * G * R).det := by
  obtain ⟨hTR, hinj, hspan⟩ := hf
  obtain ⟨hTR', hinj', hspan'⟩ := hf'
  have hcol : ∀ j, ∃ c : Fin m → K, (fun i => P' i j) = P *ᵥ c := by
    intro j
    obtain ⟨c, hc⟩ := hspan (fun k => R' k j)
    refine ⟨c, ?_⟩
    rw [← hc]
    ext i
    rw [← mul_apply_col, hTR']
  choose c hc using hcol
  set U : Matrix (Fin m) (Fin m) K := Matrix.of fun i j => c j i
  have hPU : P * U = P' := by
    ext i j
    rw [mul_apply_col]
    exact (congrFun (hc j) i).symm
  set Y := R' - R * U
  have hY : ∀ j, S *ᵥ (fun k => Y k j) = fun k => Y k j := by
    intro j
    have h0 : (1 - S) * Y = 0 := by
      simp only [Y, Matrix.mul_sub, hTR', ← Matrix.mul_assoc, hTR, hPU, sub_self]
    have e : (1 - S) *ᵥ (fun k => Y k j) = 0 := by
      ext k; rw [← mul_apply_col, h0]; rfl
    rw [sub_mulVec, one_mulVec, sub_eq_zero] at e
    exact e.symm
  have hPY : Pᵀ * G * Y = 0 := by
    ext i j
    have hga : (Pᵀ * G * Y) i j = (fun k => P k i) ⬝ᵥ (G *ᵥ fun k => Y k j) := by
      simp only [Matrix.mul_apply, transpose_apply, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [hga]
    have : (fun k => P k i) = (1 - S) *ᵥ (fun k => R k i) := by
      ext k; rw [← mul_apply_col, hTR]
    rw [this, orth_ker_mat hS _ _ (hY j)]
    rfl
  have hR' : R' = R * U + Y := by simp [Y]
  have hG : P'ᵀ * G * R' = Uᵀ * (Pᵀ * G * R) * U := by
    simp only [← hPU, hR', Matrix.mul_add, transpose_mul]
    rw [show Uᵀ * Pᵀ * G * Y = Uᵀ * (Pᵀ * G * Y) by simp only [Matrix.mul_assoc], hPY, Matrix.mul_zero,
      add_zero]
    simp only [Matrix.mul_assoc]
  have hU : U.det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hx0
    apply hinj' x
    rw [← hPU, ← mulVec_mulVec, hx, mulVec_zero]
  refine ⟨U.det, hU, ?_⟩
  rw [hG, det_mul, det_mul, det_transpose]
  ring

/-- The symmetric part of the Wall form is half the form: $C + C^{\mathsf T} = P^{\mathsf T} G P$ for
$C = P^{\mathsf T} G R$. -/
theorem wall_symm_id (hG : Gᵀ = G) (hS : Sᵀ * G * S = G) {m : ℕ} {P R : Matrix (Fin n) (Fin m) K}
    (hTR : (1 - S) * R = P) : Pᵀ * G * R + (Pᵀ * G * R)ᵀ = Pᵀ * G * P := by
  have key : (1 - S)ᵀ * G * (1 - S) = (1 - S)ᵀ * G + G * (1 - S) := by
    rw [transpose_sub, transpose_one]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    rw [hS]
    abel
  subst hTR
  simp only [transpose_mul, transpose_transpose, hG]
  calc _ = Rᵀ * ((1 - S)ᵀ * G + G * (1 - S)) * R := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = Rᵀ * ((1 - S)ᵀ * G * (1 - S)) * R := by rw [key]
    _ = Rᵀ * (1 - S)ᵀ * G * ((1 - S) * R) := by simp only [Matrix.mul_assoc]

end MatrixVersion

/-! ### Existence of frames -/

/-- **Every $S$ has a Wall frame** (a basis of $V_\sigma = (1 - S)V$ and preimages). -/
theorem exists_wallFrame (S : Matrix (Fin n) (Fin n) K) :
    ∃ m, ∃ P R : Matrix (Fin n) (Fin m) K, IsWallFrame K S P R := by
  set W := LinearMap.range (Matrix.toLin' (1 - S))
  set b := Module.finBasis K W
  have hpre : ∀ j, ∃ z : Fin n → K, (1 - S) *ᵥ z = (b j : Fin n → K) := by
    intro j
    obtain ⟨z, hz⟩ := (b j).2
    exact ⟨z, by rw [← Matrix.toLin'_apply]; exact hz⟩
  choose z hz using hpre
  refine ⟨Module.finrank K W, Matrix.of fun i j => (b j : Fin n → K) i, Matrix.of fun i j => z j i, ?_, ?_, ?_⟩
  · ext i j
    rw [mul_apply_col]
    exact congrFun (hz j) i
  · intro c hc
    rw [mulVec_eq_sum_cols] at hc
    have h2 : ∑ j, c j • b j = 0 := by
      ext i
      have := congrFun hc i
      simpa [Submodule.coe_sum, Finset.sum_apply] using this
    exact funext ((Fintype.linearIndependent_iff.mp b.linearIndependent) c h2)
  · intro y
    have hy : (1 - S) *ᵥ y ∈ W := ⟨y, Matrix.toLin'_apply _ _⟩
    refine ⟨b.repr ⟨_, hy⟩, ?_⟩
    conv_rhs => rw [mulVec_eq_sum_cols]
    have := b.sum_repr ⟨_, hy⟩
    have h2 := congrArg (fun w : W => (w : Fin n → K)) this
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    exact h2.symm

/-! ### Multiplying by a symmetry -/

theorem mat_mul (σ τ : orthGroup Q K) : mat Q K (σ * τ) = mat Q K σ * mat Q K τ := rfl

/-- $(1 - \tau_v S)r = (1 - S)r + \frac{B(v, Sr)}{Q(v)}\,v$. -/
theorem one_sub_symm_mul_mulVec {v : Fin n → K} (hv : Q.evalIn K v ≠ 0) (σ : orthGroup Q K) (r : Fin n → K) :
    (1 - mat Q K (symm Q K v * σ)) *ᵥ r =
      (1 - mat Q K σ) *ᵥ r + ((v ⬝ᵥ (Hk *ᵥ (mat Q K σ *ᵥ r))) / Q.evalIn K v) • v := by
  rw [mat_mul, sub_mulVec, one_mulVec, ← mulVec_mulVec, symm_mulVec_bil Q K hv, sub_mulVec, one_mulVec]
  simp only [qbil]
  abel

theorem mulVec_snoc {m : ℕ} (P : Matrix (Fin n) (Fin m) K) (v : Fin n → K) (c : Fin (m + 1) → K) :
    (Matrix.of fun i j => Fin.lastCases (v i) (fun j => P i j) j : Matrix (Fin n) (Fin (m + 1)) K) *ᵥ c =
      P *ᵥ (fun j => c (Fin.castSucc j)) + c (Fin.last m) • v := by
  rw [mulVec_eq_sum_cols, mulVec_eq_sum_cols, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    ext i
    simp
  · congr 1
    ext i
    simp

/-- **The extension step** (first case): if $f$ is fixed by $\sigma$ with $B(v, f) \ne 0$, a Wall frame $(P, R)$ of
$\sigma$ extends to the Wall frame $(P \mid v, R')$ of $\tau_v\sigma$, and the determinant gets multiplied by $Q(v)$. -/
theorem wallFrame_extend (σ : orthGroup Q K) {v f : Fin n → K} (hv : Q.evalIn K v ≠ 0)
    (hf : mat Q K σ *ᵥ f = f) (hvf : v ⬝ᵥ (Hk *ᵥ f) ≠ 0) {m : ℕ} {P R : Matrix (Fin n) (Fin m) K}
    (hfr : IsWallFrame K (mat Q K σ) P R) :
    ∃ P' R' : Matrix (Fin n) (Fin (m + 1)) K, IsWallFrame K (mat Q K (symm Q K v * σ)) P' R' ∧
      (wallGram Q K P' R').det = Q.evalIn K v * (wallGram Q K P R).det := by
  obtain ⟨hTR, hinj, hspan⟩ := hfr
  set S := mat Q K σ with hS
  set β := v ⬝ᵥ (Hk *ᵥ f) with hβ
  set qv := Q.evalIn K v with hqv
  set P' : Matrix (Fin n) (Fin (m + 1)) K := Matrix.of fun i j => Fin.lastCases (v i) (fun j => P i j) j with hP'
  set r : Fin m → Fin n → K := fun j => (fun k => R k j) - ((v ⬝ᵥ (Hk *ᵥ (S *ᵥ fun k => R k j))) / β) • f
    with hr
  set R' : Matrix (Fin n) (Fin (m + 1)) K :=
    Matrix.of fun i j => Fin.lastCases ((qv / β) * f i) (fun j => r j i) j with hR'
  have hTf : (1 - S) *ᵥ f = 0 := by rw [sub_mulVec, one_mulVec, hf, sub_self]
  have hPcol : ∀ j, (fun k => P k j) = (1 - S) *ᵥ (fun k => R k j) := fun j => by
    ext k; rw [← mul_apply_col, hTR]
  have hPf : ∀ c, (P *ᵥ c) ⬝ᵥ (Hk *ᵥ f) = 0 := fun c => by
    have : P *ᵥ c = (1 - S) *ᵥ (R *ᵥ c) := by rw [mulVec_mulVec, hTR]
    rw [this]; exact orth_ker σ _ _ hf
  have hcolP : ∀ j, (fun k => P k j) ⬝ᵥ (Hk *ᵥ f) = 0 := fun j => by rw [hPcol]; exact orth_ker σ _ _ hf
  have hR'last : (fun k => R' k (Fin.last m)) = (qv / β) • f := by ext k; simp [hR']
  have hR'cs : ∀ j, (fun k => R' k (Fin.castSucc j)) = r j := by intro j; ext k; simp [hR']
  have hP'last : (fun k => P' k (Fin.last m)) = v := by ext k; simp [hP']
  have hP'cs : ∀ j, (fun k => P' k (Fin.castSucc j)) = fun k => P k j := by intro j; ext k; simp [hP']
  have hSc : ∀ c : K, S *ᵥ (c • f) = c • f := fun c => by rw [mulVec_smul, hf]
  have hBvf : ∀ c : K, v ⬝ᵥ (Hk *ᵥ (c • f)) = c * β := fun c => by
    rw [mulVec_smul, dotProduct_smul, smul_eq_mul]
  -- the columns of `R'` are mapped to the columns of `P'`
  have hcol_last : (1 - mat Q K (symm Q K v * σ)) *ᵥ ((qv / β) • f) = v := by
    rw [one_sub_symm_mul_mulVec hv, mulVec_smul, hTf, smul_zero, zero_add, hSc, hBvf]
    rw [show qv / β * β / qv = 1 by field_simp]
    exact one_smul K v
  have hcol_cs : ∀ j, (1 - mat Q K (symm Q K v * σ)) *ᵥ r j = fun k => P k j := by
    intro j
    rw [one_sub_symm_mul_mulVec hv]
    have h1 : (1 - S) *ᵥ r j = fun k => P k j := by
      simp only [hr, mulVec_sub, mulVec_smul, hTf, smul_zero, sub_zero]
      exact (hPcol j).symm
    have h2 : v ⬝ᵥ (Hk *ᵥ (S *ᵥ r j)) = 0 := by
      simp only [hr, mulVec_sub, hSc, dotProduct_sub, hBvf]
      field_simp
      ring
    rw [h1, h2, zero_div, zero_smul, add_zero]
  refine ⟨P', R', ⟨?_, ?_, ?_⟩, ?_⟩
  · ext i j
    rw [mul_apply_col]
    induction j using Fin.lastCases with
    | last => rw [hR'last, hcol_last]; simp [hP']
    | cast j => rw [hR'cs, hcol_cs]; simp [hP']
  · intro c hc
    rw [hP', mulVec_snoc] at hc
    have h1 := congrArg (fun w => w ⬝ᵥ (Hk *ᵥ f)) hc
    simp only [add_dotProduct, smul_dotProduct, hPf, zero_add, smul_eq_mul, zero_dotProduct] at h1
    have hlast : c (Fin.last m) = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h hvf
    rw [hlast, zero_smul, add_zero] at hc
    have hcs := hinj _ hc
    funext j
    induction j using Fin.lastCases with
    | last => exact hlast
    | cast j => exact congrFun hcs j
  · intro z
    obtain ⟨c, hc⟩ := hspan z
    refine ⟨Fin.snoc c ((v ⬝ᵥ (Hk *ᵥ (S *ᵥ z))) / qv), ?_⟩
    rw [one_sub_symm_mul_mulVec hv, hc, hP', mulVec_snoc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rfl
  · -- the Gram matrix is block triangular with corner `Q(v)`
    have hG : ∀ i j, wallGram Q K P' R' i j = (fun k => P' k i) ⬝ᵥ (Hk *ᵥ fun k => R' k j) :=
      fun i j => gram_apply P' R' i j
    have hcorner : wallGram Q K P' R' (Fin.last m) (Fin.last m) = qv := by
      rw [hG, hP'last, hR'last, hBvf]; field_simp
    have hcolz : ∀ i : Fin m, wallGram Q K P' R' (Fin.castSucc i) (Fin.last m) = 0 := by
      intro i
      rw [hG, hP'cs, hR'last, mulVec_smul, dotProduct_smul, hcolP, smul_zero]
    have hblock : (wallGram Q K P' R').submatrix Fin.castSucc Fin.castSucc = wallGram Q K P R := by
      ext i j
      rw [submatrix_apply, hG, hP'cs, hR'cs, wallGram, gram_apply]
      simp only [hr, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hcolP, smul_zero, sub_zero]
    rw [det_succ_column _ (Fin.last m), Fin.sum_univ_castSucc]
    simp only [hcolz, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, hcorner, Fin.succAbove_last,
      hblock]
    rw [show ((Fin.last m : Fin (m + 1)) : ℕ) + ((Fin.last m : Fin (m + 1)) : ℕ) = 2 * m by simp; ring,
      pow_mul]
    simp

/-! ### $V_\sigma = (\ker T)^\perp$ -/

theorem dot_hess_comm (x y : Fin n → K) : x ⬝ᵥ (Hk *ᵥ y) = y ⬝ᵥ (Hk *ᵥ x) := by
  simpa [qbil] using qbil_comm Q K x y

/-- **$V_\sigma = (\ker T)^\perp$**: a vector $B$-orthogonal to every fixed vector of $\sigma$ lies in $(1 - S)V$. -/
theorem mem_range_of_orth_ker (hQ : Q.Nondegenerate) (σ : orthGroup Q K) (v : Fin n → K)
    (h : ∀ f, mat Q K σ *ᵥ f = f → v ⬝ᵥ (Hk *ᵥ f) = 0) : ∃ u, (1 - mat Q K σ) *ᵥ u = v := by
  set T := 1 - mat Q K σ
  set B : LinearMap.BilinForm K (Fin n → K) := Matrix.toBilin' Hk
  have hdet : (Q.hessian.map (algebraMap F K)).det ≠ 0 := by
    have e := RingHom.map_det (algebraMap F K) Q.hessian
    rw [RingHom.mapMatrix_apply] at e
    rw [← e]
    exact (map_ne_zero _).mpr hQ
  have hB : B.Nondegenerate := LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hdet
  set Z := LinearMap.ker (Matrix.toLin' T)
  set W := LinearMap.range (Matrix.toLin' T)
  have hBapp : ∀ x y, B x y = x ⬝ᵥ (Hk *ᵥ y) := fun x y => Matrix.toBilin'_apply' Hk x y
  have hfix : ∀ x ∈ Z, mat Q K σ *ᵥ x = x := fun x hx => by
    have : T *ᵥ x = 0 := by simpa [Z] using hx
    rw [sub_mulVec, one_mulVec, sub_eq_zero] at this
    exact this.symm
  have hle : W ≤ B.orthogonal Z := by
    rintro _ ⟨z, rfl⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    rw [hBapp, Matrix.toLin'_apply, dot_hess_comm]
    exact orth_ker σ z x (hfix x hx)
  have hdim : Module.finrank K W = Module.finrank K (B.orthogonal Z) := by
    rw [LinearMap.BilinForm.finrank_orthogonal hB]
    have := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' T)
    have hZ : Module.finrank K (LinearMap.ker (Matrix.toLin' T)) = Module.finrank K Z := rfl
    have hW : Module.finrank K (LinearMap.range (Matrix.toLin' T)) = Module.finrank K W := rfl
    rw [Module.finrank_fin_fun] at this ⊢
    omega
  have heq := Submodule.eq_of_le_of_finrank_eq hle hdim
  have hv : v ∈ B.orthogonal Z := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    rw [hBapp, dot_hess_comm]
    exact h x (hfix x hx)
  rw [← heq] at hv
  obtain ⟨u, hu⟩ := hv
  exact ⟨u, by rw [← Matrix.toLin'_apply]; exact hu⟩

/-! ### Wall's formula -/

theorem mat_symmProd_nil : mat Q K (symmProd Q K []) = 1 := by
  simp [symmProd, mat]

theorem symmProd_cons (x : Fin n → K) (xs : List (Fin n → K)) :
    symmProd Q K (x :: xs) = symm Q K x * symmProd Q K xs := by
  simp [symmProd]

theorem valProd_cons (x : Fin n → K) (xs : List (Fin n → K)) :
    valProd Q K (x :: xs) = Q.evalIn K x * valProd Q K xs := by
  simp [valProd]

/-- The induction behind Wall's formula, over a factorization into symmetries. -/
theorem wall_symmProd (hQ : Q.Nondegenerate) :
    ∀ xs : List (Fin n → K), (∀ x ∈ xs, Q.evalIn K x ≠ 0) →
      ∀ {m : ℕ} (P R : Matrix (Fin n) (Fin m) K), IsWallFrame K (mat Q K (symmProd Q K xs)) P R →
        sqClassOf (wallGram Q K P R).det = sqClassOf (valProd Q K xs) ∧ (wallGram Q K P R).det ≠ 0 ∧
          (-1 : K) ^ m = (-1) ^ xs.length := by
  intro xs
  induction xs with
  | nil =>
    intro _ m P R hf
    rw [mat_symmProd_nil] at hf
    obtain ⟨hTR, hinj, -⟩ := hf
    have hP : P = 0 := by rw [← hTR]; simp
    cases m with
    | zero =>
      refine ⟨?_, ?_, by simp⟩
      · simp [valProd, Matrix.det_isEmpty]
      · simp [Matrix.det_isEmpty]
    | succ k =>
      exfalso
      have := hinj (Pi.single 0 1) (by rw [hP, zero_mulVec])
      have h1 := congrFun this 0
      simp at h1
  | cons x xs ih =>
    intro hxs m P R hf
    have hx : Q.evalIn K x ≠ 0 := hxs x List.mem_cons_self
    have hxs' : ∀ y ∈ xs, Q.evalIn K y ≠ 0 := fun y hy => hxs y (List.mem_cons_of_mem x hy)
    have hvp := valProd_ne_zero Q K hxs'
    rw [symmProd_cons] at hf
    rw [valProd_cons, sqClassOf_mul hx hvp, List.length_cons]
    set σ₀ := symmProd Q K xs
    by_cases hA : ∃ f, mat Q K σ₀ *ᵥ f = f ∧ x ⬝ᵥ (Hk *ᵥ f) ≠ 0
    · obtain ⟨f, hf0, hxf⟩ := hA
      obtain ⟨m₀, P₀, R₀, hfr₀⟩ := exists_wallFrame (mat Q K σ₀)
      obtain ⟨h1, h2, h3⟩ := ih hxs' P₀ R₀ hfr₀
      obtain ⟨P₁, R₁, hfr₁, hdet₁⟩ := wallFrame_extend σ₀ hx hf0 hxf hfr₀
      obtain rfl := wallFrame_size_eq hf hfr₁
      obtain ⟨hc, hne⟩ := sqClassOf_wallDet_eq (symm Q K x * σ₀) hfr₁ hf
      refine ⟨?_, ?_, ?_⟩
      · rw [hc, hdet₁, sqClassOf_mul hx h2, h1]
      · exact hne.mpr (by rw [hdet₁]; exact mul_ne_zero hx h2)
      · rw [pow_succ, pow_succ, h3]
    · simp only [not_exists, not_and, not_not] at hA
      obtain ⟨u, hu⟩ := mem_range_of_orth_ker hQ σ₀ x hA
      set σ := symm Q K x * σ₀
      have hxu : x ⬝ᵥ (Hk *ᵥ u) = Q.evalIn K x := by
        rw [← hu]; exact wall_diag σ₀ u
      have hS0u : mat Q K σ₀ *ᵥ u = u - x := by
        rw [← hu, sub_mulVec, one_mulVec]; abel
      have hfix : mat Q K σ *ᵥ u = u := by
        have e := one_sub_symm_mul_mulVec hx σ₀ u
        rw [hu, hS0u, mulVec_sub, dotProduct_sub, hxu, ← two_mul_evalIn] at e
        rw [show (Q.evalIn K x - 2 * Q.evalIn K x) / Q.evalIn K x = -1 by field_simp; ring] at e
        rw [neg_one_smul, add_neg_cancel, sub_mulVec, one_mulVec, sub_eq_zero] at e
        exact e.symm
      obtain ⟨m₁, P₁, R₁, hfr₁⟩ := exists_wallFrame (mat Q K σ)
      obtain ⟨P₂, R₂, hfr₂, hdet₂⟩ := wallFrame_extend σ hx hfix (by rw [hxu]; exact hx) hfr₁
      have hback : symm Q K x * σ = σ₀ := by
        simp only [σ, ← mul_assoc, symm_mul_self, one_mul]
      rw [hback] at hfr₂
      obtain ⟨h1, h2, h3⟩ := ih hxs' P₂ R₂ hfr₂
      obtain rfl := wallFrame_size_eq hf hfr₁
      obtain ⟨hc, hne⟩ := sqClassOf_wallDet_eq σ hfr₁ hf
      have hd1 : (wallGram Q K P₁ R₁).det ≠ 0 := by
        intro h0; apply h2; rw [hdet₂, h0, mul_zero]
      refine ⟨?_, hne.mpr hd1, ?_⟩
      · rw [hc, ← h1, hdet₂, sqClassOf_mul hx hd1, ← mul_assoc, SqClass.mul_self, one_mul]
      · rw [pow_succ] at h3
        rw [pow_succ, ← h3]
        ring

/-- **Wall's formula for the spinor norm** (G. E. Wall 1959; H. Zassenhaus 1962): for nondegenerate $Q$ and every
Wall frame $(P, R)$ of $\sigma \in O(V)(K)$, of size $m = \dim(1 - \sigma)V$,
$\theta(\sigma) = \det(P^{\mathsf T} H R)\,K^{\times 2}$, this determinant is nonzero, and $\det\sigma = (-1)^m$. -/
@[kb "conwaysloane1999" "Ch. 15, §9.3, p. 390 (spinor norm; computed by Wall's formula)"]
theorem wall_formula (hQ : Q.Nondegenerate) (σ : orthGroup Q K) {m : ℕ} {P R : Matrix (Fin n) (Fin m) K}
    (hf : IsWallFrame K (mat Q K σ) P R) :
    spinorNorm Q K σ = sqClassOf (wallGram Q K P R).det ∧ (wallGram Q K P R).det ≠ 0 ∧
      (mat Q K σ).det = (-1) ^ m := by
  obtain ⟨xs, hxs, rfl⟩ := exists_symmProd_eq Q K hQ σ
  obtain ⟨h1, h2, h3⟩ := wall_symmProd hQ xs hxs P R hf
  refine ⟨by rw [spinorNorm_symmProd Q K hQ xs hxs, h1], h2, ?_⟩
  rw [h3, ← detHom_symmProd Q K xs hxs, detHom_val]

end QuadFormsKB.ConwaySloane.Wall
