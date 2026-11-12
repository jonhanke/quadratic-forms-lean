/-
# Kitaoka 1993, Section 2.1: proof of Lemma 2.1.3 (every $g$ has a $\Gamma$-translate in a Siegel domain)

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §2.1, Lemma 2.1.3, pp. 35–36 (printed pages).

**Proves** `lemma213 : Lemma213`: for $m \ge 2$ and $g \in G = \mathrm{GL}_m(\mathbb R)$ there is
$\gamma_0 \in \Gamma = \mathrm{GL}_m(\mathbb Z)$ with $\phi(g\gamma_0) = \min_{\gamma \in \Gamma} \phi(g\gamma)$ and
$g\gamma_0 \in \tilde S_{2/\sqrt3, 1/2}$.

**Proof** (Kitaoka's induction on $m$, run from $m = 1$, where the Siegel conditions are empty).
1. *The minimum exists* (`exists_min_firstColNorm`): $\phi(g\gamma) = |g x|$ for the first column $x \in \mathbb Z^m$ of
   $\gamma$, and only finitely many $x \in \mathbb Z^m$ satisfy $|g x| \le \phi(g)$, since
   $|x_i| \le \sum_j |(g^{-1})_{ij}|\,|g x|$.
2. *Induction step.* Let $\gamma'$ realize the minimum and $g\gamma' = k a n$ (Iwasawa decomposition,
   `iwasawaDecomposition`). Then $a n = \begin{pmatrix} a_0 & r \\ 0 & b\end{pmatrix}$ with $b \in \mathrm{GL}_{m-1}(\mathbb R)$
   (block matrices are `blk`). The induction hypothesis gives $x \in \mathrm{GL}_{m-1}(\mathbb Z)$ with
   $b x = k' a' n'$ in the Siegel domain of size $m - 1$, so with $D = \mathrm{diag}(1, x)$
   $$g\gamma' D = k\,\mathrm{diag}(1, k')\,\mathrm{diag}(a_0, a')\,\begin{pmatrix} 1 & a_0^{-1} r x \\ 0 & n'\end{pmatrix}.$$
   Lemma 2.1.1 writes the last factor as $z y$ with $z \in N_{1/2}$ and $y \in N_{\mathbb Z}$; put
   $\gamma_0 = \gamma' D y^{-1}$. Since $D$ and $y^{-1}$ fix the first basis vector, $\phi(g\gamma_0) = \phi(g\gamma')$ is
   still the minimum, and then Lemma 2.1.2 (`lemma212`) applied to $g\gamma_0$ gives $a_0 / a'_0 \le 2/\sqrt3$; the
   other ratios are bounded by the induction hypothesis.
-/
import QuadFormsKB.Literature.Kitaoka.Ch2ReductionProofs
import QuadFormsKB.Literature.Kitaoka.Ch2Lemma212
import Mathlib.Data.Pi.Interval
import Mathlib.Order.Interval.Finset.Defs

open Matrix

noncomputable section

namespace QuadFormsKB.Kitaoka.Reduction

/-! ### Block matrices $\begin{pmatrix} c & r \\ 0 & B \end{pmatrix}$ -/

/-- The $(m+1) \times (m+1)$ block matrix $\begin{pmatrix} c & r \\ 0 & B \end{pmatrix}$ (first row $(c, r)$, first
column $(c, 0, \dots, 0)$). -/
def blk {R : Type*} [Zero R] {m : ℕ} (c : R) (r : Fin m → R) (B : Matrix (Fin m) (Fin m) R) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of fun i j => Fin.cases (Fin.cases c r j) (fun i' => Fin.cases 0 (B i') j) i

section blk

variable {R : Type*} {m : ℕ}

@[simp] theorem blk_zero_zero [Zero R] (c : R) (r : Fin m → R) (B : Matrix (Fin m) (Fin m) R) :
    blk c r B 0 0 = c := rfl

@[simp] theorem blk_zero_succ [Zero R] (c : R) (r : Fin m → R) (B : Matrix (Fin m) (Fin m) R) (j : Fin m) :
    blk c r B 0 j.succ = r j := rfl

@[simp] theorem blk_succ_zero [Zero R] (c : R) (r : Fin m → R) (B : Matrix (Fin m) (Fin m) R) (i : Fin m) :
    blk c r B i.succ 0 = 0 := rfl

@[simp] theorem blk_succ_succ [Zero R] (c : R) (r : Fin m → R) (B : Matrix (Fin m) (Fin m) R) (i j : Fin m) :
    blk c r B i.succ j.succ = B i j := rfl

theorem blk_mul [CommSemiring R] (c c' : R) (r r' : Fin m → R) (B B' : Matrix (Fin m) (Fin m) R) :
    blk c r B * blk c' r' B' = blk (c * c') (c • r' + r ᵥ* B') (B * B') := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, vecMul, dotProduct]

theorem blk_one [CommSemiring R] : blk (1 : R) 0 (1 : Matrix (Fin m) (Fin m) R) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp [Matrix.one_apply_ne (Fin.succ_ne_zero j).symm]
  · simp [Matrix.one_apply_ne (Fin.succ_ne_zero i)]
  · simp [Matrix.one_apply, Fin.succ_inj]

theorem blk_transpose [Zero R] (c : R) (B : Matrix (Fin m) (Fin m) R) : (blk c 0 B)ᵀ = blk c 0 Bᵀ := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem blk_diagonal [Zero R] (c : R) (α : Fin m → R) :
    blk c 0 (diagonal α) = diagonal (Fin.cons c α : Fin (m + 1) → R) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [diagonal_apply, Fin.succ_ne_zero, eq_comm]

theorem blk_one_col [Zero R] [One R] (r : Fin m → R) (B : Matrix (Fin m) (Fin m) R) (j : Fin (m + 1)) :
    blk (1 : R) r B j 0 = if j = 0 then 1 else 0 := by
  refine Fin.cases ?_ (fun j => ?_) j <;> simp [Fin.succ_ne_zero]

end blk

/-! ### The function $\phi$ -/

variable {m : ℕ}

theorem firstColNorm_succ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :
    firstColNorm g = Real.sqrt (∑ i, (g i 0) ^ 2) := by
  simp [firstColNorm]

/-- $\phi(hM) = \phi(h)$ when $M$ fixes the first basis vector $e_0$. -/
theorem firstColNorm_mul_of_col (h M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hM : ∀ j, M j 0 = if j = 0 then 1 else 0) : firstColNorm (h * M) = firstColNorm h := by
  rw [firstColNorm_succ, firstColNorm_succ]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.mul_apply, hM]

theorem unitri_col {n : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hn : n ∈ unitri (m + 1)) (j : Fin (m + 1)) :
    n j 0 = if j = 0 then 1 else 0 := by
  by_cases hj : j = 0
  · subst hj; simp [hn.2]
  · simp only [hj, ↓reduceIte]
    exact hn.1 (Fin.pos_iff_ne_zero.2 hj)

/-- The real matrix of $\gamma \in \mathrm{GL}_m(\mathbb Z)$ is multiplicative. -/
theorem intCast_mul (γ δ : GL (Fin m) ℤ) : intCast (γ * δ) = intCast γ * intCast δ := by
  simp only [intCast, Units.val_mul, map_cast_mul']

/-- $\gamma \in \mathrm{GL}_m(\mathbb Z)$ as an element of $\mathrm{GL}_m(\mathbb R)$. -/
def glCast (γ : GL (Fin m) ℤ) : GL (Fin m) ℝ := Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) γ

theorem coe_glCast (γ : GL (Fin m) ℤ) : (glCast γ : Matrix (Fin m) (Fin m) ℝ) = intCast γ := by
  ext i j; simp [glCast, intCast, Matrix.GeneralLinearGroup.map_apply]

/-- **Step 1: the minimum of $\phi(g\gamma)$ over $\Gamma$ is attained.** -/
theorem exists_min_firstColNorm (g : GL (Fin (m + 1)) ℝ) :
    ∃ γ₀ : GL (Fin (m + 1)) ℤ, ∀ γ : GL (Fin (m + 1)) ℤ,
      firstColNorm ((g : Matrix _ _ ℝ) * intCast γ₀) ≤ firstColNorm ((g : Matrix _ _ ℝ) * intCast γ) := by
  classical
  set G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := ↑g
  let col : GL (Fin (m + 1)) ℤ → (Fin (m + 1) → ℤ) := fun γ j => (γ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) j 0
  let F : (Fin (m + 1) → ℤ) → ℝ := fun x => Real.sqrt (∑ i, ((G *ᵥ fun j => (x j : ℝ)) i) ^ 2)
  have hF : ∀ γ, firstColNorm (G * intCast γ) = F (col γ) := by
    intro γ
    rw [firstColNorm_succ]
    simp [F, col, intCast, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  set R := F (col 1)
  set Gi : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := (g⁻¹ : GL (Fin (m + 1)) ℝ).val
  have hinv : Gi * G = 1 := by
    simp only [Gi, G]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  set N : ℕ := ⌈∑ i, ∑ j, |Gi i j| * R⌉₊
  have hbound : ∀ x, F x ≤ R → ∀ i, |x i| ≤ (N : ℤ) := by
    intro x hx i
    set xr : Fin (m + 1) → ℝ := fun j => (x j : ℝ)
    set y := G *ᵥ xr
    have hy : ∀ j, |y j| ≤ R := by
      intro j
      refine le_trans ?_ hx
      apply Real.abs_le_sqrt
      exact Finset.single_le_sum (f := fun k => (y k) ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    have hxi : (x i : ℝ) = (Gi *ᵥ y) i := by
      simp only [y, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, xr]
    have h1 : |(x i : ℝ)| ≤ ∑ j, |Gi i j| * R := by
      rw [hxi]
      simp only [Matrix.mulVec, dotProduct]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hy j) (abs_nonneg _)
    have hR : 0 ≤ R := Real.sqrt_nonneg _
    have h2 : ∑ j, |Gi i j| * R ≤ ∑ i', ∑ j, |Gi i' j| * R :=
      Finset.single_le_sum (f := fun i' => ∑ j, |Gi i' j| * R)
        (fun i' _ => Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) hR) (Finset.mem_univ i)
    have h3 : |(x i : ℝ)| ≤ (N : ℝ) := h1.trans (h2.trans (Nat.le_ceil _))
    have h4 : ((|x i| : ℤ) : ℝ) ≤ ((N : ℤ) : ℝ) := by rw [Int.cast_abs]; exact_mod_cast h3
    exact_mod_cast h4
  let S : Set (Fin (m + 1) → ℤ) := {x | (∃ γ, col γ = x) ∧ F x ≤ R}
  have hS : S.Finite := by
    refine (Set.finite_Icc (fun _ => -(N : ℤ)) (fun _ => (N : ℤ))).subset fun x hx => ?_
    have hb := hbound x hx.2
    exact ⟨fun i => (abs_le.1 (hb i)).1, fun i => (abs_le.1 (hb i)).2⟩
  have hne : S.Nonempty := ⟨col 1, ⟨1, rfl⟩, le_rfl⟩
  obtain ⟨x₀, ⟨⟨γ₀, rfl⟩, hx₀R⟩, hmin⟩ := Set.exists_min_image S F hS hne
  refine ⟨γ₀, fun γ => ?_⟩
  rw [hF, hF]
  by_cases h : F (col γ) ≤ R
  · exact hmin _ ⟨⟨γ, rfl⟩, h⟩
  · exact hx₀R.trans (le_of_not_ge h)

/-- `diag(1, x)` for $x \in \mathrm{GL}_m(\mathbb Z)$, as an element of $\mathrm{GL}_{m+1}(\mathbb Z)$. -/
def glBlk (x : GL (Fin m) ℤ) : GL (Fin (m + 1)) ℤ where
  val := blk 1 0 (x : Matrix (Fin m) (Fin m) ℤ)
  inv := blk 1 0 ((x⁻¹ : GL (Fin m) ℤ) : Matrix (Fin m) (Fin m) ℤ)
  val_inv := by rw [blk_mul]; simp [blk_one]
  inv_val := by rw [blk_mul]; simp [blk_one]

theorem intCast_glBlk (x : GL (Fin m) ℤ) : intCast (glBlk x) = blk 1 0 (intCast x) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [intCast, glBlk]

/-- The general form of Lemma 2.1.3, for every size $m + 1 \ge 1$ (for size $1$ the Siegel conditions are empty). -/
theorem lemma213_aux : ∀ (m : ℕ) (g : GL (Fin (m + 1)) ℝ), ∃ γ₀ : GL (Fin (m + 1)) ℤ,
    (∀ γ : GL (Fin (m + 1)) ℤ, firstColNorm ((g : Matrix _ _ ℝ) * intCast γ₀) ≤
      firstColNorm ((g : Matrix _ _ ℝ) * intCast γ)) ∧
    (g : Matrix _ _ ℝ) * intCast γ₀ ∈ siegelDomainG (m + 1) (2 / Real.sqrt 3) (1 / 2) := by
  intro m
  induction m with
  | zero =>
    intro g
    obtain ⟨γ₀, hmin⟩ := exists_min_firstColNorm g
    obtain ⟨k, hk, a, ⟨α, hα, rfl⟩, n, hn, hEq⟩ := iwasawaDecomposition 1 (g * glCast γ₀)
    rw [Units.val_mul, coe_glCast] at hEq
    refine ⟨γ₀, hmin, k, hk, diagonal α, ⟨α, hα, fun i j h => ?_, rfl⟩, n, ⟨hn, fun i j hij => ?_⟩, hEq⟩
    · exfalso; have := j.isLt; omega
    · exfalso; have h1 := j.isLt; have h2 : i.val < j.val := hij; omega
  | succ m ih =>
    intro g
    classical
    obtain ⟨γ', hmin⟩ := exists_min_firstColNorm g
    obtain ⟨k, hk, a, ⟨α, hα, rfl⟩, n, hn, hEq⟩ := iwasawaDecomposition (m + 2) (g * glCast γ')
    rw [Units.val_mul, coe_glCast] at hEq
    -- the block form of `diagonal α * n`
    set n₁ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := n.submatrix Fin.succ Fin.succ with hn₁
    set r : Fin (m + 1) → ℝ := fun j => α 0 * n 0 j.succ with hr
    set b : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := diagonal (fun i => α i.succ) * n₁ with hb
    have hblk : diagonal α * n = blk (α 0) r b := by
      ext i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simp [diagonal_mul, hn.2]
      · simp [diagonal_mul, hr]
      · have h0 : n i.succ 0 = 0 := hn.1 (Fin.succ_pos i)
        simp [diagonal_mul, h0]
      · simp [diagonal_mul, hb, hn₁]
    have hn₁u : n₁.IsUpperTriangular := fun i j h => hn.1 (Fin.succ_lt_succ_iff.2 h)
    have hbdet : IsUnit b.det := by
      rw [hb, det_mul, det_diagonal, Matrix.det_of_isUpperTriangular hn₁u]
      simp only [hn₁, submatrix_apply, hn.2, Finset.prod_const_one, mul_one]
      exact (Finset.prod_pos fun i _ => hα i.succ).ne'.isUnit
    obtain ⟨x, -, k', hk', a', ⟨α', hα'pos, hα't, rfl⟩, n', hn', hbx⟩ := ih (Matrix.nonsingInvUnit b hbdet)
    simp only [Matrix.nonsingInvUnit] at hbx
    -- the new triangular factor
    set s : Fin (m + 1) → ℝ := (α 0)⁻¹ • (r ᵥ* intCast x) with hs
    set N₁ : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ := blk 1 s n' with hN₁
    have hN₁u : N₁ ∈ unitri (m + 2) := by
      refine ⟨fun i j h => ?_, fun i => ?_⟩
      · revert h
        refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> intro h
        · exact absurd h (lt_irrefl _)
        · exact absurd h (not_lt.2 (Fin.zero_le _))
        · simp [hN₁]
        · simpa [hN₁] using hn'.1.1 (Fin.succ_lt_succ_iff.1 h)
      · refine Fin.cases ?_ (fun i => ?_) i
        · simp [hN₁]
        · simp [hN₁, hn'.1.2 i]
    set K₁ : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ := blk 1 0 k' with hK₁
    set α₁ : Fin (m + 2) → ℝ := Fin.cons (α 0) α' with hα₁
    have hkey : (g : Matrix _ _ ℝ) * intCast γ' * intCast (glBlk x) = (k * K₁) * diagonal α₁ * N₁ := by
      have h0 : (α 0) ≠ 0 := (hα 0).ne'
      rw [hEq, intCast_glBlk, Matrix.mul_assoc k, hblk, hα₁, ← blk_diagonal, hK₁, hN₁, Matrix.mul_assoc k,
        Matrix.mul_assoc k, Matrix.mul_assoc k]
      congr 1
      rw [blk_mul, blk_mul, blk_mul, ← hbx]
      congr 1
      · ring
      · simp only [hs, smul_zero, zero_add, zero_vecMul, add_zero, one_smul, smul_smul, one_mul,
          mul_inv_cancel₀ h0]
    -- Lemma 2.1.1 on N₁
    obtain ⟨z, hz, Y, hYu, hN₁eq⟩ := lemma211 (m + 2) N₁ hN₁u
    have hYZ : UTri Y := by
      refine ⟨fun i j h => ?_, fun i => ?_⟩
      · have := hYu.1 h
        simpa using this
      · have := hYu.2 i
        simpa using this
    obtain ⟨Yi, hYi, hYYi⟩ := hYZ.exists_inv
    have hYiY : Yi * Y = 1 := mul_eq_one_comm.1 hYYi
    let YU : GL (Fin (m + 2)) ℤ := ⟨Yi, Y, hYiY, hYYi⟩
    have hYUcast : intCast YU = Yi.map (Int.cast : ℤ → ℝ) := rfl
    set γ₀ : GL (Fin (m + 2)) ℤ := γ' * glBlk x * YU with hγ₀
    -- the minimum is still attained at `γ₀`
    have hφ : firstColNorm ((g : Matrix _ _ ℝ) * intCast γ₀) = firstColNorm ((g : Matrix _ _ ℝ) * intCast γ') := by
      rw [hγ₀, intCast_mul, intCast_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hYUcast,
        firstColNorm_mul_of_col _ _ (unitri_col ((mem_unitri_iff _).2 hYi.map_cast)),
        intCast_glBlk, firstColNorm_mul_of_col _ _ (blk_one_col _ _)]
    have hmin₀ : ∀ γ : GL (Fin (m + 2)) ℤ, firstColNorm ((g : Matrix _ _ ℝ) * intCast γ₀) ≤
        firstColNorm ((g : Matrix _ _ ℝ) * intCast γ) := fun γ => hφ ▸ hmin γ
    -- `g γ₀ = (k K₁) diag(α₁) z`
    have hG₀ : (g : Matrix _ _ ℝ) * intCast γ₀ = (k * K₁) * diagonal α₁ * z := by
      rw [hγ₀, intCast_mul, intCast_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hkey, hN₁eq, hYUcast]
      simp only [Matrix.mul_assoc, ← map_cast_mul', hYYi, map_cast_one', Matrix.mul_one]
    have hK₁orth : K₁ ∈ Matrix.orthogonalGroup (Fin (m + 2)) ℝ := by
      have hk'' : k'ᵀ * k' = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin (m + 1)) ℝ).1 hk'
      refine (Matrix.mem_orthogonalGroup_iff' (Fin (m + 2)) ℝ).2 ?_
      rw [hK₁, blk_transpose, blk_mul]
      simp [hk'', blk_one]
    have hkK₁ : k * K₁ ∈ orthMat (m + 2) := Submonoid.mul_mem _ hk hK₁orth
    have hα₁pos : ∀ i, 0 < α₁ i := fun i =>
      Fin.cases (by simpa [hα₁] using hα 0) (fun i => by simpa [hα₁] using hα'pos i) i
    -- Lemma 2.1.2 for `g γ₀`
    have hfirst := lemma212 (m + 2) (by omega) (g * glCast γ₀) (k * K₁) α₁ z hkK₁ hα₁pos hz.1
      (by rw [Units.val_mul, coe_glCast]; exact hG₀)
      (by
        intro γ
        rw [Units.val_mul, coe_glCast, Matrix.mul_assoc, ← intCast_mul]
        exact hmin₀ _)
    refine ⟨γ₀, hmin₀, k * K₁, hkK₁, diagonal α₁, ⟨α₁, hα₁pos, fun i j hij => ?_, rfl⟩, z, hz, hG₀⟩
    revert hij
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> intro hij
    · simp at hij
    · have hj : j = 0 := Fin.ext (by simp [Fin.val_succ] at hij; omega)
      subst hj
      exact hfirst
    · simp at hij
    · simp only [hα₁, Fin.cons_succ]
      exact hα't i j (by simp [Fin.val_succ] at hij; omega)

/-- **Kitaoka 1993, Lemma 2.1.3** (p. 35), *proved*: for $m \ge 2$ and $g \in \mathrm{GL}_m(\mathbb R)$ there is
$\gamma_0 \in \mathrm{GL}_m(\mathbb Z)$ such that $\phi(g\gamma_0) = \min_{\gamma} \phi(g\gamma)$ and
$g\gamma_0 \in \tilde S_{2/\sqrt3, 1/2}$. Proof: Kitaoka's induction on $m$ (`lemma213_aux`, see the module docstring),
using Lemma 2.1.1, Lemma 2.1.2 and the Iwasawa decomposition. -/
@[kb "kitaoka1993" "§2.1, Lemma 2.1.3, p. 35"]
theorem lemma213 : Lemma213 := by
  intro m hm g
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  exact lemma213_aux m' g
