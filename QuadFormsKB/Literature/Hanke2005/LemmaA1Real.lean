import QuadFormsKB.Literature.Hanke2005.ArchSymmetricReal
import QuadFormsKB.Citation

open Matrix

noncomputable section

namespace QuadFormsKB.Hanke2005.ArchReal

variable {r t : ℕ}

/-- The embedding of the first block ($r$ coordinates) into `Fin (r + t + r)`. -/
def e1 (r t : ℕ) : Fin r → Fin (r + t + r) := fun i => Fin.castAdd r (Fin.castAdd t i)

/-- The embedding of the middle block ($t$ coordinates) into `Fin (r + t + r)`. -/
def e2 (r t : ℕ) : Fin t → Fin (r + t + r) := fun k => Fin.castAdd r (Fin.natAdd r k)

/-- The embedding of the last block ($r$ coordinates) into `Fin (r + t + r)`. -/
def e3 (r t : ℕ) : Fin r → Fin (r + t + r) := fun i => Fin.natAdd (r + t) i

theorem cBlk_mul_left (g : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ)
    (u : Matrix (Fin (r + t + r)) (Fin r) ℝ) :
    cBlk (g * u) = g.submatrix (e1 r t) (e1 r t) * cBlk u + g.submatrix (e1 r t) (e2 r t) * fBlk u +
      g.submatrix (e1 r t) (e3 r t) * wBlk u := by
  ext i j
  simp [cBlk, fBlk, wBlk, e1, e2, e3, Matrix.mul_apply, Fin.sum_univ_add, add_assoc]

theorem fBlk_mul_left (g : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ)
    (u : Matrix (Fin (r + t + r)) (Fin r) ℝ) :
    fBlk (g * u) = g.submatrix (e2 r t) (e1 r t) * cBlk u + g.submatrix (e2 r t) (e2 r t) * fBlk u +
      g.submatrix (e2 r t) (e3 r t) * wBlk u := by
  ext i j
  simp [cBlk, fBlk, wBlk, e1, e2, e3, Matrix.mul_apply, Fin.sum_univ_add, add_assoc]

theorem wBlk_mul_left (g : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ)
    (u : Matrix (Fin (r + t + r)) (Fin r) ℝ) :
    wBlk (g * u) = g.submatrix (e3 r t) (e1 r t) * cBlk u + g.submatrix (e3 r t) (e2 r t) * fBlk u +
      g.submatrix (e3 r t) (e3 r t) * wBlk u := by
  ext i j
  simp [cBlk, fBlk, wBlk, e1, e2, e3, Matrix.mul_apply, Fin.sum_univ_add, add_assoc]

theorem transpose_phiR_mul_blocks {s s' : ℕ} (u : Matrix (Fin (r + t + r)) (Fin s) ℝ)
    (v : Matrix (Fin (r + t + r)) (Fin s') ℝ) :
    uᵀ * phiR r t * v = (u.submatrix (e1 r t) id)ᵀ * v.submatrix (e1 r t) id +
      (u.submatrix (e2 r t) id)ᵀ * v.submatrix (e2 r t) id -
      (u.submatrix (e3 r t) id)ᵀ * v.submatrix (e3 r t) id := by
  ext i j
  rw [phiR, Matrix.mul_apply]
  simp only [mul_diagonal, transpose_apply]
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp [signVec, e1, e2, e3, Matrix.mul_apply]
  ring

/-- If $g\in O(\varphi_v)$ fixes $z\in Z_{\mathbb R}$, then $g\,P(z) = P(z)\,m$ for some $m$. -/
theorem exists_mul_frame {g : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ}
    (hg : gᵀ * phiR r t * g = phiR r t) {z : Fin (r + t) → Fin r → ℝ} (hz : z ∈ ZR r t)
    (hfix : actR g z = z) :
    ∃ m : Matrix (Fin r) (Fin r) ℝ, g * frameOf z 1 = frameOf z 1 * m := by
  have hneg : (-((g * frameOf z 1)ᵀ * phiR r t * (g * frameOf z 1))).PosDef := by
    have h1 : (g * frameOf z 1)ᵀ * phiR r t * (g * frameOf z 1) =
        (frameOf z 1)ᵀ * (gᵀ * phiR r t * g) * frameOf z 1 := by
      simp only [transpose_mul, Matrix.mul_assoc]
    have h2 : (g * frameOf z 1)ᵀ * phiR r t * (g * frameOf z 1) = -(xiR z) := by
      rw [h1, hg, transpose_frameOf_mul]; simp
    rw [h2, neg_neg]; exact hz
  have hU : IsUnit (wBlk (g * frameOf z 1) + cBlk (g * frameOf z 1)).det :=
    isUnit_iff_ne_zero.mpr (det_wc_ne_zero hneg)
  have h3 := frameOf_zOf hU
  have h4 : zOf (g * frameOf z 1) = z := hfix
  rw [h4] at h3
  refine ⟨wBlk (g * frameOf z 1) + cBlk (g * frameOf z 1), ?_⟩
  rw [← frameOf_eq_mul]; exact h3.symm

theorem xiR_zMk (x : Matrix (Fin r) (Fin r) ℝ) (y : Matrix (Fin t) (Fin r) ℝ) :
    xiR (zMk x y) = (1 / 2 : ℝ) • (xᵀ + x - yᵀ * y) := by
  simp [xiR]

/-- The block equations for $g\,P(z) = P(z)\,m$, $z = \begin{bmatrix}x\\y\end{bmatrix}$. -/
theorem fix_eqs {g : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ}
    (hg : gᵀ * phiR r t * g = phiR r t) (hfix : ∀ z ∈ ZR r t, actR g z = z)
    (x : Matrix (Fin r) (Fin r) ℝ) (y : Matrix (Fin t) (Fin r) ℝ) (hz : zMk x y ∈ ZR r t) :
    ∃ m : Matrix (Fin r) (Fin r) ℝ,
      g.submatrix (e1 r t) (e1 r t) * ((1 / 2 : ℝ) • (1 - x)) +
        g.submatrix (e1 r t) (e2 r t) * ((Real.sqrt 2)⁻¹ • y) +
        g.submatrix (e1 r t) (e3 r t) * ((1 / 2 : ℝ) • (1 + x)) = ((1 / 2 : ℝ) • (1 - x)) * m ∧
      g.submatrix (e2 r t) (e1 r t) * ((1 / 2 : ℝ) • (1 - x)) +
        g.submatrix (e2 r t) (e2 r t) * ((Real.sqrt 2)⁻¹ • y) +
        g.submatrix (e2 r t) (e3 r t) * ((1 / 2 : ℝ) • (1 + x)) = ((Real.sqrt 2)⁻¹ • y) * m ∧
      g.submatrix (e3 r t) (e1 r t) * ((1 / 2 : ℝ) • (1 - x)) +
        g.submatrix (e3 r t) (e2 r t) * ((Real.sqrt 2)⁻¹ • y) +
        g.submatrix (e3 r t) (e3 r t) * ((1 / 2 : ℝ) • (1 + x)) = ((1 / 2 : ℝ) • (1 + x)) * m := by
  obtain ⟨m, hm⟩ := exists_mul_frame hg hz (hfix _ hz)
  refine ⟨m, ?_, ?_, ?_⟩
  · have := congrArg cBlk hm
    rw [cBlk_mul_left, cBlk_mul, cBlk_frameOf, fBlk_frameOf, wBlk_frameOf] at this
    simpa only [xBlk_zMk, yBlk_zMk, Matrix.mul_one] using this
  · have := congrArg fBlk hm
    rw [fBlk_mul_left, fBlk_mul, cBlk_frameOf, fBlk_frameOf, wBlk_frameOf] at this
    simpa only [xBlk_zMk, yBlk_zMk, Matrix.mul_one] using this
  · have := congrArg wBlk hm
    rw [wBlk_mul_left, wBlk_mul, cBlk_frameOf, fBlk_frameOf, wBlk_frameOf] at this
    simpa only [xBlk_zMk, yBlk_zMk, Matrix.mul_one] using this

/-- The block equations at a point $\begin{bmatrix}x\\0\end{bmatrix}$. -/
theorem fix_eqs0 {g : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ}
    (hg : gᵀ * phiR r t * g = phiR r t) (hfix : ∀ z ∈ ZR r t, actR g z = z)
    (x : Matrix (Fin r) (Fin r) ℝ) (hz : zMk x (0 : Matrix (Fin t) (Fin r) ℝ) ∈ ZR r t) :
    ∃ m : Matrix (Fin r) (Fin r) ℝ,
      g.submatrix (e1 r t) (e1 r t) * ((1 / 2 : ℝ) • (1 - x)) +
        g.submatrix (e1 r t) (e3 r t) * ((1 / 2 : ℝ) • (1 + x)) = ((1 / 2 : ℝ) • (1 - x)) * m ∧
      g.submatrix (e2 r t) (e1 r t) * ((1 / 2 : ℝ) • (1 - x)) +
        g.submatrix (e2 r t) (e3 r t) * ((1 / 2 : ℝ) • (1 + x)) = 0 ∧
      g.submatrix (e3 r t) (e1 r t) * ((1 / 2 : ℝ) • (1 - x)) +
        g.submatrix (e3 r t) (e3 r t) * ((1 / 2 : ℝ) • (1 + x)) = ((1 / 2 : ℝ) • (1 + x)) * m := by
  obtain ⟨m, h1, h2, h3⟩ := fix_eqs hg hfix x 0 hz
  simp only [smul_zero, Matrix.mul_zero, add_zero, Matrix.zero_mul] at h1 h2 h3
  exact ⟨m, h1, h2, h3⟩

theorem xiR_zMk_smul_one (a : ℝ) :
    xiR (zMk (a • (1 : Matrix (Fin r) (Fin r) ℝ)) (0 : Matrix (Fin t) (Fin r) ℝ)) = a • 1 := by
  rw [xiR_zMk]
  simp only [transpose_smul, transpose_one, transpose_zero, Matrix.zero_mul, sub_zero]
  module

theorem zMk_smul_one_mem {a : ℝ} (ha : 0 < a) :
    zMk (a • (1 : Matrix (Fin r) (Fin r) ℝ)) (0 : Matrix (Fin t) (Fin r) ℝ) ∈ ZR r t := by
  show (xiR _).PosDef
  rw [xiR_zMk_smul_one, smul_one_eq_diagonal]
  exact PosDef.diagonal fun _ => ha

/-- Block equations at $x = a\cdot 1$, $y = 0$ ($a > 0$). -/
theorem fix_eqs_scalar {g : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ}
    (hg : gᵀ * phiR r t * g = phiR r t) (hfix : ∀ z ∈ ZR r t, actR g z = z) {a : ℝ} (ha : 0 < a) :
    ∃ m : Matrix (Fin r) (Fin r) ℝ,
      ((1 - a) / 2) • g.submatrix (e1 r t) (e1 r t) + ((1 + a) / 2) • g.submatrix (e1 r t) (e3 r t) =
        ((1 - a) / 2) • m ∧
      ((1 - a) / 2) • g.submatrix (e2 r t) (e1 r t) + ((1 + a) / 2) • g.submatrix (e2 r t) (e3 r t) = 0 ∧
      ((1 - a) / 2) • g.submatrix (e3 r t) (e1 r t) + ((1 + a) / 2) • g.submatrix (e3 r t) (e3 r t) =
        ((1 + a) / 2) • m := by
  obtain ⟨m, h1, h2, h3⟩ := fix_eqs0 hg hfix (a • 1) (zMk_smul_one_mem ha)
  have hc : (1 / 2 : ℝ) • (1 - a • (1 : Matrix (Fin r) (Fin r) ℝ)) = ((1 - a) / 2) • 1 := by module
  have hw : (1 / 2 : ℝ) • (1 + a • (1 : Matrix (Fin r) (Fin r) ℝ)) = ((1 + a) / 2) • 1 := by module
  rw [hc, hw] at h1 h2 h3
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul] at h1 h2 h3
  exact ⟨m, h1, h2, h3⟩

theorem phase_a {g : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ}
    (hg : gᵀ * phiR r t * g = phiR r t) (hfix : ∀ z ∈ ZR r t, actR g z = z) :
    g.submatrix (e1 r t) (e3 r t) = 0 ∧ g.submatrix (e2 r t) (e3 r t) = 0 := by
  obtain ⟨m, h1, h2, h3⟩ := fix_eqs_scalar hg hfix (a := 1) one_pos
  norm_num at h1 h2
  exact ⟨h1, h2⟩

theorem e3_ne_e1 (i j : Fin r) : e3 r t i ≠ e1 r t j := fun h => by
  have := congrArg Fin.val h
  simp [e3, e1] at this; have := j.isLt; have := i.isLt; omega

theorem e3_ne_e2 (i : Fin r) (j : Fin t) : e3 r t i ≠ e2 r t j := fun h => by
  have := congrArg Fin.val h
  simp [e3, e2] at this; have := j.isLt; omega

theorem phiR_e3_e3 : (phiR r t).submatrix (e3 r t) (e3 r t) = -1 := by
  ext i j
  simp [phiR, diagonal_apply, signVec, e3, one_apply, Fin.natAdd_inj]
  split_ifs <;> simp

theorem phiR_e3_e1 : (phiR r t).submatrix (e3 r t) (e1 r t) = 0 := by
  ext i j
  simp only [submatrix_apply, Matrix.zero_apply]
  exact diagonal_apply_ne _ (e3_ne_e1 i j)

theorem phiR_e3_e2 : (phiR r t).submatrix (e3 r t) (e2 r t) = 0 := by
  ext i j
  simp only [submatrix_apply, Matrix.zero_apply]
  exact diagonal_apply_ne _ (e3_ne_e2 i j)

theorem orth_col3 {g : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ}
    (hg : gᵀ * phiR r t * g = phiR r t) {s : ℕ} (κ : Fin s → Fin (r + t + r)) :
    (lastCols g)ᵀ * phiR r t * g.submatrix id κ = (phiR r t).submatrix (e3 r t) κ := by
  have : (gᵀ * phiR r t * g).submatrix (e3 r t) κ = (phiR r t).submatrix (e3 r t) κ := by
    rw [hg]
  rw [← this]
  ext i j
  rfl

theorem orth_block3 {g : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ}
    (hg : gᵀ * phiR r t * g = phiR r t) (h13 : g.submatrix (e1 r t) (e3 r t) = 0)
    (h23 : g.submatrix (e2 r t) (e3 r t) = 0) {s : ℕ} (κ : Fin s → Fin (r + t + r)) :
    -((g.submatrix (e3 r t) (e3 r t))ᵀ * g.submatrix (e3 r t) κ) = (phiR r t).submatrix (e3 r t) κ := by
  have h := orth_col3 hg κ
  rw [transpose_phiR_mul_blocks] at h
  have e1' : (lastCols g).submatrix (e1 r t) id = g.submatrix (e1 r t) (e3 r t) := rfl
  have e2' : (lastCols g).submatrix (e2 r t) id = g.submatrix (e2 r t) (e3 r t) := rfl
  have e3' : (lastCols g).submatrix (e3 r t) id = g.submatrix (e3 r t) (e3 r t) := rfl
  have e4 : (g.submatrix id κ).submatrix (e3 r t) id = g.submatrix (e3 r t) κ := rfl
  rw [e1', e2', e3', e4, h13, h23] at h
  simp only [transpose_zero, Matrix.zero_mul, zero_add, zero_sub] at h
  exact h

theorem phase_b {g : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ}
    (hg : gᵀ * phiR r t * g = phiR r t) (h13 : g.submatrix (e1 r t) (e3 r t) = 0)
    (h23 : g.submatrix (e2 r t) (e3 r t) = 0) :
    (g.submatrix (e3 r t) (e3 r t))ᵀ * g.submatrix (e3 r t) (e3 r t) = 1 ∧
    g.submatrix (e3 r t) (e1 r t) = 0 ∧ g.submatrix (e3 r t) (e2 r t) = 0 := by
  have hA := orth_block3 hg h13 h23 (e3 r t)
  have hB := orth_block3 hg h13 h23 (e1 r t)
  have hC := orth_block3 hg h13 h23 (e2 r t)
  rw [phiR_e3_e3] at hA
  rw [phiR_e3_e1] at hB
  rw [phiR_e3_e2] at hC
  have hA' : (g.submatrix (e3 r t) (e3 r t))ᵀ * g.submatrix (e3 r t) (e3 r t) = 1 := by
    simpa using hA
  have hA'' : g.submatrix (e3 r t) (e3 r t) * (g.submatrix (e3 r t) (e3 r t))ᵀ = 1 :=
    mul_eq_one_comm.mp hA'
  refine ⟨hA', ?_, ?_⟩
  · have hB' : (g.submatrix (e3 r t) (e3 r t))ᵀ * g.submatrix (e3 r t) (e1 r t) = 0 := by
      simpa using hB
    calc g.submatrix (e3 r t) (e1 r t)
        = (g.submatrix (e3 r t) (e3 r t) * (g.submatrix (e3 r t) (e3 r t))ᵀ) *
            g.submatrix (e3 r t) (e1 r t) := by rw [hA'', Matrix.one_mul]
      _ = 0 := by rw [Matrix.mul_assoc, hB', Matrix.mul_zero]
  · have hC' : (g.submatrix (e3 r t) (e3 r t))ᵀ * g.submatrix (e3 r t) (e2 r t) = 0 := by
      simpa using hC
    calc g.submatrix (e3 r t) (e2 r t)
        = (g.submatrix (e3 r t) (e3 r t) * (g.submatrix (e3 r t) (e3 r t))ᵀ) *
            g.submatrix (e3 r t) (e2 r t) := by rw [hA'', Matrix.one_mul]
      _ = 0 := by rw [Matrix.mul_assoc, hC', Matrix.mul_zero]

theorem phase_c {g : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ}
    (hg : gᵀ * phiR r t * g = phiR r t) (hfix : ∀ z ∈ ZR r t, actR g z = z)
    (h13 : g.submatrix (e1 r t) (e3 r t) = 0) (h23 : g.submatrix (e2 r t) (e3 r t) = 0)
    (h31 : g.submatrix (e3 r t) (e1 r t) = 0) :
    g.submatrix (e2 r t) (e1 r t) = 0 ∧
      g.submatrix (e1 r t) (e1 r t) = g.submatrix (e3 r t) (e3 r t) := by
  obtain ⟨m, h1, h2, h3⟩ := fix_eqs_scalar hg hfix (a := 1 / 2) (by norm_num)
  rw [h13] at h1
  rw [h23] at h2
  rw [h31] at h3
  norm_num at h1 h2 h3
  exact ⟨h2, h1.trans h3.symm⟩

/-- $D$ commutes with every $x$ with $\begin{bmatrix}x\\0\end{bmatrix}\in Z_{\mathbb R}$, once
$g_{13} = g_{31} = 0$ and $g_{33} = g_{11} = D$. -/
theorem phase_comm {g : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ}
    (hg : gᵀ * phiR r t * g = phiR r t) (hfix : ∀ z ∈ ZR r t, actR g z = z)
    (h13 : g.submatrix (e1 r t) (e3 r t) = 0) (h31 : g.submatrix (e3 r t) (e1 r t) = 0)
    (h33 : g.submatrix (e3 r t) (e3 r t) = g.submatrix (e1 r t) (e1 r t))
    (x : Matrix (Fin r) (Fin r) ℝ) (hz : zMk x (0 : Matrix (Fin t) (Fin r) ℝ) ∈ ZR r t) :
    g.submatrix (e1 r t) (e1 r t) * x = x * g.submatrix (e1 r t) (e1 r t) := by
  obtain ⟨m, h1, -, h3⟩ := fix_eqs0 hg hfix x hz
  rw [h13] at h1
  rw [h31, h33] at h3
  simp only [Matrix.zero_mul, zero_add, add_zero] at h1 h3
  have hcw : (1 / 2 : ℝ) • (1 - x) + (1 / 2 : ℝ) • (1 + x) = 1 := by module
  have hsum := congrArg₂ HAdd.hAdd h1 h3
  rw [← Matrix.mul_add, ← Matrix.add_mul, hcw, Matrix.mul_one, Matrix.one_mul] at hsum
  rw [← hsum] at h1
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul] at h1
  have h2 := smul_right_injective _ (by norm_num : (1 / 2 : ℝ) ≠ 0) h1
  exact (sub_right_inj.mp h2)

theorem comm_offdiag {D : Matrix (Fin r) (Fin r) ℝ}
    (h : ∀ a : Fin r → ℝ, (∀ l, 0 < a l) → D * diagonal a = diagonal a * D) {i j : Fin r}
    (hij : i ≠ j) : D i j = 0 := by
  have hpos : ∀ l, 0 < (fun l : Fin r => if l = i then (2 : ℝ) else 1) l := fun l => by
    simp only; split_ifs <;> norm_num
  have := congrFun (congrFun (h _ hpos) i) j
  simp [mul_diagonal, diagonal_mul, hij, hij.symm] at this
  linarith

/-- The antisymmetric matrix $E_{ij} - E_{ji}$. -/
def antiK (i j : Fin r) : Matrix (Fin r) (Fin r) ℝ := Matrix.single i j 1 - Matrix.single j i 1

theorem comm_antiK {D : Matrix (Fin r) (Fin r) ℝ}
    (h : ∀ i j : Fin r, i ≠ j → D * (1 + antiK i j) = (1 + antiK i j) * D) {i j : Fin r}
    (hij : i ≠ j) : D i i = D j j := by
  have h1 := h i j hij
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, add_right_inj] at h1
  have := congrFun (congrFun h1 i) j
  simp [antiK, Matrix.mul_sub, Matrix.sub_mul, hij, hij.symm] at this
  exact this

theorem scalar_of_comm (hr : 1 ≤ r) {D : Matrix (Fin r) (Fin r) ℝ}
    (hoff : ∀ i j : Fin r, i ≠ j → D i j = 0) (hdiag : ∀ i j : Fin r, i ≠ j → D i i = D j j) :
    ∃ d : ℝ, D = d • 1 := by
  refine ⟨D ⟨0, hr⟩ ⟨0, hr⟩, ?_⟩
  ext a b
  by_cases hab : a = b
  · subst hab
    by_cases h0 : a = ⟨0, hr⟩
    · subst h0; simp
    · simp [hdiag a ⟨0, hr⟩ h0]
  · simp [hab, hoff a b hab]

theorem xiR_zMk_diagonal (a : Fin r → ℝ) :
    xiR (zMk (diagonal a) (0 : Matrix (Fin t) (Fin r) ℝ)) = diagonal a := by
  rw [xiR_zMk]
  simp only [diagonal_transpose, transpose_zero, Matrix.zero_mul, sub_zero]
  module

theorem zMk_diagonal_mem {a : Fin r → ℝ} (ha : ∀ l, 0 < a l) :
    zMk (diagonal a) (0 : Matrix (Fin t) (Fin r) ℝ) ∈ ZR r t := by
  show (xiR _).PosDef
  rw [xiR_zMk_diagonal]
  exact PosDef.diagonal ha

theorem antiK_transpose (i j : Fin r) : (antiK i j)ᵀ = -antiK i j := by
  simp [antiK, transpose_single]

theorem zMk_antiK_mem (i j : Fin r) :
    zMk (1 + antiK i j) (0 : Matrix (Fin t) (Fin r) ℝ) ∈ ZR r t := by
  show (xiR _).PosDef
  have : xiR (zMk (1 + antiK i j) (0 : Matrix (Fin t) (Fin r) ℝ)) = 1 := by
    rw [xiR_zMk]
    simp only [transpose_add, transpose_one, antiK_transpose, transpose_zero, Matrix.zero_mul,
      sub_zero]
    module
  rw [this]
  exact PosDef.one

/-- $D = g_{11}$ is a scalar matrix. -/
theorem phase_scalar {g : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ} (hr : 1 ≤ r)
    (hg : gᵀ * phiR r t * g = phiR r t) (hfix : ∀ z ∈ ZR r t, actR g z = z)
    (h13 : g.submatrix (e1 r t) (e3 r t) = 0) (h31 : g.submatrix (e3 r t) (e1 r t) = 0)
    (h33 : g.submatrix (e3 r t) (e3 r t) = g.submatrix (e1 r t) (e1 r t)) :
    ∃ d : ℝ, g.submatrix (e1 r t) (e1 r t) = d • 1 := by
  have hcomm := phase_comm hg hfix h13 h31 h33
  refine scalar_of_comm hr (fun i j hij => ?_) (fun i j hij => ?_)
  · exact comm_offdiag (fun a ha => hcomm (diagonal a) (zMk_diagonal_mem ha)) hij
  · refine comm_antiK (fun i j hij => ?_) hij
    exact hcomm _ (zMk_antiK_mem i j)

/-- The test points $\begin{bmatrix}1\\ \tfrac12E_{kj}\end{bmatrix}$ lie in $Z_{\mathbb R}$. -/
theorem zMk_one_single_mem (k : Fin t) (j : Fin r) :
    zMk (1 : Matrix (Fin r) (Fin r) ℝ) (Matrix.single k j (1 / 2 : ℝ)) ∈ ZR r t := by
  show (xiR _).PosDef
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v hv => ?_⟩
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    exact xiR_transpose _
  · have hyv : ∀ v : Fin r → ℝ, v ⬝ᵥ (((Matrix.single k j (1 / 2 : ℝ))ᵀ * Matrix.single k j (1 / 2 : ℝ)) *ᵥ v) =
        ((1 / 2) * v j) ^ 2 := by
      intro v
      rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, Matrix.single_mulVec]
      show (Pi.single k ((1 / 2) * v j) : Fin t → ℝ) ⬝ᵥ Pi.single k ((1 / 2) * v j) = _
      rw [single_dotProduct]
      simp
      ring
    have hq : v ⬝ᵥ (xiR (zMk (1 : Matrix (Fin r) (Fin r) ℝ) (Matrix.single k j (1 / 2 : ℝ))) *ᵥ v) =
        (1 / 2) * (v ⬝ᵥ v + v ⬝ᵥ v - ((1 / 2) * v j) ^ 2) := by
      rw [xiR_zMk, Matrix.smul_mulVec, dotProduct_smul, Matrix.sub_mulVec, Matrix.add_mulVec,
        transpose_one, Matrix.one_mulVec, dotProduct_sub, dotProduct_add, hyv]
      simp
    simp only [star_trivial]
    rw [hq]
    have hP : 0 < v ⬝ᵥ v :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
        (fun h => hv (dotProduct_self_eq_zero.mp h.symm))
    have hj : v j * v j ≤ v ⬝ᵥ v :=
      Finset.single_le_sum (f := fun i => v i * v i) (fun i _ => mul_self_nonneg _) (Finset.mem_univ j)
    nlinarith

theorem phase_g {g : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ} (hr : 1 ≤ r)
    (hg : gᵀ * phiR r t * g = phiR r t) (hfix : ∀ z ∈ ZR r t, actR g z = z)
    (h13 : g.submatrix (e1 r t) (e3 r t) = 0) (h23 : g.submatrix (e2 r t) (e3 r t) = 0)
    (h32 : g.submatrix (e3 r t) (e2 r t) = 0) {d : ℝ}
    (h33 : g.submatrix (e3 r t) (e3 r t) = d • 1) :
    g.submatrix (e1 r t) (e2 r t) = 0 ∧ g.submatrix (e2 r t) (e2 r t) = d • 1 := by
  have key : ∀ (k : Fin t) (j : Fin r), ∃ m : Matrix (Fin r) (Fin r) ℝ,
      m = d • 1 ∧
      g.submatrix (e1 r t) (e2 r t) * ((Real.sqrt 2)⁻¹ • Matrix.single k j (1 / 2 : ℝ)) = 0 ∧
      g.submatrix (e2 r t) (e2 r t) * ((Real.sqrt 2)⁻¹ • Matrix.single k j (1 / 2 : ℝ)) =
        ((Real.sqrt 2)⁻¹ • Matrix.single k j (1 / 2 : ℝ)) * m := by
    intro k j
    obtain ⟨m, h1, h2, h3⟩ := fix_eqs hg hfix 1 (Matrix.single k j (1 / 2 : ℝ)) (zMk_one_single_mem k j)
    have hc : (1 / 2 : ℝ) • (1 - (1 : Matrix (Fin r) (Fin r) ℝ)) = 0 := by simp
    have hw : (1 / 2 : ℝ) • (1 + (1 : Matrix (Fin r) (Fin r) ℝ)) = 1 := by module
    rw [hc, hw] at h1 h2 h3
    rw [h13] at h1
    rw [h23] at h2
    rw [h32, h33] at h3
    simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, Matrix.mul_one, Matrix.one_mul]
      at h1 h2 h3
    refine ⟨m, ?_, h1, h2⟩
    rw [← h3]
  have hs : (Real.sqrt 2)⁻¹ ≠ 0 := by positivity
  constructor
  · ext a k
    obtain ⟨j⟩ : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    obtain ⟨m, -, h1, -⟩ := key k j
    have := congrFun (congrFun h1 a) j
    simp [Matrix.mul_smul] at this
    simpa [hs] using this
  · ext a k
    obtain ⟨j⟩ : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    obtain ⟨m, hm, -, h2⟩ := key k j
    have := congrFun (congrFun h2 a) j
    subst hm
    simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.single_apply] at this
    have hc : ((Real.sqrt 2)⁻¹ * 2⁻¹ : ℝ) ≠ 0 := by positivity
    by_cases hka : k = a
    · subst hka
      rw [if_pos rfl] at this
      simpa [one_apply] using mul_right_cancel₀ hc this
    · rw [if_neg hka] at this
      have h0 := (mul_eq_zero.mp this).resolve_right hc
      simp [one_apply, Ne.symm hka, h0]

theorem e1_ne_e2 (i : Fin r) (k : Fin t) : e1 r t i ≠ e2 r t k := fun h => by
  have := congrArg Fin.val h
  simp [e1, e2] at this; have := i.isLt; omega

theorem e1_ne_e3 (i j : Fin r) : e1 r t i ≠ e3 r t j := fun h => by
  have := congrArg Fin.val h
  simp [e1, e3] at this; have := i.isLt; omega

theorem e2_ne_e3 (k : Fin t) (j : Fin r) : e2 r t k ≠ e3 r t j := fun h => by
  have := congrArg Fin.val h
  simp [e2, e3] at this; have := k.isLt; omega

theorem e1_injective : Function.Injective (e1 r t) := fun a b h => by
  have := congrArg Fin.val h
  simp [e1] at this; exact Fin.ext this

theorem e2_injective : Function.Injective (e2 r t) := fun a b h => by
  have := congrArg Fin.val h
  simp [e2] at this; exact Fin.ext this

theorem e3_injective : Function.Injective (e3 r t) := fun a b h => by
  have := congrArg Fin.val h
  simp [e3] at this; exact Fin.ext this

theorem smul_one_submatrix_same {s : ℕ} (d : ℝ) {e : Fin s → Fin (r + t + r)} (he : Function.Injective e) :
    (d • (1 : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ)).submatrix e e = d • 1 := by
  ext a b
  simp [one_apply, he.eq_iff]

theorem smul_one_submatrix_ne {s s' : ℕ} (d : ℝ) {e : Fin s → Fin (r + t + r)}
    {e' : Fin s' → Fin (r + t + r)} (he : ∀ i j, e i ≠ e' j) :
    (d • (1 : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ)).submatrix e e' = 0 := by
  ext a b
  simp [one_apply_ne (he a b)]

theorem ext_blocks {g h : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ}
    (h11 : g.submatrix (e1 r t) (e1 r t) = h.submatrix (e1 r t) (e1 r t))
    (h12 : g.submatrix (e1 r t) (e2 r t) = h.submatrix (e1 r t) (e2 r t))
    (h13 : g.submatrix (e1 r t) (e3 r t) = h.submatrix (e1 r t) (e3 r t))
    (h21 : g.submatrix (e2 r t) (e1 r t) = h.submatrix (e2 r t) (e1 r t))
    (h22 : g.submatrix (e2 r t) (e2 r t) = h.submatrix (e2 r t) (e2 r t))
    (h23 : g.submatrix (e2 r t) (e3 r t) = h.submatrix (e2 r t) (e3 r t))
    (h31 : g.submatrix (e3 r t) (e1 r t) = h.submatrix (e3 r t) (e1 r t))
    (h32 : g.submatrix (e3 r t) (e2 r t) = h.submatrix (e3 r t) (e2 r t))
    (h33 : g.submatrix (e3 r t) (e3 r t) = h.submatrix (e3 r t) (e3 r t)) : g = h := by
  ext i j
  refine Fin.addCases (fun a => Fin.addCases (fun a1 => ?_) (fun b => ?_) a) (fun c => ?_) i <;>
  refine Fin.addCases (fun a' => Fin.addCases (fun a1' => ?_) (fun b' => ?_) a') (fun c' => ?_) j
  all_goals first
    | exact congrFun (congrFun h11 _) _
    | exact congrFun (congrFun h12 _) _
    | exact congrFun (congrFun h13 _) _
    | exact congrFun (congrFun h21 _) _
    | exact congrFun (congrFun h22 _) _
    | exact congrFun (congrFun h23 _) _
    | exact congrFun (congrFun h31 _) _
    | exact congrFun (congrFun h32 _) _
    | exact congrFun (congrFun h33 _) _

/-- **Lemma A1 at a real place** (Hanke thesis, p. 21; Hanke 2005, Lemma A1). Let
$\varphi_v = \mathrm{diag}[1_q, -1_r]$, $q = r + t$, $r \ge 1$, $n = q + r$, and let
$O(\varphi_v) = \{g \in GL_n(\mathbb R) : {}^tg\,\varphi_v\,g = \varphi_v\}$ act on the symmetric space
$Z_{\mathbb R}$ (`actR`). Then
$$\{g \in O(\varphi_v) : gz = z\ \text{for all } z \in Z_{\mathbb R}\} = \{\pm 1_n\}.$$
This is stated for matrices $g$ with ${}^tg\varphi_vg = \varphi_v$, so it holds a fortiori for $SO(\varphi_v)$:
for $n$ odd, $-1_n \notin SO(\varphi_v)$ and the kernel of the action on $SO(\varphi_v)$ is $\{1_n\}$; for $n$
even it is $\{\pm 1_n\}$. -/
@[kb "hanke2005crelle" "Lemma A1, p. 21 (real places)"]
theorem lemmaA1_real {r t : ℕ} (hr : 1 ≤ r) {g : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ}
    (hg : gᵀ * phiR r t * g = phiR r t) :
    (∀ z ∈ ZR r t, actR g z = z) ↔ g = 1 ∨ g = -1 := by
  constructor
  · intro hfix
    obtain ⟨h13, h23⟩ := phase_a hg hfix
    obtain ⟨hGG, h31, h32⟩ := phase_b hg h13 h23
    obtain ⟨h21, h11⟩ := phase_c hg hfix h13 h23 h31
    obtain ⟨d, hd⟩ := phase_scalar hr hg hfix h13 h31 h11.symm
    have h33 : g.submatrix (e3 r t) (e3 r t) = d • 1 := h11.symm.trans hd
    obtain ⟨h12, h22⟩ := phase_g hr hg hfix h13 h23 h32 h33
    have hdd : d * d = 1 := by
      rw [h33] at hGG
      have := congrFun (congrFun hGG ⟨0, hr⟩) ⟨0, hr⟩
      simpa [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul] using this
    have hgd : g = d • 1 := by
      refine ext_blocks ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rw [hd, smul_one_submatrix_same _ e1_injective]
      · rw [h12, smul_one_submatrix_ne _ e1_ne_e2]
      · rw [h13, smul_one_submatrix_ne _ e1_ne_e3]
      · rw [h21, smul_one_submatrix_ne _ (fun i j => (e1_ne_e2 j i).symm)]
      · rw [h22, smul_one_submatrix_same _ e2_injective]
      · rw [h23, smul_one_submatrix_ne _ e2_ne_e3]
      · rw [h31, smul_one_submatrix_ne _ (fun i j => (e1_ne_e3 j i).symm)]
      · rw [h32, smul_one_submatrix_ne _ (fun i j => (e2_ne_e3 j i).symm)]
      · rw [h33, smul_one_submatrix_same _ e3_injective]
    rcases mul_self_eq_one_iff.mp hdd with h | h
    · left; rw [hgd, h, one_smul]
    · right; rw [hgd, h, neg_smul, one_smul]
  · rintro (rfl | rfl) z _
    · have hU : IsUnit (1 : Matrix (Fin r) (Fin r) ℝ).det := by simp
      rw [actR, Matrix.one_mul]
      simpa using zOf_frameOf z (m := 1) hU
    · have hU : IsUnit (-1 : Matrix (Fin r) (Fin r) ℝ).det :=
        (Matrix.isUnit_iff_isUnit_det _).mp isUnit_one.neg
      rw [actR, show (-1 : Matrix (Fin (r + t + r)) (Fin (r + t + r)) ℝ) * frameOf z 1 =
        frameOf z 1 * (-1 : Matrix (Fin r) (Fin r) ℝ) by simp, zOf_mul_right _ hU]
      simpa using zOf_frameOf z (m := 1) (by simp)

end QuadFormsKB.Hanke2005.ArchReal
