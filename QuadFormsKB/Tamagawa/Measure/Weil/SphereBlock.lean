import QuadFormsKB.Tamagawa.Measure.Weil.ReflectionSection
import QuadFormsKB.Tamagawa.SplitForm

/-!
# Local algebra for the sphere $\{q = q(\xi)\}$: the stabilizer of $\xi$ in block form and a two-branch section


**Generic (any field $R$).** $H_0\in M_{k+1}(R)$ symmetric, $P\in GL_{k+1}(R)$ with
$$P^{\mathsf T}H_0P = \mathrm{diag}(a, H')\qquad(\texttt{cornerMat}\ a\ H',\ a\ne0),$$
so the first column $\xi_P = Pe_0$ is anisotropic and the other columns span $\xi_P^\perp$, with Gram matrix $H'$.

* **`conjBlock P h`** $= P\,\mathrm{diag}(1, h)\,P^{-1}$: for $h^{\mathsf T}H'h = H'$ it preserves $H_0$ (`conjBlock_orth`), has
  $\det = \det h$ (`det_conjBlock`), fixes $\xi_P$ (`conjBlock_mulVec`), and is multiplicative (`conjBlock_mul`).
* **`exists_conjBlock_eq`** (the stabilizer): every $g$ with $g^{\mathsf T}H_0g = H_0$ and $g\xi_P = \xi_P$ is
  $\mathrm{conjBlock}\,P\,h$ for $h = $ `blockOf P g` with $h^{\mathsf T}H'h = H'$, $\det h = \det g$.
* **The two-branch section** `secP D b x` $=\tau_{x+x_0}\tau_{x_0}$ if `b x`, else $\tau_{x-x_0}\tau_w$ (the reflections):
  $s(x)x_0 = x$ whenever the chosen branch has $q(x\pm x_0)\ne0$ (`secP_mulVec`). `sphereSec` is the case
  $b(x) \Leftrightarrow q(x + x_0)\ne0$; at a finite place we choose the branch by absolute values, which makes the section
  integral at almost all places.
-/

open Matrix
open scoped Matrix

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {R : Type*} [Field R] {k : ℕ}

/-! ### The two branches of the reflection section -/

section Section

variable {n : ℕ} (H : Matrix (Fin n) (Fin n) R)

/-- First branch: $\tau_{x+x_0}\tau_{x_0}x_0 = x$ when $q(x) = q(x_0)$ and $q(x + x_0)\ne0$. -/
theorem refl_add_mulVec (hH : Hᵀ = H) (h2 : (2 : R) ≠ 0) {x₀ x : Fin n → R} (hx₀ : qH H x₀ ≠ 0)
    (hx : qH H x = qH H x₀) (h : qH H (x + x₀) ≠ 0) : (refl H (x + x₀) * refl H x₀) *ᵥ x₀ = x := by
  rw [← mulVec_mulVec, refl_self hH hx₀, mulVec_neg, refl_mulVec hH]
  have hq : qH H (x + x₀) = 2 * bH H (x + x₀) x₀ := by
    rw [qH_add hH, bH_add_left, ← qH_eq_bH, hx]; ring
  have hB0 : bH H (x + x₀) x₀ ≠ 0 := fun h0 => h (by rw [hq, h0, mul_zero])
  rw [hq, div_self (mul_ne_zero h2 hB0), one_smul]
  abel

/-- Second branch: $\tau_{x-x_0}\tau_wx_0 = x$ when $q(x) = q(x_0)$, $B(w, x_0) = 0$ and $q(x - x_0)\ne0$. -/
theorem refl_sub_mulVec (hH : Hᵀ = H) {x₀ x w : Fin n → R} (horth : bH H w x₀ = 0)
    (hx : qH H x = qH H x₀) (h : qH H (x - x₀) ≠ 0) : (refl H (x - x₀) * refl H w) *ᵥ x₀ = x := by
  rw [← mulVec_mulVec, refl_of_orth hH horth, refl_mulVec hH]
  have hq : qH H (x - x₀) = -2 * bH H (x - x₀) x₀ := by
    rw [qH_sub hH, bH_sub_left, ← qH_eq_bH, hx]; ring
  have hB0 : bH H (x - x₀) x₀ ≠ 0 := fun h0 => h (by rw [hq, h0, mul_zero])
  have h2 : (-2 : R) ≠ 0 := fun h0 => h (by rw [hq, h0, zero_mul])
  rw [hq, show 2 * bH H (x - x₀) x₀ / (-2 * bH H (x - x₀) x₀) = -1 by
    rw [div_eq_iff (mul_ne_zero h2 hB0)]; ring]
  simp

/-- $q(x + x_0) + q(x - x_0) = 4q(x_0)$ on the quadric $q(x) = q(x_0)$. -/
theorem qH_add_add_qH_sub (hH : Hᵀ = H) {x₀ x : Fin n → R} (hx : qH H x = qH H x₀) :
    qH H (x + x₀) + qH H (x - x₀) = 4 * qH H x₀ := by
  rw [qH_add hH, qH_sub hH, hx]; ring

open Classical in
/-- **The two-branch section** $s(x) = \tau_{x+x_0}\tau_{x_0}$ if $b(x)$, else $\tau_{x-x_0}\tau_w$. -/
def secP (D : SphereData H) (b : (Fin n → R) → Prop) (x : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  if b x then refl H (x + D.x₀) * refl H D.x₀ else refl H (x - D.x₀) * refl H D.w

/-- **$s(x)x_0 = x$** on the quadric, when the chosen branch is anisotropic. -/
theorem secP_mulVec (hH : Hᵀ = H) (h2 : (2 : R) ≠ 0) (D : SphereData H) (b : (Fin n → R) → Prop)
    {x : Fin n → R} (hx : qH H x = qH H D.x₀) (h1 : b x → qH H (x + D.x₀) ≠ 0)
    (h1' : ¬ b x → qH H (x - D.x₀) ≠ 0) : secP H D b x *ᵥ D.x₀ = x := by
  classical
  unfold secP
  split_ifs with hb
  · exact refl_add_mulVec H hH h2 D.hx₀ hx (h1 hb)
  · exact refl_sub_mulVec H hH D.horth hx (h1' hb)

/-- Two reflections preserve $H$ and have determinant $1$. -/
theorem refl_mul_refl_mem (hH : Hᵀ = H) {u v : Fin n → R} (hu : qH H u ≠ 0) (hv : qH H v ≠ 0) :
    (refl H u * refl H v)ᵀ * H * (refl H u * refl H v) = H ∧ (refl H u * refl H v).det = 1 := by
  refine ⟨?_, ?_⟩
  · rw [transpose_mul, show (refl H v)ᵀ * (refl H u)ᵀ * H * (refl H u * refl H v) =
        (refl H v)ᵀ * ((refl H u)ᵀ * H * refl H u) * refl H v by simp only [Matrix.mul_assoc],
      transpose_refl_mul_mul_refl hH hu, transpose_refl_mul_mul_refl hH hv]
  · rw [det_mul, det_refl hu, det_refl hv]; ring

/-- **$s(x)\in SO(H)$** when the chosen branch is anisotropic. -/
theorem secP_mem (hH : Hᵀ = H) (D : SphereData H) (b : (Fin n → R) → Prop) {x : Fin n → R}
    (h1 : b x → qH H (x + D.x₀) ≠ 0) (h1' : ¬ b x → qH H (x - D.x₀) ≠ 0) :
    (secP H D b x)ᵀ * H * secP H D b x = H ∧ (secP H D b x).det = 1 := by
  classical
  unfold secP
  split_ifs with hb
  · exact refl_mul_refl_mem H hH (h1 hb) D.hx₀
  · exact refl_mul_refl_mem H hH (h1' hb) D.hw

/-- Reflections are involutions: $\tau_u\tau_u = 1$. -/
theorem refl_mul_refl_self (hH : Hᵀ = H) {u : Fin n → R} (hu : qH H u ≠ 0) : refl H u * refl H u = 1 := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [← mulVec_mulVec, one_mulVec, refl_mulVec hH, refl_mulVec hH, bH_sub_right, bH_smul_right,
    ← qH_eq_bH]
  set a := 2 * bH H u (Pi.single j 1) / qH H u
  rw [show 2 * (bH H u (Pi.single j 1) - a * qH H u) / qH H u = -a by
    simp only [a]; field_simp; ring]
  rw [neg_smul, sub_neg_eq_add, sub_add_cancel]

open Classical in
/-- The inverse of the two-branch section: $\tau_{x_0}\tau_{x+x_0}$ if `b x`, else $\tau_w\tau_{x-x_0}$. -/
def secPInv (D : SphereData H) (b : (Fin n → R) → Prop) (x : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  if b x then refl H D.x₀ * refl H (x + D.x₀) else refl H D.w * refl H (x - D.x₀)

theorem secP_mul_secPInv (hH : Hᵀ = H) (D : SphereData H) (b : (Fin n → R) → Prop) {x : Fin n → R}
    (h1 : b x → qH H (x + D.x₀) ≠ 0) (h1' : ¬ b x → qH H (x - D.x₀) ≠ 0) :
    secP H D b x * secPInv H D b x = 1 ∧ secPInv H D b x * secP H D b x = 1 := by
  classical
  unfold secP secPInv
  split_ifs with hb
  · constructor
    · rw [show refl H (x + D.x₀) * refl H D.x₀ * (refl H D.x₀ * refl H (x + D.x₀)) =
        refl H (x + D.x₀) * (refl H D.x₀ * refl H D.x₀) * refl H (x + D.x₀) by simp only [Matrix.mul_assoc],
        refl_mul_refl_self H hH D.hx₀, Matrix.mul_one, refl_mul_refl_self H hH (h1 hb)]
    · rw [show refl H D.x₀ * refl H (x + D.x₀) * (refl H (x + D.x₀) * refl H D.x₀) =
        refl H D.x₀ * (refl H (x + D.x₀) * refl H (x + D.x₀)) * refl H D.x₀ by simp only [Matrix.mul_assoc],
        refl_mul_refl_self H hH (h1 hb), Matrix.mul_one, refl_mul_refl_self H hH D.hx₀]
  · constructor
    · rw [show refl H (x - D.x₀) * refl H D.w * (refl H D.w * refl H (x - D.x₀)) =
        refl H (x - D.x₀) * (refl H D.w * refl H D.w) * refl H (x - D.x₀) by simp only [Matrix.mul_assoc],
        refl_mul_refl_self H hH D.hw, Matrix.mul_one, refl_mul_refl_self H hH (h1' hb)]
    · rw [show refl H D.w * refl H (x - D.x₀) * (refl H (x - D.x₀) * refl H D.w) =
        refl H D.w * (refl H (x - D.x₀) * refl H (x - D.x₀)) * refl H D.w by simp only [Matrix.mul_assoc],
        refl_mul_refl_self H hH (h1' hb), Matrix.mul_one, refl_mul_refl_self H hH D.hw]

/-- **The section as an invertible matrix** (when the chosen branch is anisotropic). -/
def secGL (hH : Hᵀ = H) (D : SphereData H) (b : (Fin n → R) → Prop) (x : Fin n → R)
    (h1 : b x → qH H (x + D.x₀) ≠ 0) (h1' : ¬ b x → qH H (x - D.x₀) ≠ 0) : GL (Fin n) R :=
  ⟨secP H D b x, secPInv H D b x, (secP_mul_secPInv H hH D b h1 h1').1, (secP_mul_secPInv H hH D b h1 h1').2⟩

@[simp] theorem secGL_val (hH : Hᵀ = H) (D : SphereData H) (b : (Fin n → R) → Prop) (x : Fin n → R)
    (h1 : b x → qH H (x + D.x₀) ≠ 0) (h1' : ¬ b x → qH H (x - D.x₀) ≠ 0) :
    (secGL H hH D b x h1 h1' : Matrix (Fin n) (Fin n) R) = secP H D b x := rfl

@[simp] theorem secGL_inv_val (hH : Hᵀ = H) (D : SphereData H) (b : (Fin n → R) → Prop) (x : Fin n → R)
    (h1 : b x → qH H (x + D.x₀) ≠ 0) (h1' : ¬ b x → qH H (x - D.x₀) ≠ 0) :
    (((secGL H hH D b x h1 h1')⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = secPInv H D b x := rfl

/-- On the quadric, the first branch ($q(x + x_0)\ne0$) is admissible. -/
theorem branch_ne (hH : Hᵀ = H) (h2 : (2 : R) ≠ 0) (D : SphereData H) {x : Fin n → R}
    (hx : qH H x = qH H D.x₀) : ¬ qH H (x + D.x₀) ≠ 0 → qH H (x - D.x₀) ≠ 0 := fun h => by
  push Not at h
  exact qH_sub_ne_zero (H := H) hH h2 D hx h

end Section

/-! ### Conjugated block matrices -/

section Block

theorem cornerMat_submatrix_succ (c : R) (A : Matrix (Fin k) (Fin k) R) :
    (cornerMat c A).submatrix Fin.succ Fin.succ = A := by
  ext i j; simp

variable (P : Matrix (Fin (k + 1)) (Fin (k + 1)) R)

/-- **The conjugated block** $P\,\mathrm{diag}(1, h)\,P^{-1}$. -/
def conjBlock (h : Matrix (Fin k) (Fin k) R) : Matrix (Fin (k + 1)) (Fin (k + 1)) R :=
  P * cornerMat 1 h * P⁻¹

/-- **The block of $g$**: the lower right $k\times k$ block of $P^{-1}gP$. -/
def blockOf (g : Matrix (Fin (k + 1)) (Fin (k + 1)) R) : Matrix (Fin k) (Fin k) R :=
  (P⁻¹ * g * P).submatrix Fin.succ Fin.succ

variable {P} (hP : IsUnit P.det)

include hP in
theorem conjBlock_mul (h h' : Matrix (Fin k) (Fin k) R) :
    conjBlock P (h * h') = conjBlock P h * conjBlock P h' := by
  unfold conjBlock
  have : P⁻¹ * P = 1 := nonsing_inv_mul P hP
  rw [show P * cornerMat 1 h * P⁻¹ * (P * cornerMat 1 h' * P⁻¹) =
      P * cornerMat 1 h * (P⁻¹ * P) * cornerMat 1 h' * P⁻¹ by simp only [Matrix.mul_assoc], this,
    Matrix.mul_one, Matrix.mul_assoc P (cornerMat 1 h), cornerMat_mul, one_mul]

include hP in
theorem conjBlock_one : conjBlock P (1 : Matrix (Fin k) (Fin k) R) = 1 := by
  unfold conjBlock
  rw [cornerMat_one, Matrix.mul_one, mul_nonsing_inv P hP]

include hP in
theorem det_conjBlock (h : Matrix (Fin k) (Fin k) R) : (conjBlock P h).det = h.det := by
  have h0 : P.det ≠ 0 := hP.ne_zero
  unfold conjBlock
  rw [det_mul, det_mul, det_cornerMat, one_mul, det_nonsing_inv, Ring.inverse_eq_inv']
  field_simp

/-- $e_0 = (1, 0, \dots, 0)$. -/
abbrev e0 : Fin (k + 1) → R := Pi.single 0 1

theorem cornerMat_one_mulVec_e0 (h : Matrix (Fin k) (Fin k) R) : cornerMat 1 h *ᵥ (e0 : Fin (k + 1) → R) = e0 := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [mulVec, dotProduct, Pi.single_apply]

include hP in
theorem conjBlock_mulVec (h : Matrix (Fin k) (Fin k) R) : conjBlock P h *ᵥ (P *ᵥ e0) = P *ᵥ e0 := by
  unfold conjBlock
  rw [mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul P hP, Matrix.mul_one, ← mulVec_mulVec,
    cornerMat_one_mulVec_e0]

variable {H₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) R} {H' : Matrix (Fin k) (Fin k) R} {a : R}

include hP in
/-- **$\mathrm{conjBlock}\,P\,h$ preserves $H_0$** when $h$ preserves $H'$ and $P^{\mathsf T}H_0P = \mathrm{diag}(a, H')$. -/
theorem conjBlock_orth (hPH : Pᵀ * H₀ * P = cornerMat a H') {h : Matrix (Fin k) (Fin k) R}
    (hh : hᵀ * H' * h = H') : (conjBlock P h)ᵀ * H₀ * conjBlock P h = H₀ := by
  have hPt : IsUnit Pᵀ.det := by rwa [det_transpose]
  have hH₀ : H₀ = (P⁻¹)ᵀ * cornerMat a H' * P⁻¹ := by
    rw [← hPH, transpose_nonsing_inv]
    simp only [← Matrix.mul_assoc]
    rw [nonsing_inv_mul _ hPt, Matrix.one_mul, Matrix.mul_assoc, mul_nonsing_inv _ hP, Matrix.mul_one]
  have hc : (cornerMat 1 h)ᵀ * cornerMat a H' * cornerMat 1 h = cornerMat a H' := by
    rw [cornerMat_transpose, cornerMat_mul, cornerMat_mul, hh]; simp
  unfold conjBlock
  rw [transpose_mul, transpose_mul]
  calc (P⁻¹)ᵀ * ((cornerMat 1 h)ᵀ * Pᵀ) * H₀ * (P * cornerMat 1 h * P⁻¹)
      = (P⁻¹)ᵀ * ((cornerMat 1 h)ᵀ * (Pᵀ * H₀ * P) * cornerMat 1 h) * P⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = H₀ := by rw [hPH, hc, hH₀]

include hP in
/-- **The stabilizer of $\xi_P = Pe_0$**: an isometry $g$ of $H_0$ fixing $Pe_0$ is $\mathrm{conjBlock}\,P\,h$ with
$h = $ `blockOf P g` an isometry of $H'$ and $\det h = \det g$ ($a\ne0$). -/
theorem exists_conjBlock_eq (ha : a ≠ 0) (hPH : Pᵀ * H₀ * P = cornerMat a H')
    {g : Matrix (Fin (k + 1)) (Fin (k + 1)) R} (hg : gᵀ * H₀ * g = H₀) (hgξ : g *ᵥ (P *ᵥ e0) = P *ᵥ e0) :
    conjBlock P (blockOf P g) = g ∧ (blockOf P g)ᵀ * H' * blockOf P g = H' ∧ (blockOf P g).det = g.det := by
  set M := P⁻¹ * g * P with hM
  have hMe : M *ᵥ e0 = e0 := by
    rw [hM, ← mulVec_mulVec, ← mulVec_mulVec, hgξ, mulVec_mulVec, nonsing_inv_mul P hP, one_mulVec]
  have hMC : Mᵀ * cornerMat a H' * M = cornerMat a H' := by
    have hPt : IsUnit Pᵀ.det := by rwa [det_transpose]
    have e1 : (P⁻¹)ᵀ * Pᵀ = 1 := by rw [← transpose_mul, mul_nonsing_inv P hP, transpose_one]
    have e2 : P * P⁻¹ = 1 := mul_nonsing_inv P hP
    rw [← hPH]
    simp only [hM, transpose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (P⁻¹)ᵀ Pᵀ, e1, Matrix.one_mul, ← Matrix.mul_assoc P P⁻¹, e2, Matrix.one_mul,
      ← Matrix.mul_assoc gᵀ, ← Matrix.mul_assoc (gᵀ * H₀), hg]
  -- column 0 of `M` is `e₀`
  have hcol : ∀ i, M i 0 = if i = 0 then 1 else 0 := by
    intro i
    have := congrFun hMe i
    simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] at this
    rw [this]
  -- row 0 of `M` is `e₀ᵀ`
  have hrow : ∀ j : Fin k, M 0 j.succ = 0 := by
    intro j
    have := congrArg (fun X => X 0 j.succ) hMC
    simp only [mul_apply, transpose_apply] at this
    have hs : ∀ l, (∑ i, M i 0 * cornerMat a H' i l) = if l = 0 then a else 0 := by
      intro l
      simp only [hcol, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      refine Fin.cases ?_ (fun l => ?_) l <;> simp
    simp only [hs, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, cornerMat_zero_succ] at this
    exact (mul_eq_zero.mp this).resolve_left ha
  have hMeq : M = cornerMat 1 (M.submatrix Fin.succ Fin.succ) := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [hcol]
    · simp [hrow]
    · simp [hcol, Fin.succ_ne_zero]
    · simp
  refine ⟨?_, ?_, ?_⟩
  · unfold conjBlock blockOf
    rw [← hM, ← hMeq, hM]
    simp only [← Matrix.mul_assoc]
    rw [mul_nonsing_inv P hP, Matrix.one_mul, Matrix.mul_assoc, mul_nonsing_inv P hP, Matrix.mul_one]
  · have h1 := hMC
    rw [hMeq, cornerMat_transpose, cornerMat_mul, cornerMat_mul] at h1
    have := congrArg (fun X => X.submatrix Fin.succ Fin.succ) h1
    simp only [cornerMat_submatrix_succ] at this
    simpa [blockOf, ← hM] using this
  · have h1 : M.det = g.det := by
      have h0 : P.det ≠ 0 := hP.ne_zero
      rw [hM, det_mul, det_mul, det_nonsing_inv, Ring.inverse_eq_inv']
      field_simp
    rw [← h1]
    conv_rhs => rw [hMeq]
    rw [det_cornerMat, one_mul]
    rfl

end Block

end

end QuadFormsKB.Tamagawa.Measure.Weil
