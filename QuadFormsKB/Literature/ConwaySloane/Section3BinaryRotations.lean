/-
# The rotations of a binary quadratic space and their square roots

Helper for the Estes–Pall theorem, "only if" direction (Conway–Sloane, Ch. 15, §3.5, p. 366;
`Section3EstesPallOnlyIf.lean`).

**Setting.** $V = K^2$ ($K$ a field of characteristic $0$, an $F$-algebra for a number field $F$) with a quadratic form
$Q$ whose Hessian (over $K$) is $H = \begin{pmatrix} h_0 & h_1 \\ h_1 & h_2\end{pmatrix}$, so
$B(x, y) = x^{\mathsf T}Hy$ and $B(x, x) = 2Q(x)$. Put
$$J = \begin{pmatrix} -h_1 & -h_2 \\ h_0 & h_1 \end{pmatrix}, \qquad
  M(s, t) = s\cdot 1 + t\cdot J \quad (s, t \in K).$$
(For $Q = [a, b, c] = ax^2 + bxy + cy^2$ this is $J = \begin{pmatrix} -b & -2c \\ 2a & b\end{pmatrix}$, $J^2 = D$ with
$D = b^2 - 4ac = -\det H$: the matrices $M(s, t)$ form the quadratic algebra $K[\sqrt D]$, the even Clifford algebra of
$V$.)

**Proves** (all for $\det H \ne 0$)
* the algebra: $\det M(s, t) = s^2 + t^2\det H$, $M(s,t)^{\mathsf T} H M(s,t) = \det M(s,t)\, H$ (every $M(s,t)$ is a
  similitude), $M(s, t)M(s', t') = M(ss' - tt'\det H, st' + ts')$ (`det_rotM`, `rotM_transpose_mul`, `rotM_mul`);
* `exists_rotM_eq`: **every rotation is an $M(s, t)$** (with $s^2 + t^2\det H = 1$); hence
  `rot_commute`: **the rotations of a binary space commute**;
* `spinorNorm_eq_two_add_trace`: $\theta(\sigma) = (2 + \operatorname{tr}\sigma)K^{\times 2}$ if
  $2 + \operatorname{tr}\sigma \ne 0$, and `spinorNorm_eq_two_sub_trace`: $\theta(\sigma) = (2 - \operatorname{tr}\sigma)
  \det H\, K^{\times 2}$ if $2 - \operatorname{tr}\sigma \ne 0$ (from $\sigma = \tau_{\sigma x - x}\tau_y$,
  `binary_spinorNorm_eq`);
* `exists_sq_eq_of_spinorNorm_eq_one` (**Hilbert's Theorem 90 for the spinor kernel**): if $\theta(\sigma) = 1$ then
  $\sigma = \kappa^2$ for a rotation $\kappa$, namely $\kappa = (1 + \sigma)/c$ with $c^2 = 2 + \operatorname{tr}\sigma$, or
  $\kappa = (1 - \sigma)J/c'$ with $c'^2 = (2 - \operatorname{tr}\sigma)\det H$ (`sq_rootPlus`, `sq_rootMinus`).

In the language of the quadratic algebra $E = K[\sqrt D]$: $O^+(V) = \{\alpha/\bar\alpha\}$ and
$\theta(\alpha/\bar\alpha) = N(\alpha)$, here with $\alpha = 1 + \sigma$ (so $\alpha/\bar\alpha = \sigma$,
$N\alpha = 2 + \operatorname{tr}\sigma$) or $\alpha = (1 - \sigma)J$.
-/
import QuadFormsKB.Literature.ConwaySloane.Section3BinarySpinorNorm
import QuadFormsKB.Lattices.CartanDieudonne

open NumberField Matrix

noncomputable section

namespace QuadFormsKB.ConwaySloane.EstesPall

open QuadFormsKB.Lattices

set_option linter.unusedSectionVars false

/-! ### The algebra $K[J]$ -/

section Algebra

variable {K : Type*} [Field K]

/-- The matrix $J = \begin{pmatrix} -h_1 & -h_2 \\ h_0 & h_1\end{pmatrix}$ of a $2 \times 2$ matrix
$H = (h_{ij})$ (with $h_0 = H_{00}$, $h_1 = H_{01}$, $h_2 = H_{11}$). -/
def rotJ (H : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K := !![-H 0 1, -H 1 1; H 0 0, H 0 1]

/-- $M(s, t) = s\cdot 1 + t\cdot J$. -/
def rotM (H : Matrix (Fin 2) (Fin 2) K) (s t : K) : Matrix (Fin 2) (Fin 2) K := s • 1 + t • rotJ H

theorem rotM_apply (H : Matrix (Fin 2) (Fin 2) K) (s t : K) :
    rotM H s t = !![s - t * H 0 1, -(t * H 1 1); t * H 0 0, s + t * H 0 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotM, rotJ] <;> ring

variable {H : Matrix (Fin 2) (Fin 2) K}

theorem det_rotM (hH : H 1 0 = H 0 1) (s t : K) : (rotM H s t).det = s ^ 2 + t ^ 2 * H.det := by
  rw [rotM_apply, det_fin_two_of, det_fin_two, hH]; ring

theorem trace_rotM (s t : K) : (rotM H s t).trace = 2 * s := by
  rw [rotM_apply, trace_fin_two_of]; ring

theorem rotM_transpose_mul (hH : H 1 0 = H 0 1) (s t : K) :
    (rotM H s t)ᵀ * H * rotM H s t = (rotM H s t).det • H := by
  rw [det_rotM hH, rotM_apply]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, det_fin_two, hH] <;> ring

theorem rotM_mul (hH : H 1 0 = H 0 1) (s t s' t' : K) :
    rotM H s t * rotM H s' t' = rotM H (s * s' - t * t' * H.det) (s * t' + t * s') := by
  simp only [rotM_apply]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, det_fin_two, hH] <;> ring

theorem rotM_comm (hH : H 1 0 = H 0 1) (s t s' t' : K) :
    rotM H s t * rotM H s' t' = rotM H s' t' * rotM H s t := by
  rw [rotM_mul hH, rotM_mul hH]; congr 1 <;> ring

theorem rotM_one_zero : rotM H 1 0 = 1 := by simp [rotM]

/-- **Every rotation of a nondegenerate binary form is an $M(s, t)$**: if $\sigma^{\mathsf T}H\sigma = H$,
$\det\sigma = 1$, $H$ symmetric and $\det H \ne 0$, then $\sigma = M(s, t)$ with $s = \tfrac12\operatorname{tr}\sigma$. -/
theorem exists_rotM_eq [CharZero K] (hH : H 1 0 = H 0 1) (hdet : H.det ≠ 0) {σ : Matrix (Fin 2) (Fin 2) K}
    (hσ : σᵀ * H * σ = H) (hσ1 : σ.det = 1) : ∃ t : K, σ = rotM H ((σ 0 0 + σ 1 1) / 2) t := by
  have hadj : σᵀ * H = H * adjugate σ := by
    calc σᵀ * H = σᵀ * H * (σ * adjugate σ) := by rw [mul_adjugate, hσ1, one_smul, Matrix.mul_one]
      _ = H * adjugate σ := by rw [← Matrix.mul_assoc, hσ]
  rw [adjugate_fin_two] at hadj
  have e00 := congrFun (congrFun hadj 0) 0
  have e01 := congrFun (congrFun hadj 0) 1
  have e11 := congrFun (congrFun hadj 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, hH] at e00 e01 e11
  rw [det_fin_two, hH] at hdet
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  by_cases h0 : H 0 0 = 0
  · have h1 : H 0 1 ≠ 0 := by
      intro h1; apply hdet; rw [h0, h1]; ring
    refine ⟨(σ 1 1 - σ 0 0) / (2 * H 0 1), ?_⟩
    rw [rotM_apply]
    ext i j; fin_cases i <;> fin_cases j <;> simp
    · field_simp; ring
    · field_simp; linear_combination e11
    · have hr : σ 1 0 * (2 * H 0 1) = 0 := by rw [h0] at e00; linear_combination e00
      have hr' : σ 1 0 = 0 := (mul_eq_zero.mp hr).resolve_right (mul_ne_zero h2 h1)
      rw [hr', h0]; ring
    · field_simp; ring
  · refine ⟨σ 1 0 / H 0 0, ?_⟩
    rw [rotM_apply]
    ext i j; fin_cases i <;> fin_cases j <;> simp
    · field_simp; linear_combination e00
    · field_simp; linear_combination e01
    · field_simp
    · field_simp; linear_combination (-1 : K) * e00

end Algebra

/-! ### Rotations of a binary quadratic space -/

variable {F : Type*} [Field F] [NumberField F] (Q : QuadForm F 2) (K : Type*) [Field K] [Algebra F K] [CharZero K]

local notation "H" => Q.hessian.map (algebraMap F K)

theorem hess_symm : H 1 0 = H 0 1 := by
  have := congrFun (congrFun (QuadForm.hessian_transpose Q) 0) 1
  simp only [transpose_apply] at this
  simp [Matrix.map_apply, this]

theorem hess_det_ne_zero (hQ : Q.Nondegenerate) : Matrix.det H ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero _).mpr hQ

/-- The matrix of a rotation is an $M(s, t)$ with $s = \tfrac12\operatorname{tr}\sigma$. -/
theorem exists_rotM_of_rot (hQ : Q.Nondegenerate) (σ : orthGroup Q K) (hσ : σ ∈ Tamagawa.soSub Q K) :
    ∃ t : K, (σ : GL (Fin 2) K).val = rotM H (((σ : GL (Fin 2) K).val 0 0 + (σ : GL (Fin 2) K).val 1 1) / 2) t :=
  exists_rotM_eq (hess_symm Q K) (hess_det_ne_zero Q K hQ) ((mem_orthGroup Q).mp σ.2) hσ

/-- **The rotations of a binary space commute.** -/
@[kb "omeara1963" "§43, p. 104 (the rotations of a binary space form a commutative group)"]
theorem rot_commute (hQ : Q.Nondegenerate) {σ τ : orthGroup Q K} (hσ : σ ∈ Tamagawa.soSub Q K)
    (hτ : τ ∈ Tamagawa.soSub Q K) : σ * τ = τ * σ := by
  obtain ⟨t, ht⟩ := exists_rotM_of_rot Q K hQ σ hσ
  obtain ⟨t', ht'⟩ := exists_rotM_of_rot Q K hQ τ hτ
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [ht, ht']
  exact rotM_comm (hess_symm Q K) _ _ _ _

/-- A similitude $M(s,t)$ multiplies $Q$ by $\det M(s,t)$. -/
theorem evalIn_rotM (s t : K) (x : Fin 2 → K) :
    Q.evalIn K (rotM H s t *ᵥ x) = (rotM H s t).det * Q.evalIn K x := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  apply mul_left_cancel₀ h2
  set M := rotM H s t
  have e : (M *ᵥ x) ⬝ᵥ (H *ᵥ (M *ᵥ x)) = x ⬝ᵥ ((Mᵀ * H * M) *ᵥ x) := by
    calc (M *ᵥ x) ⬝ᵥ (H *ᵥ (M *ᵥ x)) = x ⬝ᵥ (Mᵀ *ᵥ (H *ᵥ (M *ᵥ x))) := by
          rw [dotProduct_mulVec x Mᵀ, vecMul_transpose]
      _ = _ := by rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  rw [two_mul_evalIn, mul_left_comm, two_mul_evalIn, e, rotM_transpose_mul (hess_symm Q K), smul_mulVec, dotProduct_smul,
    smul_eq_mul]

/-! ### Square roots in the algebra -/

section Roots

variable {L : Type*} [Field L] {G : Matrix (Fin 2) (Fin 2) L}

/-- **The square root $(1 + \sigma)/c$**: if $s^2 + t^2\det G = 1$, $c^2 = 2 + 2s$, $ac = 1 + s$ and $bc = t$
($c \ne 0$), then $M(a, b)^2 = M(s, t)$ and $\det M(a, b) = 1$. -/
theorem sq_rootPlus (hG : G 1 0 = G 0 1) {s t c a b : L} (hst : s ^ 2 + t ^ 2 * G.det = 1)
    (hc : c ^ 2 = 2 + 2 * s) (hc0 : c ≠ 0) (ha : a * c = 1 + s) (hb : b * c = t) :
    rotM G a b * rotM G a b = rotM G s t ∧ (rotM G a b).det = 1 := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc0
  refine ⟨?_, ?_⟩
  · rw [rotM_mul hG]
    have e1 : (a * a - b * b * G.det - s) * c ^ 2 = 0 := by
      linear_combination (a * c + (1 + s)) * ha - G.det * (b * c + t) * hb - hst - s * hc
    have e2 : (a * b + b * a - t) * c ^ 2 = 0 := by
      linear_combination 2 * (b * c) * ha + 2 * (1 + s) * hb - t * hc
    have e1' := sub_eq_zero.mp ((mul_eq_zero.mp e1).resolve_right hc2)
    have e2' := sub_eq_zero.mp ((mul_eq_zero.mp e2).resolve_right hc2)
    rw [e1', e2']
  · rw [det_rotM hG]
    have e3 : (a ^ 2 + b ^ 2 * G.det - 1) * c ^ 2 = 0 := by
      linear_combination (a * c + 1 + s) * ha + G.det * (b * c + t) * hb + hst - hc
    exact sub_eq_zero.mp ((mul_eq_zero.mp e3).resolve_right hc2)

/-- **The square root $(1 - \sigma)J/c'$**: if $s^2 + t^2\det G = 1$, $c^2 = (2 - 2s)\det G$, $ac = t\det G$ and
$bc = 1 - s$ ($c \ne 0$), then $M(a, b)^2 = M(s, t)$ and $\det M(a, b) = 1$. -/
theorem sq_rootMinus (hG : G 1 0 = G 0 1) {s t c a b : L} (hst : s ^ 2 + t ^ 2 * G.det = 1)
    (hc : c ^ 2 = (2 - 2 * s) * G.det) (hc0 : c ≠ 0) (ha : a * c = t * G.det) (hb : b * c = 1 - s) :
    rotM G a b * rotM G a b = rotM G s t ∧ (rotM G a b).det = 1 := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc0
  refine ⟨?_, ?_⟩
  · rw [rotM_mul hG]
    have e1 : (a * a - b * b * G.det - s) * c ^ 2 = 0 := by
      linear_combination (a * c + t * G.det) * ha - G.det * (b * c + (1 - s)) * hb + G.det * hst - s * hc
    have e2 : (a * b + b * a - t) * c ^ 2 = 0 := by
      linear_combination 2 * (b * c) * ha + 2 * (t * G.det) * hb - t * hc
    have e1' := sub_eq_zero.mp ((mul_eq_zero.mp e1).resolve_right hc2)
    have e2' := sub_eq_zero.mp ((mul_eq_zero.mp e2).resolve_right hc2)
    rw [e1', e2']
  · rw [det_rotM hG]
    have e3 : (a ^ 2 + b ^ 2 * G.det - 1) * c ^ 2 = 0 := by
      linear_combination (a * c + t * G.det) * ha + G.det * (b * c + (1 - s)) * hb + G.det * hst - hc
    exact sub_eq_zero.mp ((mul_eq_zero.mp e3).resolve_right hc2)

/-- $\det(\colMat\,x\,y)^2\det G = (x^{\mathsf T}Gx)(y^{\mathsf T}Gy) - (x^{\mathsf T}Gy)(y^{\mathsf T}Gx)$. -/
theorem det_colMat_sq_mul (x y : Fin 2 → L) :
    (colMat L x y).det ^ 2 * G.det =
      (x ⬝ᵥ (G *ᵥ x)) * (y ⬝ᵥ (G *ᵥ y)) - (x ⬝ᵥ (G *ᵥ y)) * (y ⬝ᵥ (G *ᵥ x)) := by
  simp [colMat, det_fin_two_of, dotProduct, mulVec, Fin.sum_univ_two, det_fin_two]; ring

end Roots

theorem sqClassOf_sq_mul_bin {L : Type*} [Field L] [CharZero L] {u d : L} (hu : u ≠ 0) (hd : d ≠ 0) : sqClassOf (u ^ 2 * d) = sqClassOf d := by
  rw [sqClassOf_mul (pow_ne_zero 2 hu) hd, (sqClassOf_eq_one_iff (pow_ne_zero 2 hu)).mpr ⟨u, sq u⟩, one_mul]

/-- An $M(a, b)$ of determinant $1$ as a rotation. -/
def mkRot (a b : K) (h : (rotM H a b).det = 1) : orthGroup Q K :=
  ⟨Matrix.nonsingInvUnit (rotM H a b) (by rw [h]; exact isUnit_one), by
    rw [mem_orthGroup]
    show (rotM H a b)ᵀ * H * rotM H a b = H
    rw [rotM_transpose_mul (hess_symm Q K), h, one_smul]⟩

theorem mkRot_val (a b : K) (h : (rotM H a b).det = 1) : ((mkRot Q K a b h : GL (Fin 2) K)).val = rotM H a b :=
  rfl

theorem mkRot_mem (a b : K) (h : (rotM H a b).det = 1) : mkRot Q K a b h ∈ Tamagawa.soSub Q K := h

/-- For orthogonal $x, y$: $4Q(x)Q(y) = \det[x \mid y]^2\det H$. -/
theorem four_mul_evalIn_mul {x y : Fin 2 → K} (hxy : x ⬝ᵥ (H *ᵥ y) = 0) :
    4 * (Q.evalIn K x * Q.evalIn K y) = (colMat K x y).det ^ 2 * Matrix.det H := by
  rw [det_colMat_sq_mul, ← two_mul_evalIn, ← two_mul_evalIn, hxy]; ring

/-- **The spinor norm of a binary rotation, second form**: $\theta(\sigma) = (2 - \operatorname{tr}\sigma)\det H\,
K^{\times 2}$ when $2 - \operatorname{tr}\sigma \ne 0$. -/
@[kb "omeara1963" "§55, p. 137 (spinor norm of a binary rotation through det(σ − 1))"]
theorem spinorNorm_eq_two_sub_trace (hQ : Q.Nondegenerate) (σ : orthGroup Q K) (hσ : σ ∈ Tamagawa.soSub Q K)
    (hY : 2 - ((σ : GL (Fin 2) K).val 0 0 + (σ : GL (Fin 2) K).val 1 1) ≠ 0) :
    spinorNorm Q K σ =
      sqClassOf ((2 - ((σ : GL (Fin 2) K).val 0 0 + (σ : GL (Fin 2) K).val 1 1)) * Matrix.det H) := by
  set s := ((σ : GL (Fin 2) K).val 0 0 + (σ : GL (Fin 2) K).val 1 1) / 2 with hs
  have htr : (σ : GL (Fin 2) K).val 0 0 + (σ : GL (Fin 2) K).val 1 1 = 2 * s := by rw [hs]; ring
  rw [htr] at hY ⊢
  obtain ⟨t, ht⟩ := exists_rotM_of_rot Q K hQ σ hσ
  rw [← hs] at ht
  have hdet1 : s ^ 2 + t ^ 2 * Matrix.det H = 1 := by
    rw [← det_rotM (hess_symm Q K), ← ht]; exact hσ
  obtain ⟨e, he, hea⟩ := exists_orthogonal_basis Q K hQ
  have hxy : e 0 ⬝ᵥ (H *ᵥ e 1) = 0 := he 0 1 (by decide)
  have hsub : (σ : GL (Fin 2) K).val *ᵥ e 0 - e 0 = rotM H (s - 1) t *ᵥ e 0 := by
    have hm : rotM H (s - 1) t = rotM H s t - 1 := by simp only [rotM]; rw [sub_smul, one_smul]; abel
    rw [ht, hm, sub_mulVec, one_mulVec]
  have hQu : Q.evalIn K ((σ : GL (Fin 2) K).val *ᵥ e 0 - e 0) = (2 - 2 * s) * Q.evalIn K (e 0) := by
    rw [hsub, evalIn_rotM, det_rotM (hess_symm Q K)]
    congr 1
    linear_combination hdet1
  have hu : Q.evalIn K ((σ : GL (Fin 2) K).val *ᵥ e 0 - e 0) ≠ 0 := by rw [hQu]; exact mul_ne_zero hY (hea 0)
  rw [binary_spinorNorm_eq Q K hQ σ hσ (hea 0) (hea 1) hxy hu, hQu]
  have h4 := four_mul_evalIn_mul Q K hxy
  set d := (colMat K (e 0) (e 1)).det
  have hd : d ≠ 0 := by
    intro hd0
    rw [hd0] at h4
    have : Q.evalIn K (e 0) * Q.evalIn K (e 1) = 0 := by linear_combination h4 / 4
    exact mul_ne_zero (hea 0) (hea 1) this
  have e : (2 - 2 * s) * Q.evalIn K (e 0) * Q.evalIn K (e 1) = (d / 2) ^ 2 * ((2 - 2 * s) * Matrix.det H) := by
    linear_combination ((2 - 2 * s) / 4) * h4
  rw [e, sqClassOf_sq_mul_bin (div_ne_zero hd two_ne_zero) (mul_ne_zero hY (hess_det_ne_zero Q K hQ))]

/-- **The spinor norm of a binary rotation through its trace**: $\theta(\sigma) = (2 + \operatorname{tr}\sigma)\,
K^{\times 2}$ when $2 + \operatorname{tr}\sigma \ne 0$ (in the quadratic algebra: $\sigma = \alpha/\bar\alpha$
with $\alpha = 1 + \sigma$, $N(\alpha) = \det(1 + \sigma) = 2 + \operatorname{tr}\sigma$). -/
@[kb "omeara1963" "§55, p. 137 (spinor norm of a binary rotation: θ(α/ᾱ) = N(α), α = 1 + σ)"]
theorem spinorNorm_eq_two_add_trace (hQ : Q.Nondegenerate) (σ : orthGroup Q K) (hσ : σ ∈ Tamagawa.soSub Q K)
    (hX : 2 + ((σ : GL (Fin 2) K).val 0 0 + (σ : GL (Fin 2) K).val 1 1) ≠ 0) :
    spinorNorm Q K σ = sqClassOf (2 + ((σ : GL (Fin 2) K).val 0 0 + (σ : GL (Fin 2) K).val 1 1)) := by
  set s := ((σ : GL (Fin 2) K).val 0 0 + (σ : GL (Fin 2) K).val 1 1) / 2 with hs
  have htr : (σ : GL (Fin 2) K).val 0 0 + (σ : GL (Fin 2) K).val 1 1 = 2 * s := by rw [hs]; ring
  obtain ⟨t, ht⟩ := exists_rotM_of_rot Q K hQ σ hσ
  rw [← hs] at ht
  have hdet1 : s ^ 2 + t ^ 2 * Matrix.det H = 1 := by
    rw [← det_rotM (hess_symm Q K), ← ht]; exact hσ
  by_cases hY : 2 - ((σ : GL (Fin 2) K).val 0 0 + (σ : GL (Fin 2) K).val 1 1) = 0
  · -- `σ = 1`
    have hs1 : s = 1 := by rw [htr] at hY; linear_combination (-1/2 : K) * hY
    have ht0 : t = 0 := by
      have h0 : t ^ 2 * Matrix.det H = 0 := by rw [hs1] at hdet1; linear_combination hdet1
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
        ((mul_eq_zero.mp h0).resolve_right (hess_det_ne_zero Q K hQ))
    have hσ1 : σ = 1 := by
      refine Subtype.ext (Units.ext ?_)
      rw [ht, hs1, ht0, rotM_one_zero]; rfl
    rw [htr, hs1, hσ1]
    have h1 : spinorNorm Q K 1 = 1 := by
      have := (spinorNormHom Q K hQ).map_one
      rwa [spinorNormHom_apply] at this
    rw [h1, show (2 : K) + 2 * 1 = 2 ^ 2 * 1 by norm_num, sqClassOf_sq_mul_bin two_ne_zero one_ne_zero, sqClassOf_one]
  · rw [spinorNorm_eq_two_sub_trace Q K hQ σ hσ hY]
    rw [htr] at hX hY ⊢
    have hdH := hess_det_ne_zero Q K hQ
    have ht0 : t ≠ 0 := by
      rintro rfl
      have : (2 + 2 * s) * (2 - 2 * s) = 0 := by linear_combination (-4 : K) * hdet1
      rcases mul_eq_zero.mp this with h | h
      exacts [hX h, hY h]
    have key : (2 + 2 * s) * ((2 - 2 * s) * Matrix.det H) = (2 * t * Matrix.det H) ^ 2 := by
      linear_combination (-4 * Matrix.det H) * hdet1
    have hsq : sqClassOf (2 + 2 * s) * sqClassOf ((2 - 2 * s) * Matrix.det H) = 1 := by
      rw [← sqClassOf_mul hX (mul_ne_zero hY hdH), key, sqClassOf_eq_one_iff
        (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero two_ne_zero ht0) hdH))]
      exact ⟨_, sq _⟩
    rw [← inv_eq_of_mul_eq_one_right hsq, SqClass.inv_eq]

theorem rotM_div (s t c : K) : rotM H (s / c) (t / c) = c⁻¹ • rotM H s t := by
  simp only [rotM, smul_add, smul_smul]; congr 1 <;> rw [div_eq_inv_mul]

theorem one_add_rotM (s t : K) : 1 + rotM H s t = rotM H (1 + s) t := by
  simp only [rotM, add_smul, one_smul]; abel

theorem one_sub_rotM_mul_J (s t : K) : (1 - rotM H s t) * rotJ H = rotM H (t * Matrix.det H) (1 - s) := by
  have hJ : rotJ H = rotM H 0 1 := by simp [rotM]
  have h1 : 1 - rotM H s t = rotM H (1 - s) (-t) := by simp only [rotM, sub_smul, one_smul, neg_smul]; abel
  rw [h1, hJ, rotM_mul (hess_symm Q K)]
  congr 1 <;> ring

/-- **The square root $(1 + \sigma)/c$ of a rotation in the spinor kernel**: if $\theta(\sigma) = 1$ and
$2 + \operatorname{tr}\sigma \ne 0$, then $2 + \operatorname{tr}\sigma = c^2$ and $\kappa = c^{-1}(1 + \sigma)$ is a
rotation with $\kappa^2 = \sigma$. -/
theorem exists_sq_eq_plus (hQ : Q.Nondegenerate) (σ : orthGroup Q K) (hσ : σ ∈ Tamagawa.soSub Q K)
    (hθ : spinorNorm Q K σ = 1) (hX : 2 + ((σ : GL (Fin 2) K).val 0 0 + (σ : GL (Fin 2) K).val 1 1) ≠ 0) :
    ∃ c : K, c ^ 2 = 2 + ((σ : GL (Fin 2) K).val 0 0 + (σ : GL (Fin 2) K).val 1 1) ∧
      ∃ κ : orthGroup Q K, κ ∈ Tamagawa.soSub Q K ∧ κ * κ = σ ∧
        (κ : GL (Fin 2) K).val = c⁻¹ • (1 + (σ : GL (Fin 2) K).val) := by
  set s := ((σ : GL (Fin 2) K).val 0 0 + (σ : GL (Fin 2) K).val 1 1) / 2 with hs
  have htr : (σ : GL (Fin 2) K).val 0 0 + (σ : GL (Fin 2) K).val 1 1 = 2 * s := by rw [hs]; ring
  obtain ⟨t, ht⟩ := exists_rotM_of_rot Q K hQ σ hσ
  rw [← hs] at ht
  have hdet1 : s ^ 2 + t ^ 2 * Matrix.det H = 1 := by
    rw [← det_rotM (hess_symm Q K), ← ht]; exact hσ
  have h1 := spinorNorm_eq_two_add_trace Q K hQ σ hσ hX
  rw [htr] at hX
  rw [hθ, htr, eq_comm, sqClassOf_eq_one_iff hX] at h1
  obtain ⟨c, hc⟩ := h1
  have hc0 : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; exact hX hc
  obtain ⟨hsq, hdet⟩ := sq_rootPlus (hess_symm Q K) hdet1 (c := c) (by rw [hc]; ring) hc0
    (a := (1 + s) / c) (b := t / c) (by field_simp) (by field_simp)
  refine ⟨c, by rw [htr, hc]; ring, mkRot Q K _ _ hdet, mkRot_mem Q K _ _ hdet, Subtype.ext (Units.ext ?_), ?_⟩
  · simp only [Subgroup.coe_mul, Units.val_mul, mkRot_val]
    rw [hsq, ht]
  · rw [mkRot_val, rotM_div, ht, one_add_rotM]

/-- **The square root $(1 - \sigma)J/c$ of a rotation in the spinor kernel**: if $\theta(\sigma) = 1$ and
$2 - \operatorname{tr}\sigma \ne 0$, then $(2 - \operatorname{tr}\sigma)\det H = c^2$ and
$\kappa = c^{-1}(1 - \sigma)J$ is a rotation with $\kappa^2 = \sigma$. -/
theorem exists_sq_eq_minus (hQ : Q.Nondegenerate) (σ : orthGroup Q K) (hσ : σ ∈ Tamagawa.soSub Q K)
    (hθ : spinorNorm Q K σ = 1) (hY : 2 - ((σ : GL (Fin 2) K).val 0 0 + (σ : GL (Fin 2) K).val 1 1) ≠ 0) :
    ∃ c : K, c ^ 2 = (2 - ((σ : GL (Fin 2) K).val 0 0 + (σ : GL (Fin 2) K).val 1 1)) * Matrix.det H ∧
      ∃ κ : orthGroup Q K, κ ∈ Tamagawa.soSub Q K ∧ κ * κ = σ ∧
        (κ : GL (Fin 2) K).val = c⁻¹ • ((1 - (σ : GL (Fin 2) K).val) * rotJ H) := by
  set s := ((σ : GL (Fin 2) K).val 0 0 + (σ : GL (Fin 2) K).val 1 1) / 2 with hs
  have htr : (σ : GL (Fin 2) K).val 0 0 + (σ : GL (Fin 2) K).val 1 1 = 2 * s := by rw [hs]; ring
  obtain ⟨t, ht⟩ := exists_rotM_of_rot Q K hQ σ hσ
  rw [← hs] at ht
  have hdet1 : s ^ 2 + t ^ 2 * Matrix.det H = 1 := by
    rw [← det_rotM (hess_symm Q K), ← ht]; exact hσ
  have hdH := hess_det_ne_zero Q K hQ
  have h1 := spinorNorm_eq_two_sub_trace Q K hQ σ hσ hY
  rw [htr] at hY
  rw [hθ, htr, eq_comm, sqClassOf_eq_one_iff (mul_ne_zero hY hdH)] at h1
  obtain ⟨c, hc⟩ := h1
  have hc0 : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; exact mul_ne_zero hY hdH hc
  obtain ⟨hsq, hdet⟩ := sq_rootMinus (hess_symm Q K) hdet1 (c := c) (by rw [hc]; ring) hc0
    (a := t * Matrix.det H / c) (b := (1 - s) / c) (by field_simp) (by field_simp)
  refine ⟨c, by rw [htr, hc]; ring, mkRot Q K _ _ hdet, mkRot_mem Q K _ _ hdet, Subtype.ext (Units.ext ?_), ?_⟩
  · simp only [Subgroup.coe_mul, Units.val_mul, mkRot_val]
    rw [hsq, ht]
  · rw [mkRot_val, rotM_div, ht, one_sub_rotM_mul_J]

/-- **Hilbert's Theorem 90 for the spinor kernel of a binary space**: a rotation $\sigma$ with $\theta(\sigma) = 1$
is the square $\kappa^2$ of a rotation $\kappa$. -/
@[kb "omeara1963" "§55, p. 137 (binary spaces: O'(V) consists of the squares of rotations)"]
theorem exists_sq_eq_of_spinorNorm_eq_one (hQ : Q.Nondegenerate) (σ : orthGroup Q K) (hσ : σ ∈ Tamagawa.soSub Q K)
    (hθ : spinorNorm Q K σ = 1) : ∃ κ : orthGroup Q K, κ ∈ Tamagawa.soSub Q K ∧ κ * κ = σ := by
  set s := ((σ : GL (Fin 2) K).val 0 0 + (σ : GL (Fin 2) K).val 1 1) / 2 with hs
  have htr : (σ : GL (Fin 2) K).val 0 0 + (σ : GL (Fin 2) K).val 1 1 = 2 * s := by rw [hs]; ring
  obtain ⟨t, ht⟩ := exists_rotM_of_rot Q K hQ σ hσ
  rw [← hs] at ht
  have hdet1 : s ^ 2 + t ^ 2 * Matrix.det H = 1 := by
    rw [← det_rotM (hess_symm Q K), ← ht]; exact hσ
  have hdH := hess_det_ne_zero Q K hQ
  by_cases hX : 2 + 2 * s = 0
  · have hY : 2 - ((σ : GL (Fin 2) K).val 0 0 + (σ : GL (Fin 2) K).val 1 1) ≠ 0 := by
      rw [htr]; intro h; have : (4 : K) = 0 := by linear_combination hX + h
      norm_num at this
    have h1 := spinorNorm_eq_two_sub_trace Q K hQ σ hσ hY
    rw [hθ, htr, eq_comm, sqClassOf_eq_one_iff (mul_ne_zero (by rwa [htr] at hY) hdH)] at h1
    obtain ⟨c, hc⟩ := h1
    have hc0 : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; exact mul_ne_zero (by rwa [htr] at hY) hdH hc
    obtain ⟨hsq, hdet⟩ := sq_rootMinus (hess_symm Q K) hdet1 (c := c) (by rw [hc]; ring) hc0
      (a := t * Matrix.det H / c) (b := (1 - s) / c) (by field_simp) (by field_simp)
    refine ⟨mkRot Q K _ _ hdet, mkRot_mem Q K _ _ hdet, Subtype.ext (Units.ext ?_)⟩
    simp only [Subgroup.coe_mul, Units.val_mul, mkRot_val]
    rw [hsq, ht]
  · have h1 := spinorNorm_eq_two_add_trace Q K hQ σ hσ (by rwa [htr])
    rw [hθ, htr, eq_comm, sqClassOf_eq_one_iff hX] at h1
    obtain ⟨c, hc⟩ := h1
    have hc0 : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; exact hX hc
    obtain ⟨hsq, hdet⟩ := sq_rootPlus (hess_symm Q K) hdet1 (c := c) (by rw [hc]; ring) hc0
      (a := (1 + s) / c) (b := t / c) (by field_simp) (by field_simp)
    refine ⟨mkRot Q K _ _ hdet, mkRot_mem Q K _ _ hdet, Subtype.ext (Units.ext ?_)⟩
    simp only [Subgroup.coe_mul, Units.val_mul, mkRot_val]
    rw [hsq, ht]

end QuadFormsKB.ConwaySloane.EstesPall
