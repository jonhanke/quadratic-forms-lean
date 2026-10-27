import Mathlib

/-!
# Split quaternion algebras: $\mathbb H[R,a,b]\cong M_2(R)$ when $b$ is a norm from $R[\sqrt a]$

**Generic, Mathlib only (upstreamable).** For a commutative ring $R$ with $2, a, b$ invertible and $x, y\in R$ with
$x^2 - ay^2 = b$, the matrices
$$I = \begin{pmatrix}0&a\\1&0\end{pmatrix},\quad J = \begin{pmatrix}x&-ay\\y&-x\end{pmatrix},\quad
K = IJ = \begin{pmatrix}ay&-ax\\x&-ay\end{pmatrix}$$
satisfy $I^2 = a$, $J^2 = b$, $JI = -K$ (`quatMatBasis`), so `QuaternionAlgebra.lift` gives an algebra homomorphism
$\mathbb H[R,a,b]\to M_2(R)$; it is bijective with an explicit inverse (`quatMatEquiv`), and
$\det(\varphi(q)) = \operatorname{nrd}(q)$ (`det_quatMatEquiv`).

Over a field $F$ of characteristic $\ne 2$ (`exists_norm_eq_of_not_division`): if $\mathbb H[F,a,b]$ is not a division
algebra, then $b = x^2 - ay^2$ for some $x, y\in F$, so $\mathbb H[F,a,b]\cong M_2(F)$.

This is the standard splitting criterion (Voight, *Quaternion Algebras*, Main Theorem 5.4.4 and §5.4 [unverified
locator]; Lam, *Introduction to Quadratic Forms over Fields*, III.2.7 [unverified locator]). Mathlib v4.35.0 has
`QuaternionAlgebra.lift` (`Mathlib/Algebra/QuaternionBasis.lean`) but no splitting criterion (searched 2026-10-21).
-/

open Matrix
open scoped Quaternion

namespace QuadFormsKB.Tamagawa.Measure.Weil

section Ring

variable {R : Type*} [CommRing R] (a b x y : R)

/-- The quaternion basis $(I, J, K)$ of $M_2(R)$ for $\mathbb H[R,a,b]$ (given $x^2 - ay^2 = b$). -/
def quatMatBasis (h : x ^ 2 - a * y ^ 2 = b) : QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) R) a 0 b where
  i := !![0, a; 1, 0]
  j := !![x, -(a * y); y, -x]
  k := !![a * y, -(a * x); x, -(a * y)]
  i_mul_i := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  j_mul_j := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ← h] <;> ring
  i_mul_j := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  j_mul_i := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The algebra homomorphism $\mathbb H[R,a,b]\to M_2(R)$. -/
noncomputable def quatMatHom (h : x ^ 2 - a * y ^ 2 = b) : ℍ[R,a,b] →ₐ[R] Matrix (Fin 2) (Fin 2) R :=
  (quatMatBasis a b x y h).liftHom

theorem quatMatHom_apply (h : x ^ 2 - a * y ^ 2 = b) (q : ℍ[R,a,b]) :
    quatMatHom a b x y h q = !![q.re + q.imJ * x + q.imK * (a * y), q.imI * a - q.imJ * (a * y) - q.imK * (a * x);
      q.imI + q.imJ * y + q.imK * x, q.re - q.imJ * x - q.imK * (a * y)] := by
  rw [quatMatHom, QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift]
  ext i j; fin_cases i <;> fin_cases j <;> simp [quatMatBasis, Algebra.algebraMap_eq_smul_one] <;> ring

/-- **The reduced norm is the determinant**: $\det\varphi(q) = q\bar q$. -/
theorem det_quatMatHom (h : x ^ 2 - a * y ^ 2 = b) (q : ℍ[R,a,b]) :
    (quatMatHom a b x y h q).det = (q * star q).re := by
  rw [quatMatHom_apply, Matrix.det_fin_two_of]
  simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
    QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, ← h]
  ring

variable [Invertible (2 : R)] [Invertible a] [Invertible b]

/-- The inverse of `quatMatHom` (explicit; uses $2, a, b$ invertible). -/
noncomputable def quatMatInv (m : Matrix (Fin 2) (Fin 2) R) : ℍ[R,a,b] :=
  let P := ⅟2 * (m 0 0 - m 1 1)
  let Q := ⅟2 * (m 1 0 - ⅟a * m 0 1)
  ⟨⅟2 * (m 0 0 + m 1 1), ⅟2 * (m 1 0 + ⅟a * m 0 1), ⅟b * (x * P - a * y * Q), ⅟b * (x * Q - y * P)⟩

theorem quatMatInv_quatMatHom (h : x ^ 2 - a * y ^ 2 = b) (q : ℍ[R,a,b]) :
    quatMatInv a b x y (quatMatHom a b x y h q) = q := by
  rw [quatMatHom_apply]
  have h2 : (⅟2 : R) * 2 = 1 := invOf_mul_self 2
  have ha : (⅟a : R) * a = 1 := invOf_mul_self a
  have hb : (⅟b : R) * b = 1 := invOf_mul_self b
  simp only [quatMatInv, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  have hP : ⅟2 * (q.re + q.imJ * x + q.imK * (a * y) - (q.re - q.imJ * x - q.imK * (a * y))) =
      q.imJ * x + q.imK * (a * y) := by linear_combination (q.imJ * x + q.imK * (a * y)) * h2
  have hQ : ⅟2 * (q.imI + q.imJ * y + q.imK * x - ⅟a * (q.imI * a - q.imJ * (a * y) - q.imK * (a * x))) =
      q.imJ * y + q.imK * x := by
    linear_combination (q.imJ * y + q.imK * x) * h2 - ⅟2 * (q.imI - q.imJ * y - q.imK * x) * ha
  rw [hP, hQ]
  ext
  · change ⅟2 * (q.re + q.imJ * x + q.imK * (a * y) + (q.re - q.imJ * x - q.imK * (a * y))) = q.re
    linear_combination q.re * h2
  · change ⅟2 * (q.imI + q.imJ * y + q.imK * x + ⅟a * (q.imI * a - q.imJ * (a * y) - q.imK * (a * x))) = q.imI
    linear_combination q.imI * h2 + ⅟2 * (q.imI - q.imJ * y - q.imK * x) * ha
  · change ⅟b * (x * (q.imJ * x + q.imK * (a * y)) - a * y * (q.imJ * y + q.imK * x)) = q.imJ
    linear_combination q.imJ * hb + ⅟b * q.imJ * h
  · change ⅟b * (x * (q.imJ * y + q.imK * x) - y * (q.imJ * x + q.imK * (a * y))) = q.imK
    linear_combination q.imK * hb + ⅟b * q.imK * h

theorem quatMatHom_quatMatInv (h : x ^ 2 - a * y ^ 2 = b) (m : Matrix (Fin 2) (Fin 2) R) :
    quatMatHom a b x y h (quatMatInv a b x y m) = m := by
  rw [quatMatHom_apply]
  have h2 : (⅟2 : R) * 2 = 1 := invOf_mul_self 2
  have ha : (⅟a : R) * a = 1 := invOf_mul_self a
  have hb : (⅟b : R) * b = 1 := invOf_mul_self b
  set P := ⅟2 * (m 0 0 - m 1 1)
  set Q := ⅟2 * (m 1 0 - ⅟a * m 0 1)
  have ht : (quatMatInv a b x y m).imJ * x + (quatMatInv a b x y m).imK * (a * y) = P := by
    change ⅟b * (x * P - a * y * Q) * x + ⅟b * (x * Q - y * P) * (a * y) = P
    linear_combination P * hb + ⅟b * P * h
  have hu : (quatMatInv a b x y m).imJ * y + (quatMatInv a b x y m).imK * x = Q := by
    change ⅟b * (x * P - a * y * Q) * y + ⅟b * (x * Q - y * P) * x = Q
    linear_combination Q * hb + ⅟b * Q * h
  have hre : (quatMatInv a b x y m).re = ⅟2 * (m 0 0 + m 1 1) := rfl
  have hI : (quatMatInv a b x y m).imI = ⅟2 * (m 1 0 + ⅟a * m 0 1) := rfl
  ext i j; fin_cases i <;> fin_cases j
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue]
    rw [add_assoc, ht, hre]; simp only [P]; linear_combination (m 0 0) * h2
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue, Fin.mk_one]
    rw [sub_sub, show (quatMatInv a b x y m).imJ * (a * y) + (quatMatInv a b x y m).imK * (a * x) = a * Q by
      rw [← hu]; ring, hI]
    simp only [Q]; linear_combination (m 0 1) * h2 + (⅟2 * 2 * m 0 1) * ha
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue, Fin.mk_one]
    rw [add_assoc, hu, hI]; simp only [Q]; linear_combination (m 1 0) * h2
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_cons, Fin.isValue, Fin.mk_one]
    rw [sub_sub, ht, hre]; simp only [P]; linear_combination (m 1 1) * h2

/-- **$\mathbb H[R,a,b]\cong M_2(R)$** when $b = x^2 - ay^2$ and $2, a, b$ are invertible. -/
noncomputable def quatMatEquiv (h : x ^ 2 - a * y ^ 2 = b) : ℍ[R,a,b] ≃ₐ[R] Matrix (Fin 2) (Fin 2) R :=
  AlgEquiv.ofBijective (quatMatHom a b x y h)
    ⟨Function.LeftInverse.injective (g := quatMatInv a b x y) (quatMatInv_quatMatHom a b x y h),
      Function.RightInverse.surjective (g := quatMatInv a b x y) (quatMatHom_quatMatInv a b x y h)⟩

theorem quatMatEquiv_apply (h : x ^ 2 - a * y ^ 2 = b) (q : ℍ[R,a,b]) :
    quatMatEquiv a b x y h q = quatMatHom a b x y h q := rfl

/-- $\detarphi(q) = \operatorname{nrd}(q)$ for the isomorphism. -/
theorem det_quatMatEquiv (h : x ^ 2 - a * y ^ 2 = b) (q : ℍ[R,a,b]) :
    (quatMatEquiv a b x y h q).det = (q * star q).re := det_quatMatHom a b x y h q

end Ring

section Field

variable {F : Type*} [Field F] (a b : F)

theorem re_mul_star_eq_nrd (q : ℍ[F,a,b]) :
    (q * star q).re = q.re ^ 2 - a * q.imI ^ 2 - b * q.imJ ^ 2 + a * b * q.imK ^ 2 := by
  simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
    QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star]
  ring

/-- **The splitting criterion**: if $\mathbb H[F,a,b]$ is not a division algebra ($2, a, b
e 0$), then $b$ is a norm
from $F(\sqrt a)$: $b = x^2 - ay^2$. -/
theorem exists_norm_eq_of_not_division (h2 : (2 : F) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ¬ ∀ ξ : ℍ[F,a,b], ξ ≠ 0 → IsUnit ξ) : ∃ x y : F, x ^ 2 - a * y ^ 2 = b := by
  push Not at h
  obtain ⟨ξ, hξ0, hξu⟩ := h
  have hn : (ξ * star ξ).re = 0 := by
    by_contra hn
    apply hξu
    have h1 : ξ * ((ξ * star ξ).re⁻¹ • star ξ) = 1 := by
      rw [mul_smul_comm, QuaternionAlgebra.mul_star_eq_coe]
      generalize (ξ * star ξ).re = n at hn ⊢
      ext <;> simp [hn]
    have h1' : ((ξ * star ξ).re⁻¹ • star ξ) * ξ = 1 := by
      rw [smul_mul_assoc, QuaternionAlgebra.star_mul_eq_coe,
        show (star ξ * ξ).re = (ξ * star ξ).re by
          simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
            QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star]; ring]
      generalize (ξ * star ξ).re = n at hn ⊢
      ext <;> simp [hn]
    exact ⟨⟨ξ, _, h1, h1'⟩, rfl⟩
  rw [re_mul_star_eq_nrd] at hn
  set r := ξ.re; set s := ξ.imI; set t := ξ.imJ; set w := ξ.imK
  by_cases hsq : ∃ c : F, a = c ^ 2
  · obtain ⟨c, rfl⟩ := hsq
    have hc : c ≠ 0 := by rintro rfl; exact ha (by ring)
    refine ⟨(b + 1) / 2, (b - 1) / (2 * c), ?_⟩
    field_simp
    ring
  · push Not at hsq
    have hN : t ^ 2 - a * w ^ 2 ≠ 0 := by
      intro hN
      have hw : w = 0 := by
        by_contra hw
        exact hsq (t / w) (by field_simp; linear_combination -hN)
      have ht : t = 0 := by rw [hw] at hN; simpa using hN
      have hs : s = 0 := by
        by_contra hs
        exact hsq (r / s) (by field_simp; rw [hw, ht] at hn; linear_combination -hn)
      have hr : r = 0 := by rw [hw, ht, hs] at hn; simpa using hn
      exact hξ0 (QuaternionAlgebra.ext hr hs ht hw)
    refine ⟨(r * t - a * s * w) / (t ^ 2 - a * w ^ 2), (s * t - r * w) / (t ^ 2 - a * w ^ 2), ?_⟩
    field_simp
    linear_combination (t ^ 2 - a * w ^ 2) * hn

end Field

end QuadFormsKB.Tamagawa.Measure.Weil
