/-
# Cassels, Chapter 13: remaining items of §§5–6, the introduction, and Example 6 (book version)

Formalization of Cassels, *Rational Quadratic Forms* (1978), Ch. 13: (5.19)–(5.20) (p. 303), the map $\pi$ of §6
(p. 304), Meyer's theorem as quoted in the introduction (p. 284), and Example 6 (p. 329) with the book's inequalities.

**Conventions.** Indices are 0-based, so the book's $X_1, X_2, X_3$ are `x 0, x 1, x 2`; $f_0 = x_0x_2 - x_1^2$ is
`fZero`.
-/
import QuadFormsKB.Literature.Cassels.Ch13.ExamplesPell
import QuadFormsKB.Literature.Cassels.Ch13.Sec5
import QuadFormsKB.Literature.Cassels.Ch13.Sec7
import QuadFormsKB.Literature.Cassels.Ch13.Sec8
import QuadFormsKB.Literature.Cassels.Ch6.Sec1

open Matrix

namespace QuadFormsKB.Reduction

/-! ### Helpers: splitting off a hyperbolic plane from a rational ternary form -/

def bfm (A : Matrix (Fin 3) (Fin 3) ℚ) (x y : Fin 3 → ℚ) : ℚ := x ⬝ᵥ (A *ᵥ y)

theorem bfm_comm {A : Matrix (Fin 3) (Fin 3) ℚ} (hs : Aᵀ = A) (x y : Fin 3 → ℚ) :
    bfm A x y = bfm A y x := by
  unfold bfm
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hs, dotProduct_comm]

theorem bfm_add_right (A : Matrix (Fin 3) (Fin 3) ℚ) (x y z : Fin 3 → ℚ) :
    bfm A x (y + z) = bfm A x y + bfm A x z := by simp [bfm, mulVec_add, dotProduct_add]
theorem bfm_sub_right (A : Matrix (Fin 3) (Fin 3) ℚ) (x y z : Fin 3 → ℚ) :
    bfm A x (y - z) = bfm A x y - bfm A x z := by simp [bfm, mulVec_sub, dotProduct_sub]
theorem bfm_smul_right (A : Matrix (Fin 3) (Fin 3) ℚ) (x y : Fin 3 → ℚ) (c : ℚ) :
    bfm A x (c • y) = c * bfm A x y := by simp [bfm, mulVec_smul, dotProduct_smul]
theorem bfm_add_left (A : Matrix (Fin 3) (Fin 3) ℚ) (x y z : Fin 3 → ℚ) :
    bfm A (x + y) z = bfm A x z + bfm A y z := by simp [bfm, add_dotProduct]
theorem bfm_sub_left (A : Matrix (Fin 3) (Fin 3) ℚ) (x y z : Fin 3 → ℚ) :
    bfm A (x - y) z = bfm A x z - bfm A y z := by simp [bfm, sub_dotProduct]
theorem bfm_smul_left (A : Matrix (Fin 3) (Fin 3) ℚ) (x y : Fin 3 → ℚ) (c : ℚ) :
    bfm A (c • x) y = c * bfm A x y := by simp [bfm, smul_dotProduct]
theorem bfm_zero_right (A : Matrix (Fin 3) (Fin 3) ℚ) (x : Fin 3 → ℚ) : bfm A x 0 = 0 := by simp [bfm]

theorem gram_apply (R A : Matrix (Fin 3) (Fin 3) ℚ) (i j : Fin 3) :
    (R * A * Rᵀ) i j = bfm A (R i) (R j) := by
  simp only [bfm, Matrix.mul_apply, dotProduct, mulVec, transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem gram_form (P A : Matrix (Fin 3) (Fin 3) ℚ) (y : Fin 3 → ℚ) :
    bfm A (P *ᵥ y) (P *ᵥ y) = y ⬝ᵥ ((Pᵀ * A * P) *ᵥ y) := by
  have h : (Pᵀ * A * P) *ᵥ y = Pᵀ *ᵥ (A *ᵥ (P *ᵥ y)) := by
    rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec]
  rw [h, dotProduct_mulVec, vecMul_transpose]
  rfl

theorem hyperbolic_core (A : Matrix (Fin 3) (Fin 3) ℚ) (hs : Aᵀ = A) (hdet : A.det ≠ 0)
    (v : Fin 3 → ℚ) (hv : v ≠ 0) (hv0 : bfm A v v = 0) :
    ∃ (M : Matrix (Fin 3) (Fin 3) ℚ) (m : ℚ), m ≠ 0 ∧ M.det ≠ 0 ∧
      ∀ x, m * bfm A x x = (M *ᵥ x) 0 * (M *ᵥ x) 2 - (M *ᵥ x) 1 ^ 2 := by
  obtain ⟨u, hu⟩ : ∃ u, bfm A v u ≠ 0 := by
    by_contra h
    push Not at h
    apply hdet
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨v, hv, ?_⟩
    have h2 : (A *ᵥ v) ⬝ᵥ (A *ᵥ v) = 0 := by
      have := h (A *ᵥ v)
      rw [bfm_comm hs] at this
      exact this
    exact dotProduct_self_eq_zero.mp h2
  set β := bfm A v u with hβ
  set w : Fin 3 → ℚ := β⁻¹ • u - (bfm A u u / (2 * β ^ 2)) • v with hw
  have huv : bfm A u v = β := bfm_comm hs u v
  have hvw : bfm A v w = 1 := by
    simp only [hw, bfm_sub_right, bfm_smul_right, hv0, ← hβ]
    field_simp
    ring
  have hwv : bfm A w v = 1 := by rw [bfm_comm hs]; exact hvw
  have hww : bfm A w w = 0 := by
    simp only [hw, bfm_sub_right, bfm_sub_left, bfm_smul_right, bfm_smul_left, hv0, huv, ← hβ]
    field_simp
    ring
  have hli : LinearIndependent ℚ ![v, w] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 := congrArg (bfm A v) h
    have h2 := congrArg (bfm A w) h
    simp only [bfm_add_right, bfm_smul_right, bfm_zero_right, hv0, hvw, hwv, hww] at h1 h2
    constructor <;> linarith
  have hcross : crossProduct v w ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.mpr hli
  set e := crossProduct v w with he
  have hdet0 : Matrix.det (![v, w, e] : Matrix (Fin 3) (Fin 3) ℚ) ≠ 0 := by
    rw [← triple_product_eq_det, ← triple_product_permutation]
    exact fun h => hcross (dotProduct_self_eq_zero.mp h)
  set p := bfm A v e with hp
  set q := bfm A w e with hq
  set z : Fin 3 → ℚ := e - q • v - p • w with hz
  have hev : bfm A e v = p := bfm_comm hs e v
  have hew : bfm A e w = q := bfm_comm hs e w
  have hzv : bfm A z v = 0 := by
    simp only [hz, bfm_sub_left, bfm_smul_left, hev, hv0, hwv]; ring
  have hzw : bfm A z w = 0 := by
    simp only [hz, bfm_sub_left, bfm_smul_left, hew, hvw, hww]; ring
  have hvz : bfm A v z = 0 := by rw [bfm_comm hs]; exact hzv
  have hwz : bfm A w z = 0 := by rw [bfm_comm hs]; exact hzw
  set d := bfm A z z with hd
  have hdetz : Matrix.det (![v, w, z] : Matrix (Fin 3) (Fin 3) ℚ) ≠ 0 := by
    have : Matrix.det (![v, w, z] : Matrix (Fin 3) (Fin 3) ℚ) = Matrix.det (![v, w, e] : Matrix (Fin 3) (Fin 3) ℚ) := by
      rw [← triple_product_eq_det, ← triple_product_eq_det]
      simp [hz, cross_apply, dotProduct, Fin.sum_univ_three]
      ring
    rw [this]; exact hdet0
  set R : Matrix (Fin 3) (Fin 3) ℚ := ![v, w, z] with hR
  set P : Matrix (Fin 3) (Fin 3) ℚ := Rᵀ with hPdef
  have hPdet : P.det ≠ 0 := by rw [hPdef, det_transpose]; exact hdetz
  set G : Matrix (Fin 3) (Fin 3) ℚ := !![0, 1, 0; 1, 0, 0; 0, 0, d] with hG
  have hGeq : Pᵀ * A * P = G := by
    rw [hPdef, transpose_transpose]
    ext i j
    rw [gram_apply]
    fin_cases i <;> fin_cases j <;> simp [hR, hG, hv0, hvw, hwv, hww, hvz, hwz, hzv, hzw, hd]
  have hdne : d ≠ 0 := by
    intro h0
    have h1 : G.det = 0 := by simp [hG, Matrix.det_fin_three, h0]
    rw [← hGeq, det_mul, det_mul, det_transpose] at h1
    simp [hPdet, hdet] at h1
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hPdet
  refine ⟨!![-2 * d, 0, 0; 0, 0, d; 0, 1, 0] * P⁻¹, -d, neg_ne_zero.mpr hdne, ?_, ?_⟩
  · rw [det_mul, det_nonsing_inv]
    have : (!![-2 * d, 0, 0; 0, 0, d; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℚ).det = 2 * d ^ 2 := by
      simp [Matrix.det_fin_three]; ring
    rw [this]
    have : Ring.inverse P.det = (P.det)⁻¹ := by
      rw [Ring.inverse_eq_inv']
    rw [this]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 2 hdne)) (inv_ne_zero hPdet)
  · intro x
    set y := P⁻¹ *ᵥ x with hy
    have hx : P *ᵥ y = x := by rw [hy, mulVec_mulVec, mul_nonsing_inv _ hPu, one_mulVec]
    have h1 : bfm A x x = y ⬝ᵥ (G *ᵥ y) := by
      rw [← hx, gram_form, hGeq]
    have h2 : (!![-2 * d, 0, 0; 0, 0, d; 0, 1, 0] * P⁻¹) *ᵥ x = !![-2 * d, 0, 0; 0, 0, d; 0, 1, 0] *ᵥ y := by
      rw [← mulVec_mulVec]
    rw [h2, h1]
    simp [hG, mulVec, dotProduct, Fin.sum_univ_three]
    ring


/-- Helper: an integral form over $\mathbb{Q}$ has the same values as its rational base change. -/
theorem evalIn_map_intRat {n : ℕ} (f : IntQF n) (x : Fin n → ℚ) :
    (f.map (Int.castRingHom ℚ)).evalIn ℚ x = f.evalIn ℚ x := by
  simp [QuadForm.evalIn, QuadForm.map]

/-- Helper: the value of an integral form at an integral vector, as a rational. -/
theorem eval_cast_rat {n : ℕ} (f : IntQF n) (c : Fin n → ℤ) :
    ((f.eval c : ℤ) : ℚ) = f.evalIn ℚ (fun i => (c i : ℚ)) := by
  simp [QuadForm.evalIn]

/-- Helper: an integral regular form is regular over $\mathbb{Q}$. -/
theorem nondegenerate_map_intRat {n : ℕ} (f : IntQF n) (hf : f.Nondegenerate) :
    (f.map (Int.castRingHom ℚ)).Nondegenerate := by
  unfold QuadForm.Nondegenerate at hf ⊢
  have h1 : (f.map (Int.castRingHom ℚ)).hessian = f.hessian.map (Int.castRingHom ℚ) := by
    simp [QuadForm.hessian, QuadForm.map, Matrix.transpose_map, Matrix.map_add]
  rw [h1, show (f.hessian.map (Int.castRingHom ℚ)).det = ((f.hessian.det : ℤ) : ℚ) from
    (RingHom.map_det (Int.castRingHom ℚ) f.hessian).symm]
  exact_mod_cast hf

/-- Helper: the value of a rational ternary form as the bilinear expression of its half-Hessian. -/
theorem rat_eval_eq_bfm (Q : RatQF 3) (x : Fin 3 → ℚ) :
    Q.evalIn ℚ x = bfm ((1 / 2 : ℚ) • Q.hessian) x x := by
  rw [QuadForm.evalIn_eq_dotProduct]
  have hC : Q.coeff.map (algebraMap ℚ ℚ) = Q.coeff := by ext i j; simp
  have hT : x ⬝ᵥ (Q.coeff)ᵀ *ᵥ x = x ⬝ᵥ Q.coeff *ᵥ x := by
    rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  rw [hC]
  simp only [bfm, QuadForm.hessian, Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_smul, hT]
  simp
  ring

/-- Helper: over $\mathbb{Q}$, an isotropic regular ternary form is a rational multiple of $f_0$ composed with an
invertible rational matrix (the hyperbolic splitting of the proof of (5.19)). -/
theorem exists_fZero_scaling_rat (Q : RatQF 3) (hQ : Q.Nondegenerate) (hiso : Q.IsotropicIn ℚ) :
    ∃ (m : ℚ) (M : Matrix (Fin 3) (Fin 3) ℚ), m ≠ 0 ∧ M.det ≠ 0 ∧
      ∀ x : Fin 3 → ℚ, m * Q.evalIn ℚ x = fZero.evalIn ℚ (M *ᵥ x) := by
  set A : Matrix (Fin 3) (Fin 3) ℚ := (1 / 2 : ℚ) • Q.hessian with hA
  have hs : Aᵀ = A := by
    simp [hA, QuadForm.hessian, Matrix.transpose_add, add_comm]
  have hdet : A.det ≠ 0 := by
    rw [hA, det_smul]
    have : Q.hessian.det ≠ 0 := hQ
    simp [this]
  obtain ⟨v, hv, hv0⟩ := hiso
  obtain ⟨M, m, hm, hM, h⟩ := hyperbolic_core A hs hdet v hv (by rw [← rat_eval_eq_bfm]; exact hv0)
  exact ⟨m, M, hm, hM, fun x => by rw [rat_eval_eq_bfm, h, evalIn_fZero]⟩

/-- Helper: a common denominator for finitely many rationals. -/
theorem exists_den_mul (s : Finset ℚ) : ∃ k : ℕ, 0 < k ∧ ∀ q ∈ s, ∃ z : ℤ, (k : ℚ) * q = z := by
  refine ⟨∏ q ∈ s, q.den, Finset.prod_pos (fun q _ => q.den_pos), fun q hq => ?_⟩
  obtain ⟨j, hj⟩ := Finset.dvd_prod_of_mem (fun q : ℚ => q.den) hq
  refine ⟨j * q.num, ?_⟩
  rw [hj]
  push_cast
  have := Rat.mul_den_eq_num q
  calc ((q.den : ℚ) * j) * q = j * (q * q.den) := by ring
    _ = _ := by rw [this]

/-- Helper: (5.19) with rational vectors. -/
theorem exists_int_scaling (Q : IntQF 3) (hQ : Q.Nondegenerate) (hiso : Q.IsotropicIn ℚ) :
    ∃ (m : ℤ) (Z : Matrix (Fin 3) (Fin 3) ℤ), m ≠ 0 ∧ Z.det ≠ 0 ∧
      ∀ x : Fin 3 → ℚ, (m : ℚ) * Q.evalIn ℚ x = fZero.evalIn ℚ (Z.map (Int.castRingHom ℚ) *ᵥ x) := by
  have hiso' : (Q.map (Int.castRingHom ℚ)).IsotropicIn ℚ := by
    obtain ⟨x, hx0, hx⟩ := hiso
    exact ⟨x, hx0, by rw [evalIn_map_intRat]; exact hx⟩
  obtain ⟨m0, M, hm0, hM, h⟩ := exists_fZero_scaling_rat _ (nondegenerate_map_intRat Q hQ) hiso'
  obtain ⟨k, hk, hkint⟩ := exists_den_mul
    (insert m0 (Finset.univ.image fun p : Fin 3 × Fin 3 => M p.1 p.2))
  choose Z0 hZ0 using fun i j => hkint (M i j)
    (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j))))
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin 3) (Fin 3) ℤ, ∀ i j, (k : ℚ) * M i j = Z i j := ⟨Matrix.of Z0, hZ0⟩
  obtain ⟨zm, hzm⟩ := hkint m0 (Finset.mem_insert_self _ _)
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hZM : Z.map (Int.castRingHom ℚ) = (k : ℚ) • M := by
    ext i j; simp [hZ]
  refine ⟨k * zm, Z, ?_, ?_, ?_⟩
  · intro h0
    have : (k : ℚ) * (zm : ℚ) = 0 := by exact_mod_cast h0
    rw [← hzm] at this
    exact mul_ne_zero hkQ (mul_ne_zero hkQ hm0) (by linear_combination this)
  · intro h0
    have h1 : (Z.det : ℚ) = 0 := by exact_mod_cast h0
    have hd : (Z.map (Int.castRingHom ℚ)).det = ((Z.det : ℤ) : ℚ) := (RingHom.map_det (Int.castRingHom ℚ) Z).symm
    rw [← hd, hZM, det_smul] at h1
    simp at h1
    rcases h1 with h1 | h1
    · exact hkQ (by exact_mod_cast h1)
    · exact hM h1
  · intro x
    rw [hZM, Matrix.smul_mulVec, evalIn_fZero]
    have := h x
    rw [evalIn_map_intRat, evalIn_fZero] at this
    push_cast
    rw [← hzm]
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination (k : ℚ) ^ 2 * this

/-! ### Example 6, book version -/

/-- **Example 6, book version** (Cassels, Ch. 13, Examples, Ex. 6, p. 329): let $f = ax^2 + 2bxy + cy^2$ be classically
integral with $a > 0 > c$, and let $t, u$ be an integral solution of $t^2 + (ac - b^2)u^2 = 1$ with $t > 0$, $u > 0$.
Every integral solution of $f(x, y) = e$, $e > 0$, is in the same orbit under the integral automorphs of $f$ as a
solution $(x', y')$ with
$$x' > 0, \qquad y' > 0, \qquad -aux' + (t - bu)y' \le 0.$$
(The inequalities are transcribed from the page image of p. 329; the machine-read text had garbled them.) Derived from `example_6`: if $y' = 0$,
apply the automorph (3.14) `pellMat a b c t u`. -/
@[kb "cassels1978" "Ch. 13, Examples, Ex. 6, p. 329 (book's inequalities)"]
theorem example_6_book {a b c : ℤ} (ha : 0 < a) (hc : c < 0) {t u : ℤ} (ht : 0 < t) (hu : 0 < u)
    (hpell : t ^ 2 + (a * c - b ^ 2) * u ^ 2 = 1) {e : ℤ} (he : 0 < e) {x y : ℤ}
    (hxy : a * x ^ 2 + 2 * b * x * y + c * y ^ 2 = e) :
    ∃ T ∈ Siegel.Aut (cform a b c), ∃ x' y' : ℤ, T.val *ᵥ ![x, y] = ![x', y'] ∧
      0 < x' ∧ 0 < y' ∧ -a * u * x' + (t - b * u) * y' ≤ 0 := by
  obtain ⟨T, hT, x', y', hTv, hy', hlt⟩ := example_6 ha hc ht hu hpell he hxy
  have hac : a * c < 0 := by nlinarith
  have htb : 0 < t - b * u := by
    by_contra hneg
    push Not at hneg
    have h1 : (t - b * u) * (t + b * u) = 1 - a * c * u ^ 2 := by linear_combination hpell
    have h2 : 0 < 1 - a * c * u ^ 2 := by nlinarith [mul_pos hu hu]
    have h3 : t + b * u < 0 := by
      by_contra h4; push Not at h4; nlinarith
    nlinarith
  rcases hy'.lt_or_eq with hpos | hzero
  · refine ⟨T, hT, x', y', hTv, ?_, hpos, hlt.le⟩
    by_contra hx
    push Not at hx
    nlinarith [mul_pos ha hu, mul_nonneg (mul_pos ha hu).le (neg_nonneg.mpr hx), mul_pos htb hpos]
  · subst hzero
    have hx : 0 < x' := by
      by_contra hx
      push Not at hx
      nlinarith [mul_pos ha hu, mul_nonneg (mul_pos ha hu).le (neg_nonneg.mpr hx)]
    have hP := pellGL_mem hpell
    refine ⟨pellGL a b c t u hpell * T, Subgroup.mul_mem _ (Siegel.mem_autPlus_iff.mp hP).1 hT,
      (t - b * u) * x', a * u * x', ?_, mul_pos htb hx, mul_pos (mul_pos ha hu) hx, by nlinarith⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hTv]
    ext i; fin_cases i <;> simp [pellGL, pellMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-! ### Meyer's theorem as quoted in the introduction (p. 284) -/

/-- **Meyer's theorem, contrapositive form** (Cassels, Ch. 13, §1, p. 284): *an indefinite form can be anisotropic over
$\mathbb{Q}$ only when $n \le 4$.* Here $Q$ is a regular rational form in $n$ variables (`Q.Nondegenerate`),
indefinite in the sense of taking a positive and a negative real value (`hpos`, `hneg`), and anisotropic over
$\mathbb{Q}$ (`hani`); then $n \le 4$. Derived from `Cassels.Ch6.meyer`. -/
@[kb "cassels1978" "Ch. 13, §1, p. 284 (Meyer: indefinite anisotropic forms have n ≤ 4)"]
theorem anisotropic_indefinite_le_four {n : ℕ} (Q : RatQF n) (hQ : Q.Nondegenerate)
    (hpos : ∃ x : Fin n → ℝ, 0 < Q.evalIn ℝ x) (hneg : ∃ y : Fin n → ℝ, Q.evalIn ℝ y < 0)
    (hani : ¬ Q.IsotropicIn ℚ) : n ≤ 4 := by
  by_contra h
  exact hani (Cassels.Ch6.meyer Q (by omega) hQ hpos hneg)

/-- **Meyer's theorem for integral forms** (Cassels, Ch. 13, §1, p. 284): the same for an integral form $f$ (regular:
nonzero Hessian determinant, i.e. regular over $\mathbb{Q}$; indefinite over $\mathbb{R}$; anisotropic over
$\mathbb{Q}$): $n \le 4$. -/
@[kb "cassels1978" "Ch. 13, §1, p. 284 (Meyer: indefinite anisotropic forms have n ≤ 4), integral form"]
theorem anisotropic_indefinite_le_four_int {n : ℕ} (f : IntQF n) (hf : f.Nondegenerate)
    (hpos : ∃ x : Fin n → ℝ, 0 < f.evalIn ℝ x) (hneg : ∃ y : Fin n → ℝ, f.evalIn ℝ y < 0)
    (hani : ¬ f.IsotropicIn ℚ) : n ≤ 4 := by
  have hreal : ∀ x : Fin n → ℝ, (f.map (Int.castRingHom ℚ)).evalIn ℝ x = f.evalIn ℝ x := by
    intro x; simp [QuadForm.evalIn, QuadForm.map]
  have hrat : ∀ x : Fin n → ℚ, (f.map (Int.castRingHom ℚ)).evalIn ℚ x = f.evalIn ℚ x := by
    intro x; simp [QuadForm.evalIn, QuadForm.map]
  exact anisotropic_indefinite_le_four (f.map (Int.castRingHom ℚ)) (nondegenerate_map_intRat f hf)
    (by obtain ⟨x, hx⟩ := hpos; exact ⟨x, by rw [hreal]; exact hx⟩)
    (by obtain ⟨x, hx⟩ := hneg; exact ⟨x, by rw [hreal]; exact hx⟩)
    (fun ⟨x, hx0, hx⟩ => hani ⟨x, hx0, by rw [← hrat]; exact hx⟩)

/-! ### The map $\pi$ for $f = X_1^2 + X_2^2 - X_3^2$ (p. 304) -/

/-- **Position of $\pi(\vec{x})$ relative to the disc $\mathcal D$** (Cassels, Ch. 13, §6, p. 304, below (6.9)): for
$f(\vec{x}) = x_0^2 + x_1^2 - x_2^2$ (the book's $X_1^2 + X_2^2 - X_3^2$) and $\pi = $ `projPt`,
(i) if $f(\vec{x}) < 0$, then $x_2 \ne 0$ (so $\pi(\vec{x})$ is defined) and $\pi(\vec{x}) \in \mathcal D$ (`disc`);
(ii) if $f(\vec{x}) = 0$ and $\vec{x} \ne 0$, then $x_2 \ne 0$ and $\pi(\vec{x})$ lies on the boundary circle
$\xi_0^2 + \xi_1^2 = 1$ of $\mathcal D$;
(iii) if $f(\vec{x}) > 0$, then either $x_2 = 0$ ($\pi$ undefined) or $\pi(\vec{x})$ lies outside the closed disc,
$\xi_0^2 + \xi_1^2 > 1$. -/
@[kb "cassels1978" "Ch. 13, §6, p. 304 (π(x) in 𝒟 / on the boundary / outside, by the sign of f(x))"]
theorem projPt_position (x : Fin 3 → ℝ) :
    (x 0 ^ 2 + x 1 ^ 2 - x 2 ^ 2 < 0 → x 2 ≠ 0 ∧ projPt x ∈ disc) ∧
    (x 0 ^ 2 + x 1 ^ 2 - x 2 ^ 2 = 0 → x ≠ 0 →
      x 2 ≠ 0 ∧ projPt x 0 ^ 2 + projPt x 1 ^ 2 = 1) ∧
    (0 < x 0 ^ 2 + x 1 ^ 2 - x 2 ^ 2 →
      x 2 = 0 ∨ 1 < projPt x 0 ^ 2 + projPt x 1 ^ 2) := by
  refine ⟨fun h => projPt_mem_disc (by linarith), fun h hx => ?_, fun h => ?_⟩
  · have h2 : x 2 ≠ 0 := by
      intro h0
      apply hx
      rw [h0] at h
      have h0' : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
      have h1' : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
      ext i; fin_cases i <;> simp [h0, h0', h1']
    refine ⟨h2, ?_⟩
    have hpos : 0 < x 2 ^ 2 := by positivity
    simp only [projPt, Matrix.cons_val_zero, Matrix.cons_val_one, div_pow]
    rw [← add_div, div_eq_one_iff_eq hpos.ne']
    linarith
  · by_cases h2 : x 2 = 0
    · exact Or.inl h2
    · right
      have hpos : 0 < x 2 ^ 2 := by positivity
      simp only [projPt, Matrix.cons_val_zero, Matrix.cons_val_one, div_pow]
      rw [← add_div, one_lt_div hpos]
      linarith


/-! ### (5.19) and (5.20): the general isotropic ternary form (p. 303) -/

/-- **(5.19)** (Cassels, Ch. 13, §5, p. 303): let $f$ be a classically integral, regular (`hreg`) ternary form that
is isotropic over $\mathbb{Q}$ (`hiso`). Then there are an integer $m \ne 0$ and a nonsingular integral $3 \times 3$
matrix $M$ with
$$m f(\vec{x}) = f_0(M\vec{x}), \qquad f_0 = x_0x_2 - x_1^2 \ (\text{`fZero`}),$$
for all integral $\vec{x}$. (Classical integrality `_hci` is not used in the proof: the statement holds for every
integral regular ternary form isotropic over $\mathbb{Q}$.) Proof: over $\mathbb{Q}$, $f \cong \mathbb{H} \perp \langle d \rangle$
with $f_0 \cong \mathbb{H} \perp \langle -1 \rangle$; scale by $m_0 = -d$, then clear denominators
($M \mapsto kM$, $m_0 \mapsto k^2m_0$). The identity also holds for rational $\vec{x}$ (`exists_int_scaling`). -/
@[kb "cassels1978" "Ch. 13, §5, (5.19), p. 303"]
theorem integral_isotropic_ternary_scaling (f : IntQF 3) (_hci : IsClassicallyIntegral f) (hreg : f.Nondegenerate)
    (hiso : f.IsotropicIn ℚ) :
    ∃ (m : ℤ) (M : Matrix (Fin 3) (Fin 3) ℤ), m ≠ 0 ∧ M.det ≠ 0 ∧
      ∀ x : Fin 3 → ℤ, m * f.eval x = fZero.eval (M *ᵥ x) := by
  obtain ⟨m, Z, hm, hZ, h⟩ := exists_int_scaling f hreg hiso
  refine ⟨m, Z, hm, hZ, fun x => ?_⟩
  have h1 := h (fun i => (x i : ℚ))
  have h2 : (Z.map (Int.castRingHom ℚ)) *ᵥ (fun i => (x i : ℚ)) = fun i => ((Z *ᵥ x) i : ℚ) := by
    ext i; simp [mulVec, dotProduct]
  rw [h2, ← eval_cast_rat, ← eval_cast_rat] at h1
  exact_mod_cast h1

/-- **(5.20)** (Cassels, Ch. 13, §5, p. 303): let $m \ne 0$ and $M$ be nonsingular integral with
$m f(\vec{x}) = f_0(M\vec{x})$ for integral $\vec{x}$ (as in (5.19), hypothesis `hfM`), and let $b \in \mathbb{Z}$.
(i) If $f(\vec{x}) = b$, then $M\vec{x}$ is an integral representation of $mb$ by $f_0$.
(ii) Conversely, if $\vec{c}$ is an integral representation of $mb$ by $f_0$ and $M^{-1}\vec{c} \in \mathbb{Z}^3$ (the
congruence condition (5.20), modulo $\det M$), then $\vec{x} = M^{-1}\vec{c}$ is an integral representation of $b$ by $f$
with $M\vec{x} = \vec{c}$.
(iii) For $S = \begin{pmatrix}\alpha&\beta\\ \gamma&\delta\end{pmatrix} \in SL_2^{\pm}(\mathbb{Z})$ (`hS`: $\det S = \pm 1$)
and $\vec{c}$ an integral representation of $mb$ by $f_0$, the vector $T(S)\vec{c}$ (`spinMat`) is again an integral
vector $\vec{c}_1$ representing $mb$ by $f_0$, and if $M^{-1}\vec{c}_1 \in \mathbb{Z}^3$ it comes from an integral
representation of $b$ by $f$ as in (ii). -/
@[kb "cassels1978" "Ch. 13, §5, (5.19)–(5.20), p. 303"]
theorem representation_correspondence (f : IntQF 3) {m : ℤ} (M : Matrix (Fin 3) (Fin 3) ℤ) (hm : m ≠ 0)
    (hM : M.det ≠ 0) (hfM : ∀ x : Fin 3 → ℤ, m * f.eval x = fZero.eval (M *ᵥ x)) (b : ℤ) :
    (∀ x : Fin 3 → ℤ, f.eval x = b → fZero.eval (M *ᵥ x) = m * b) ∧
    (∀ c : Fin 3 → ℤ, fZero.eval c = m * b →
      (∃ x : Fin 3 → ℤ, (fun i => (x i : ℚ)) = (M.map (Int.castRingHom ℚ))⁻¹ *ᵥ (fun i => (c i : ℚ))) →
      ∃ x : Fin 3 → ℤ, M *ᵥ x = c ∧ f.eval x = b) ∧
    (∀ α β γ δ : ℤ, (α * δ - β * γ = 1 ∨ α * δ - β * γ = -1) →
      ∀ c : Fin 3 → ℤ, fZero.eval c = m * b →
      ∃ c₁ : Fin 3 → ℤ, (fun i => (c₁ i : ℚ)) = spinMat !![(α : ℚ), β; γ, δ] *ᵥ (fun i => (c i : ℚ)) ∧
        fZero.eval c₁ = m * b ∧
        ((∃ x : Fin 3 → ℤ, (fun i => (x i : ℚ)) = (M.map (Int.castRingHom ℚ))⁻¹ *ᵥ (fun i => (c₁ i : ℚ))) →
          ∃ x : Fin 3 → ℤ, M *ᵥ x = c₁ ∧ f.eval x = b)) := by
  have hMq : IsUnit (M.map (Int.castRingHom ℚ)).det := by
    have hd : (M.map (Int.castRingHom ℚ)).det = ((M.det : ℤ) : ℚ) := (RingHom.map_det (Int.castRingHom ℚ) M).symm
    rw [hd]
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hM)
  have part2 : ∀ c : Fin 3 → ℤ, fZero.eval c = m * b →
      (∃ x : Fin 3 → ℤ, (fun i => (x i : ℚ)) = (M.map (Int.castRingHom ℚ))⁻¹ *ᵥ (fun i => (c i : ℚ))) →
      ∃ x : Fin 3 → ℤ, M *ᵥ x = c ∧ f.eval x = b := by
    intro c hc ⟨x, hx⟩
    have hMx : M *ᵥ x = c := by
      have h1 : (fun i => ((M *ᵥ x) i : ℚ)) = fun i => (c i : ℚ) := by
        have : (fun i => ((M *ᵥ x) i : ℚ)) = (M.map (Int.castRingHom ℚ)) *ᵥ (fun i => (x i : ℚ)) := by
          ext i; simp [mulVec, dotProduct]
        rw [this, hx, mulVec_mulVec, mul_nonsing_inv _ hMq, one_mulVec]
      ext i
      have := congrFun h1 i
      exact_mod_cast this
    refine ⟨x, hMx, ?_⟩
    have := hfM x
    rw [hMx, hc] at this
    exact mul_left_cancel₀ hm this
  refine ⟨fun x hx => by rw [← hfM x, hx], part2, ?_⟩
  intro α β γ δ hS c hc
  set ε : ℤ := α * δ - β * γ with hε
  have hq : (α : ℚ) * δ - β * γ = ε := by rw [hε]; push_cast; ring
  have hne : (α : ℚ) * δ - β * γ ≠ 0 := by
    rw [hq]; rcases hS with h | h <;> rw [h] <;> norm_num
  have hinv : ((α : ℚ) * δ - β * γ)⁻¹ = ε := by
    rw [hq]
    rcases hS with h | h <;> rw [h] <;> norm_num
  set c₁ : Fin 3 → ℤ := ![ε * (α ^ 2 * c 0 + 2 * α * γ * c 1 + γ ^ 2 * c 2),
    ε * (α * β * c 0 + (α * δ + β * γ) * c 1 + γ * δ * c 2),
    ε * (β ^ 2 * c 0 + 2 * β * δ * c 1 + δ ^ 2 * c 2)] with hc₁
  have hcast : (fun i => (c₁ i : ℚ)) = spinMat !![(α : ℚ), β; γ, δ] *ᵥ (fun i => (c i : ℚ)) := by
    ext i
    fin_cases i <;> simp [hc₁, spinMat_eq, hinv, mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  have hval : fZero.eval c₁ = m * b := by
    have h1 : ((fZero.eval c₁ : ℤ) : ℚ) = ((fZero.eval c : ℤ) : ℚ) := by
      rw [eval_cast_rat, eval_cast_rat, hcast]
      exact spinMat_f0 α β γ δ hne _
    rw [← hc]
    exact_mod_cast h1
  exact ⟨c₁, hcast, hval, part2 c₁ hval⟩

/-! ### Theorem 6.1 fails for isotropic forms (p. 305) -/

/-- Helper: an isotropic integral form has a nonzero integral zero. -/
theorem exists_int_isotropic_vec (Q : IntQF 3) (hQ : Q.IsotropicIn ℚ) :
    ∃ v : Fin 3 → ℤ, v ≠ 0 ∧ Q.eval v = 0 := by
  obtain ⟨x, hx0, hx⟩ := hQ
  obtain ⟨k, hk, hkint⟩ := exists_den_mul (Finset.univ.image x)
  choose z hz using fun i => hkint (x i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hcast : (fun i => (z i : ℚ)) = (k : ℚ) • x := by ext i; simp [hz i]
  refine ⟨z, ?_, ?_⟩
  · intro h0
    apply hx0
    have : (k : ℚ) • x = 0 := by rw [← hcast]; funext i; simp [h0]
    exact (smul_eq_zero.mp this).resolve_left hkQ
  · have h1 := eval_cast_rat Q z
    have h2 : Q.evalIn ℚ ((k : ℚ) • x) = (k : ℚ) ^ 2 * Q.evalIn ℚ x := by
      simp only [QuadForm.evalIn, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> ring
    rw [hcast, h2, hx, mul_zero] at h1
    exact_mod_cast h1

/-- Helper: a linear image of a coordinatewise-bounded vector is coordinatewise-bounded. -/
theorem bdd_mulVec' (M : Matrix (Fin 3) (Fin 3) ℝ) : ∃ C : ℝ, ∀ (X : Fin 3 → ℝ) (B : ℝ), 0 ≤ B →
    (∀ j, |X j| ≤ B) → ∀ i, |(M *ᵥ X) i| ≤ C * B := by
  let _ := Matrix.linftyOpNormedAddCommGroup (m := Fin 3) (n := Fin 3) (α := ℝ)
  refine ⟨‖M‖, fun X B hB hX i => ?_⟩
  have h1 : ‖X‖ ≤ B := (pi_norm_le_iff_of_nonneg hB).2 (fun j => by simpa using hX j)
  calc |(M *ᵥ X) i| = ‖(M *ᵥ X) i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖M *ᵥ X‖ := norm_le_pi_norm _ i
    _ ≤ ‖M‖ * ‖X‖ := Matrix.linfty_opNorm_mulVec M X
    _ ≤ ‖M‖ * B := by gcongr

/-- Helper: the value of the integral form is the Lorentz value of $L\vec{c}$. -/
theorem eval_eq_lorB {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ}
    (hF : realMat Q = Lᵀ * lorentz * L) (c : Fin 3 → ℤ) :
    ((Q.eval c : ℤ) : ℝ) = lorB (L *ᵥ cast c) (L *ᵥ cast c) := by
  have : ((Q.eval c : ℤ) : ℝ) = val (realMat Q) (cast c) := by
    rw [← QuadForm.evalIn_real_eq_val]
    simp [QuadForm.evalIn, cast]
  rw [this, lorB_eq, hF, val, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

/-- Helper: $L\,\widetilde{(Tc)} = A\,(L\tilde c)$ for $A = L \tilde T L^{-1}$. -/
theorem L_cast_mulVec' {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det) (T : Matrix (Fin 3) (Fin 3) ℤ)
    (c : Fin 3 → ℤ) : L *ᵥ cast (T *ᵥ c) = (L * castM T * L⁻¹) *ᵥ (L *ᵥ cast c) := by
  have h : L * castM T * L⁻¹ * L = L * castM T := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul L hL, Matrix.mul_one]
  rw [← castM_mulVec_cast, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

/-- Helper: a vector of $\mathbb{R}^3$ with $\mathrm{lorB}(x, x) = 0$ is null. -/
theorem null_of_lorB {x : Fin 3 → ℝ} (h : lorB x x = 0) : x 0 ^ 2 + x 1 ^ 2 = x 2 ^ 2 := by
  simp only [lorB] at h; nlinarith

/-- Helper: two null vectors with negative Lorentz pairing have last coordinates of the same sign. -/
theorem null_pair_sign {x y : Fin 3 → ℝ} (hx : x 0 ^ 2 + x 1 ^ 2 = x 2 ^ 2) (hy : y 0 ^ 2 + y 1 ^ 2 = y 2 ^ 2)
    (h : lorB x y < 0) : 0 < x 2 * y 2 := by
  by_contra hneg
  push Not at hneg
  have hcs : (x 0 * y 0 + x 1 * y 1) ^ 2 ≤ (-(x 2 * y 2)) ^ 2 := by
    have h1 : (x 2 * y 2) ^ 2 = (x 0 ^ 2 + x 1 ^ 2) * (y 0 ^ 2 + y 1 ^ 2) := by
      rw [mul_pow, ← hx, ← hy]
    rw [neg_sq, h1]
    nlinarith [sq_nonneg (x 0 * y 1 - x 1 * y 0)]
  have := (abs_le_of_sq_le_sq' hcs (by linarith)).1
  simp only [lorB] at h
  linarith

/-- Helper: the Lorentz value of a combination of two vectors. -/
theorem lorB_comb (n m : Fin 3 → ℝ) (p q : ℝ) :
    lorB (p • n + q • m) (p • n + q • m) = p ^ 2 * lorB n n + 2 * p * q * lorB n m + q ^ 2 * lorB m m := by
  simp only [lorB, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Helper: the last coordinates of the images of integral nonzero null vectors are bounded away from $0$. -/
theorem null_lower_bound {Q : IntQF 3} {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det)
    (hF : realMat Q = Lᵀ * lorentz * L) :
    ∃ c : ℝ, 0 < c ∧ ∀ w : Fin 3 → ℤ, w ≠ 0 → Q.eval w = 0 → c ≤ |(L *ᵥ cast w) 2| := by
  obtain ⟨C, hC⟩ := bdd_mulVec' L⁻¹
  refine ⟨1 / (|C| + 1), by positivity, fun w hw hQw => ?_⟩
  set y := L *ᵥ cast w with hy
  have hnull : y 0 ^ 2 + y 1 ^ 2 = y 2 ^ 2 := by
    apply null_of_lorB
    rw [← eval_eq_lorB hF, hQw]
    simp
  have hbd : ∀ j, |y j| ≤ |y 2| := by
    intro j
    rw [← sq_le_sq]
    fin_cases j
    · show y 0 ^ 2 ≤ y 2 ^ 2
      nlinarith [sq_nonneg (y 1)]
    · show y 1 ^ 2 ≤ y 2 ^ 2
      nlinarith [sq_nonneg (y 0)]
    · exact le_rfl
  have hcast : cast w = L⁻¹ *ᵥ y := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul L hL, Matrix.one_mulVec]
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (funext h)
  have h1 : (1 : ℝ) ≤ |(L⁻¹ *ᵥ y) i| := by
    rw [← hcast]
    show 1 ≤ |((w i : ℤ) : ℝ)|
    exact_mod_cast Int.one_le_abs hi
  have h2 := hC y |y 2| (abs_nonneg _) hbd i
  have h3 : 1 ≤ (|C| + 1) * |y 2| := by
    nlinarith [le_abs_self C, abs_nonneg (y 2)]
  rw [div_le_iff₀ (by positivity)]
  linarith

set_option maxHeartbeats 1000000 in
/-- **For isotropic forms the conclusion of the Corollary to Theorem 6.1 fails** (Cassels, Ch. 13, §6, p. 305): let
$f$ be an integral ternary form isotropic over $\mathbb{Q}$ and $\mathbb{R}$-equivalent to $X_0^2 + X_1^2 - X_2^2$
(`hF`, with $L$ invertible). For no radius $0 \le r < 1$ does every point $\vec\alpha$ of the disc $\mathcal D$ have an
image $T(\vec\alpha)$, $T \in O^+(f)$, in the disc $\xi_0^2 + \xi_1^2 \le r^2$. (So no set $\mathcal C$ with property (i)
of Theorem 6.1 lies in such a disc; the proper orbits do not reach into the cusps at the rational isotropic points.) -/
theorem no_ball_fundamental_set_of_isotropic {Q : IntQF 3} (hQ : Q.IsotropicIn ℚ)
    {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det) (hF : realMat Q = Lᵀ * lorentz * L) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1) :
    ¬ ∀ α ∈ disc, ∃ T ∈ Siegel.AutPlus Q,
      (actD L (castM T.val) α) 0 ^ 2 + (actD L (castM T.val) α) 1 ^ 2 ≤ r ^ 2 := by
  intro hP
  obtain ⟨c, hc, hcb⟩ := null_lower_bound hL hF
  obtain ⟨v, hv0, hv⟩ := exists_int_isotropic_vec Q hQ
  set ν := L *ᵥ cast v with hν
  have hνnull : ν 0 ^ 2 + ν 1 ^ 2 = ν 2 ^ 2 := by
    apply null_of_lorB
    rw [← eval_eq_lorB hF, hv]
    simp
  have hν2 : c ≤ |ν 2| := hcb v hv0 hv
  obtain ⟨ε, hε, hεpos⟩ : ∃ ε : ℝ, |ε| = 1 ∧ 0 < ε * ν 2 := by
    rcases lt_or_gt_of_ne (show ν 2 ≠ 0 from fun h => by rw [h] at hν2; simp at hν2; linarith) with h | h
    · exact ⟨-1, by simp, by nlinarith⟩
    · exact ⟨1, by simp, by nlinarith⟩
  have hε2 : ε ^ 2 = 1 := by rw [← sq_abs, hε]; norm_num
  set n : Fin 3 → ℝ := ε • ν with hn
  have hn2 : 0 < n 2 := by simpa [hn] using hεpos
  have hnnull : n 0 ^ 2 + n 1 ^ 2 = n 2 ^ 2 := by
    simp only [hn, Pi.smul_apply, smul_eq_mul]
    linear_combination ε ^ 2 * hνnull
  set m : Fin 3 → ℝ := ![-(n 0) / (2 * n 2 ^ 2), -(n 1) / (2 * n 2 ^ 2), 1 / (2 * n 2)] with hm
  have hn2ne : n 2 ≠ 0 := hn2.ne'
  have hmnull : m 0 ^ 2 + m 1 ^ 2 = m 2 ^ 2 := by
    simp only [hm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    field_simp
    linear_combination hnnull
  have hnm : lorB n m = -1 := by
    simp only [lorB, hm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    field_simp
    linear_combination (-1 : ℝ) * hnnull
  have hm2 : 0 < m 2 := by simp [hm]; positivity
  have hnn : lorB n n = 0 := by simp only [lorB]; linarith
  have hmm : lorB m m = 0 := by simp only [lorB]; linarith
  set s : ℝ := c * (1 - r) / 4 with hs
  have h1r : 0 < 1 - r := by linarith
  have hspos : 0 < s := by rw [hs]; positivity
  set a : Fin 3 → ℝ := (1 / (2 * s)) • n + s • m with ha
  have haa : lorB a a = -1 := by
    rw [ha, lorB_comb, hnn, hmm, hnm]
    field_simp
    ring
  have ha2 : 0 < a 2 := by
    simp only [ha, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    positivity
  have hαD : projPt a ∈ disc := (projPt_mem_disc (by simp only [lorB] at haa; linarith)).2
  obtain ⟨T, hT, hball⟩ := hP _ hαD
  have hTaut : T ∈ Siegel.Aut Q := (Siegel.mem_autPlus_iff.mp hT).1
  have hPlor : (L * castM T.val * L⁻¹)ᵀ * lorentz * (L * castM T.val * L⁻¹) = lorentz :=
    isLor_conj_aut hL hF hTaut
  set P := L * castM T.val * L⁻¹ with hP'
  set y := P *ᵥ a with hy
  have hξ : actD L (castM T.val) (projPt a) = projPt y := by
    unfold actD flt
    rw [liftPt_projPt ha2.ne', Matrix.mulVec_smul, projPt_smul (inv_ne_zero ha2.ne')]
  have hyy : lorB y y = -1 := by rw [hy, lorB_mulVec hPlor, haa]
  set w : Fin 3 → ℤ := T.val *ᵥ v with hw
  have hw0 : w ≠ 0 := by
    intro h0
    apply hv0
    have : (T⁻¹).val *ᵥ (T.val *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [← this, ← hw, h0, Matrix.mulVec_zero]
  have hwQ : Q.eval w = 0 := by rw [hw, hTaut v, hv]
  have hPν : P *ᵥ ν = L *ᵥ cast w := (L_cast_mulVec' hL T.val v).symm
  have hPn : P *ᵥ n = ε • (L *ᵥ cast w) := by rw [hn, Matrix.mulVec_smul, hPν]
  have hpc : c ≤ |(P *ᵥ n) 2| := by
    rw [hPn]
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, hε, one_mul]
    exact hcb w hw0 hwQ
  set p := (P *ᵥ n) 2 with hp
  set q := (P *ᵥ m) 2 with hq
  have hPnn : lorB (P *ᵥ n) (P *ᵥ n) = 0 := by rw [lorB_mulVec hPlor, hnn]
  have hPmm : lorB (P *ᵥ m) (P *ᵥ m) = 0 := by rw [lorB_mulVec hPlor, hmm]
  have hPnm : lorB (P *ᵥ n) (P *ᵥ m) = -1 := by rw [lorB_mulVec hPlor, hnm]
  have hpq : 0 < p * q := null_pair_sign (null_of_lorB hPnn) (null_of_lorB hPmm) (by rw [hPnm]; norm_num)
  have hy2 : y 2 * (2 * s) = p + 2 * s ^ 2 * q := by
    have : y 2 = 1 / (2 * s) * p + s * q := by
      simp only [hy, ha, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rfl
    rw [this]
    field_simp
  have h2s : 0 < 2 * s := by positivity
  have hbig : c ≤ |y 2| * (2 * s) := by
    rcases lt_or_gt_of_ne (show p ≠ 0 from fun h => by rw [h] at hpq; simp at hpq) with hneg | hpos
    · have hqneg : q < 0 := by nlinarith
      have h4 : 2 * s ^ 2 * q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hqneg.le
      have h5 : y 2 * (2 * s) ≤ p := by rw [hy2]; linarith
      have h6 : (-(y 2)) * (2 * s) ≤ |y 2| * (2 * s) := mul_le_mul_of_nonneg_right (neg_le_abs _) h2s.le
      rw [abs_of_neg hneg] at hpc
      linarith
    · have hqpos : 0 < q := by nlinarith
      have h4 : 0 ≤ 2 * s ^ 2 * q := by positivity
      have h5 : p ≤ y 2 * (2 * s) := by rw [hy2]; linarith
      have h6 : y 2 * (2 * s) ≤ |y 2| * (2 * s) := mul_le_mul_of_nonneg_right (le_abs_self _) h2s.le
      rw [abs_of_pos hpos] at hpc
      linarith
  have hD : 2 ≤ |y 2| * (1 - r) := by
    have h1 : c * 2 ≤ c * (|y 2| * (1 - r)) := by
      rw [hs] at hbig
      linarith
    exact le_of_mul_le_mul_left h1 hc
  have hy2ne : y 2 ≠ 0 := by
    intro h0
    rw [h0] at hD
    simp at hD
    linarith
  rw [hξ] at hball
  simp only [projPt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, div_pow] at hball
  have hy2sq : 0 < y 2 ^ 2 := by positivity
  rw [← add_div, div_le_iff₀ hy2sq] at hball
  simp only [lorB] at hyy
  have hD2 : 4 ≤ (|y 2| * (1 - r)) ^ 2 := by nlinarith
  have h5 : (|y 2| * (1 - r)) ^ 2 = y 2 ^ 2 * (1 - r) ^ 2 := by rw [mul_pow, sq_abs]
  have hrr : r ^ 2 ≤ r := by nlinarith
  nlinarith [mul_nonneg (sq_nonneg (y 2)) (sub_nonneg.2 hrr)]

/-- **The Corollary to Theorem 6.1 is false for isotropic forms** (Cassels, Ch. 13, §6, p. 305): let $f$ be an integral
ternary form isotropic over $\mathbb{Q}$ and $\mathbb{R}$-equivalent to $X_0^2 + X_1^2 - X_2^2$. There is no finite
set $V$ of vertices in the open disc $\mathcal D$ whose convex hull $\mathcal C$ has property (i) of Theorem 6.1 (every
$\vec\alpha \in \mathcal D$ has $T(\vec\alpha) \in \mathcal C$ for some $T \in O^+(f)$), because such a hull lies in a disc
$\xi_0^2 + \xi_1^2 \le r^2$ with $r < 1$ (`convexHull_subset_ball`). So Theorem 6.1 fails for isotropic forms as stated
(vertices in $\mathcal D$); Cassels remarks that it holds if vertices on the boundary circle are allowed (not formalized
here: that needs the reduction theory of §5 and the cusps). -/
@[kb "cassels1978" "Ch. 13, §6, p. 305 (Thm. 6.1 and its Corollary fail for isotropic forms)"]
theorem no_fundamental_polygon_of_isotropic {Q : IntQF 3} (hQ : Q.IsotropicIn ℚ)
    {L : Matrix (Fin 3) (Fin 3) ℝ} (hL : IsUnit L.det) (hF : realMat Q = Lᵀ * lorentz * L) :
    ¬ ∃ V : Finset (Fin 2 → ℝ), (∀ v ∈ V, v ∈ disc) ∧
      ∀ α ∈ disc, ∃ T ∈ Siegel.AutPlus Q,
        actD L (castM T.val) α ∈ convexHull ℝ (V : Set (Fin 2 → ℝ)) := by
  rintro ⟨V, hV, hP⟩
  obtain ⟨r, hr0, hr1, hball⟩ := convexHull_subset_ball hV
  exact no_ball_fundamental_set_of_isotropic hQ hL hF hr0 hr1 fun α hα => by
    obtain ⟨T, hT, h⟩ := hP α hα
    exact ⟨T, hT, hball _ h⟩

end QuadFormsKB.Reduction
