import QuadFormsKB.Analysis.LatticePoisson

/-!
# Poisson summation with a quadratic polynomial weight

For a real symmetric positive definite $n \times n$ matrix $S$, $w \in \mathbb{C}$ with $\operatorname{Re} w > 0$ and
$\vec v \in \mathbb{R}^n$, differentiating the shifted theta inversion formula `tsum_gaussian_quadratic_shift`
twice in the shift $\vec h = t\vec v$ at $t = 0$ gives

$$\sum_{\vec x \in \mathbb{Z}^n}\Big(4\pi^2 w^2\,(\vec x^{\mathsf T} S\vec v)^2 - 2\pi w\,\vec v^{\mathsf T}S\vec v\Big)
    e^{-\pi w\,\vec x^{\mathsf T}S\vec x}
  = -4\pi^2\,\frac{(w^{-1})^{n/2}}{\sqrt{\det S}}\sum_{\vec y \in \mathbb{Z}^n}(\vec y\cdot\vec v)^2\,
    e^{-\pi w^{-1}\,\vec y^{\mathsf T}S^{-1}\vec y}$$

(`tsum_sq_gaussian_quadratic`). This is the transformation law behind theta series with a harmonic polynomial
coefficient of degree $2$ (Venkov; used for Chenevier–Lannes Proposition 2.3.2 in
`Literature/ChenevierLannes/Venkov060/`).

**Main results.**
* `summable_sq_mul_gaussian_quadratic`: absolute convergence of $\sum_{\vec x}(\vec x\cdot\vec a)^2
  e^{-\pi w\,\vec x^{\mathsf T}S\vec x}$ for every $\vec a \in \mathbb{R}^n$.
* `tsum_sq_gaussian_quadratic`: the identity above.

Sources: Serre, *A Course in Arithmetic*, Ch. VII §6 (Poisson formula) [unverified]; Ebeling, *Lattices and Codes*,
§3.1 (theta series with harmonic coefficients) [unverified].
-/

open Complex Matrix

namespace QuadFormsKB.Analysis

noncomputable section

variable {n : ℕ}

private lemma quad_nonneg {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) (y : Fin n → ℝ) :
    0 ≤ quadAtR S y := by
  have := hS.posSemidef.dotProduct_mulVec_nonneg y
  simpa [quadAtR] using this

private lemma dot_comm_S {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) (x u : Fin n → ℝ) :
    u ⬝ᵥ S *ᵥ x = x ⬝ᵥ S *ᵥ u := by
  have hsym : Sᵀ = S := by
    have := hS.isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, dotProduct_comm]

/-- Cauchy–Schwarz for the form of a positive definite matrix. -/
private lemma cs_quad {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) (x u : Fin n → ℝ) :
    (x ⬝ᵥ S *ᵥ u) ^ 2 ≤ quadAtR S x * quadAtR S u := by
  have key : ∀ s : ℝ, 0 ≤ quadAtR S u * (s * s) + (2 * (x ⬝ᵥ S *ᵥ u)) * s + quadAtR S x := by
    intro s
    have := quad_nonneg hS (x + s • u)
    simp only [quadAtR, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul] at this
    rw [dot_comm_S hS x u] at this
    simp only [quadAtR]
    nlinarith [this]
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

private lemma dot_sq_le {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) (x a : Fin n → ℝ) :
    (x ⬝ᵥ a) ^ 2 ≤ quadAtR S x * quadAtR S (S⁻¹ *ᵥ a) := by
  have hu : IsUnit S.det := hS.det_pos.ne'.isUnit
  have h1 : S *ᵥ (S⁻¹ *ᵥ a) = a := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have h := cs_quad hS x (S⁻¹ *ᵥ a)
  rwa [h1] at h

private lemma norm_gauss (w : ℂ) (q : ℝ) :
    ‖cexp (-Real.pi * w * (q : ℂ))‖ = Real.exp (-Real.pi * w.re * q) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

private lemma summable_pow_quad {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) (k : ℕ) {r : ℝ}
    (hr : 0 < r) :
    Summable fun x : Fin n → ℤ => quadAt S x ^ k * Real.exp (-r * quadAt S x) := by
  obtain ⟨C, hC⟩ := exists_bound_pow_mul_exp_neg_mul_of_nonneg k (half_pos hr)
  have hw : 0 < (((r / 2 / Real.pi : ℝ)) : ℂ).re := by
    rw [Complex.ofReal_re]; exact div_pos (half_pos hr) Real.pi_pos
  have hs := (summable_norm_gaussian_quadratic hS hw).mul_left C
  refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) hs
  · exact mul_nonneg (pow_nonneg (quad_nonneg hS _) _) (Real.exp_pos _).le
  · rw [norm_gauss, Complex.ofReal_re]
    have e : -Real.pi * (r / 2 / Real.pi) * quadAt S x = -(r / 2) * quadAt S x := by
      field_simp
    rw [e]
    have e2 : Real.exp (-r * quadAt S x) =
        Real.exp (-(r / 2) * quadAt S x) * Real.exp (-(r / 2) * quadAt S x) := by
      rw [← Real.exp_add]; congr 1; ring
    have := hC (quadAt S x) (quad_nonneg hS _)
    rw [e2, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le

private lemma summable_poly2 {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) {r : ℝ} (hr : 0 < r)
    (α β γ : ℝ) :
    Summable fun x : Fin n → ℤ =>
      (α + β * quadAt S x + γ * quadAt S x ^ 2) * Real.exp (-r * quadAt S x) := by
  have h0 := summable_pow_quad hS 0 hr
  have h1 := summable_pow_quad hS 1 hr
  have h2 := summable_pow_quad hS 2 hr
  exact (((h0.mul_left α).add (h1.mul_left β)).add (h2.mul_left γ)).congr (fun x => by ring)

private lemma phi_lower {q b c t : ℝ} (hq : 0 ≤ q) (hc : 0 ≤ c) (hb : b ^ 2 ≤ q * c)
    (ht : t ^ 2 ≤ 1) : q / 2 - c ≤ q + 2 * t * b + t ^ 2 * c := by
  have h1 : (2 * t * b) ^ 2 ≤ (q / 2 + 2 * t ^ 2 * c) ^ 2 := by
    nlinarith [sq_nonneg (q / 2 - 2 * t ^ 2 * c), mul_le_mul_of_nonneg_left hb (sq_nonneg t)]
  have h2 := (abs_le_of_sq_le_sq' h1 (by positivity)).1
  nlinarith [mul_le_mul_of_nonneg_right ht hc]

private lemma X_abs {q b c t : ℝ} (hq : 0 ≤ q) (hc : 0 ≤ c) (hb : b ^ 2 ≤ q * c)
    (ht : |t| ≤ 1) : |2 * b + 2 * t * c| ≤ q + 3 * c := by
  have h1 : (2 * b) ^ 2 ≤ (q + c) ^ 2 := by nlinarith [sq_nonneg (q - c)]
  have h2 : |2 * b| ≤ q + c := abs_le.mpr (abs_le_of_sq_le_sq' h1 (by positivity))
  have h3 : |2 * t * c| ≤ 2 * c := by
    rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_two]
    nlinarith [mul_le_mul_of_nonneg_right ht hc]
  calc |2 * b + 2 * t * c| ≤ |2 * b| + |2 * t * c| := abs_add_le _ _
    _ ≤ q + 3 * c := by linarith

private lemma two_deriv_tsum {ι : Type*} (g g1 g2 : ι → ℝ → ℂ) (u1 u2 : ι → ℝ)
    (h1 : Summable u1) (h2 : Summable u2)
    (hg : ∀ i, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt (g i) (g1 i t) t)
    (hg1 : ∀ i, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt (g1 i) (g2 i t) t)
    (hb1 : ∀ i, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ‖g1 i t‖ ≤ u1 i)
    (hb2 : ∀ i, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ‖g2 i t‖ ≤ u2 i)
    (h0 : Summable fun i => g i 0) :
    (∀ t ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt (fun s => ∑' i, g i s) (∑' i, g1 i t) t) ∧
    HasDerivAt (fun s => ∑' i, g1 i s) (∑' i, g2 i 0) 0 := by
  have h00 : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
  refine ⟨fun t ht => ?_, ?_⟩
  · exact hasDerivAt_tsum_of_isPreconnected h1 isOpen_Ioo isPreconnected_Ioo hg hb1 h00 h0 ht
  · exact hasDerivAt_tsum_of_isPreconnected h2 isOpen_Ioo isPreconnected_Ioo hg1 hb2 h00
      (Summable.of_norm_bounded h1 fun i => hb1 i 0 h00) h00

private lemma norm_aux1 (a b : ℂ) (X : ℝ) : ‖a * (b * (X : ℂ))‖ = ‖a‖ * (‖b‖ * |X|) := by
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]

private lemma norm_aux2 (a b : ℂ) (X Y : ℝ) :
    ‖a * ((b * (X : ℂ)) ^ 2 + b * (Y : ℂ))‖ ≤ ‖a‖ * (‖b‖ ^ 2 * X ^ 2 + ‖b‖ * |Y|) := by
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖(b * (X : ℂ)) ^ 2 + b * (Y : ℂ)‖ ≤ ‖(b * (X : ℂ)) ^ 2‖ + ‖b * (Y : ℂ)‖ := norm_add_le _ _
    _ = ‖b‖ ^ 2 * X ^ 2 + ‖b‖ * |Y| := by
      rw [norm_pow, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, mul_pow, sq_abs]

private lemma summable_sq_aux {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) {w : ℂ}
    (hw : 0 < w.re) (a : Fin n → ℝ) :
    Summable fun x : Fin n → ℤ =>
      ‖(((∑ i, (x i : ℝ) * a i : ℝ) : ℂ) ^ 2) * cexp (-Real.pi * w * (quadAt S x : ℂ))‖ := by
  have hr : 0 < Real.pi * w.re := mul_pos Real.pi_pos hw
  have hs := (summable_pow_quad hS 1 hr).mul_left (quadAtR S (S⁻¹ *ᵥ a))
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => ?_) hs
  rw [norm_mul, norm_pow, Complex.norm_real, norm_gauss, Real.norm_eq_abs, sq_abs]
  have h : (∑ i, (x i : ℝ) * a i) ^ 2 ≤ quadAt S x * quadAtR S (S⁻¹ *ᵥ a) :=
    dot_sq_le hS (fun i => (x i : ℝ)) a
  have he := Real.exp_pos (-Real.pi * w.re * quadAt S x)
  have e : -Real.pi * w.re * quadAt S x = -(Real.pi * w.re) * quadAt S x := by ring
  rw [e] at he ⊢
  calc (∑ i, (x i : ℝ) * a i) ^ 2 * Real.exp (-(Real.pi * w.re) * quadAt S x)
      ≤ (quadAt S x * quadAtR S (S⁻¹ *ᵥ a)) * Real.exp (-(Real.pi * w.re) * quadAt S x) :=
        mul_le_mul_of_nonneg_right h he.le
    _ = _ := by ring

/-! ### The left side: shifted Gaussian -/

private def bL (S : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (x : Fin n → ℤ) : ℝ :=
  (fun i => (x i : ℝ)) ⬝ᵥ S *ᵥ v

private def gL (S : Matrix (Fin n) (Fin n) ℝ) (w : ℂ) (v : Fin n → ℝ) (x : Fin n → ℤ) (t : ℝ) : ℂ :=
  cexp (-(Real.pi : ℂ) * w * ((quadAt S x + 2 * t * bL S v x + t ^ 2 * quadAtR S v : ℝ) : ℂ))

private def XL (S : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (x : Fin n → ℤ) (t : ℝ) : ℝ :=
  2 * bL S v x + 2 * t * quadAtR S v

private def g1L (S : Matrix (Fin n) (Fin n) ℝ) (w : ℂ) (v : Fin n → ℝ) (x : Fin n → ℤ) (t : ℝ) : ℂ :=
  gL S w v x t * (-(Real.pi : ℂ) * w * (XL S v x t : ℂ))

private def g2L (S : Matrix (Fin n) (Fin n) ℝ) (w : ℂ) (v : Fin n → ℝ) (x : Fin n → ℤ) (t : ℝ) : ℂ :=
  gL S w v x t * ((-(Real.pi : ℂ) * w * (XL S v x t : ℂ)) ^ 2 +
    (-(Real.pi : ℂ) * w) * ((2 * quadAtR S v : ℝ) : ℂ))

private lemma quad_shift_expand {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) (x : Fin n → ℤ)
    (v : Fin n → ℝ) (t : ℝ) :
    quadAtR S (fun i => (x i : ℝ) + (t • v) i) =
      quadAt S x + 2 * t * bL S v x + t ^ 2 * quadAtR S v := by
  have e : (fun i => (x i : ℝ) + (t • v) i) = (fun i => (x i : ℝ)) + t • v := rfl
  rw [e]
  simp only [quadAtR, quadAt, bL, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
    add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [dot_comm_S hS (fun i => (x i : ℝ)) v]
  ring

private lemma hasDerivAt_gL (S : Matrix (Fin n) (Fin n) ℝ) (w : ℂ) (v : Fin n → ℝ)
    (x : Fin n → ℤ) (t : ℝ) : HasDerivAt (gL S w v x) (g1L S w v x t) t := by
  have h : HasDerivAt (fun s : ℝ => quadAt S x + 2 * s * bL S v x + s ^ 2 * quadAtR S v)
      (XL S v x t) t := by
    have := ((((hasDerivAt_id' t).const_mul 2).mul_const (bL S v x)).const_add (quadAt S x)).add
      ((hasDerivAt_pow 2 t).mul_const (quadAtR S v))
    refine this.congr_deriv ?_
    simp only [XL]; push_cast; ring
  exact (h.ofReal_comp.const_mul (-(Real.pi : ℂ) * w)).cexp

private lemma hasDerivAt_g1L (S : Matrix (Fin n) (Fin n) ℝ) (w : ℂ) (v : Fin n → ℝ)
    (x : Fin n → ℤ) (t : ℝ) : HasDerivAt (g1L S w v x) (g2L S w v x t) t := by
  have h : HasDerivAt (fun s : ℝ => 2 * bL S v x + 2 * s * quadAtR S v) (2 * quadAtR S v) t := by
    have := (((hasDerivAt_id' t).const_mul 2).mul_const (quadAtR S v)).const_add (2 * bL S v x)
    refine this.congr_deriv ?_
    ring
  have h2 := (hasDerivAt_gL S w v x t).mul (h.ofReal_comp.const_mul (-(Real.pi : ℂ) * w))
  exact h2.congr_deriv (by simp only [g1L, g2L, XL]; ring)

private lemma L_side {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) {w : ℂ} (hw : 0 < w.re)
    (v : Fin n → ℝ) :
    (∀ t ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt (fun s => ∑' x : Fin n → ℤ, gL S w v x s)
        (∑' x : Fin n → ℤ, g1L S w v x t) t) ∧
    HasDerivAt (fun s => ∑' x : Fin n → ℤ, g1L S w v x s) (∑' x : Fin n → ℤ, g2L S w v x 0) 0 := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.pi * w.re / 2 := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact div_pos (mul_pos Real.pi_pos hw) two_pos
  have hr2 : Real.pi * w.re = 2 * r := by rw [hr]; ring
  have hc0 : 0 ≤ quadAtR S v := quad_nonneg hS v
  have hq0 : ∀ x : Fin n → ℤ, 0 ≤ quadAt S x := fun x => quad_nonneg hS _
  have hbc : ∀ x : Fin n → ℤ, (bL S v x) ^ 2 ≤ quadAt S x * quadAtR S v :=
    fun x => cs_quad hS _ v
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ‖-(Real.pi : ℂ) * w‖ := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; exact norm_nonneg _
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (2 * r * quadAtR S v) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hE]; exact (Real.exp_pos _).le
  have hbase : ∀ x : Fin n → ℤ, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      ‖gL S w v x t‖ ≤ E * Real.exp (-r * quadAt S x) := by
    intro x t ht
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    have h1 := phi_lower (hq0 x) hc0 (hbc x) ht2
    unfold gL
    rw [norm_gauss, hE, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : -Real.pi * w.re = -(2 * r) := by rw [← hr2]; ring
    rw [this]
    nlinarith [mul_nonneg hr0.le (sub_nonneg.2 h1)]
  have hX : ∀ x : Fin n → ℤ, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      |XL S v x t| ≤ quadAt S x + 3 * quadAtR S v := by
    intro x t ht
    exact X_abs (hq0 x) hc0 (hbc x) (abs_le.2 ⟨ht.1.le, ht.2.le⟩)
  have hu1 : Summable fun x : Fin n → ℤ =>
      E * (M * (quadAt S x + 3 * quadAtR S v)) * Real.exp (-r * quadAt S x) :=
    (summable_poly2 hS hr0 (E * M * (3 * quadAtR S v)) (E * M) 0).congr fun x => by ring
  have hu2 : Summable fun x : Fin n → ℤ =>
      E * (M ^ 2 * (quadAt S x + 3 * quadAtR S v) ^ 2 + M * (2 * quadAtR S v)) *
        Real.exp (-r * quadAt S x) :=
    (summable_poly2 hS hr0 (E * (9 * M ^ 2 * quadAtR S v ^ 2 + 2 * M * quadAtR S v))
      (E * (6 * M ^ 2 * quadAtR S v)) (E * M ^ 2)).congr fun x => by ring
  have hb1 : ∀ x : Fin n → ℤ, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ‖g1L S w v x t‖ ≤
      E * (M * (quadAt S x + 3 * quadAtR S v)) * Real.exp (-r * quadAt S x) := by
    intro x t ht
    unfold g1L
    rw [norm_aux1, ← hM]
    calc ‖gL S w v x t‖ * (M * |XL S v x t|)
        ≤ (E * Real.exp (-r * quadAt S x)) * (M * (quadAt S x + 3 * quadAtR S v)) :=
          mul_le_mul (hbase x t ht) (mul_le_mul_of_nonneg_left (hX x t ht) hM0)
            (mul_nonneg hM0 (abs_nonneg _)) (mul_nonneg hE0 (Real.exp_pos _).le)
      _ = _ := by ring
  have hb2 : ∀ x : Fin n → ℤ, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ‖g2L S w v x t‖ ≤
      E * (M ^ 2 * (quadAt S x + 3 * quadAtR S v) ^ 2 + M * (2 * quadAtR S v)) *
        Real.exp (-r * quadAt S x) := by
    intro x t ht
    unfold g2L
    refine (norm_aux2 _ _ _ _).trans ?_
    rw [← hM]
    have hsq : (XL S v x t) ^ 2 ≤ (quadAt S x + 3 * quadAtR S v) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) (hX x t ht) 2
      rwa [sq_abs] at this
    have habs : |2 * quadAtR S v| = 2 * quadAtR S v := abs_of_nonneg (by linarith)
    rw [habs]
    calc ‖gL S w v x t‖ * (M ^ 2 * XL S v x t ^ 2 + M * (2 * quadAtR S v))
        ≤ (E * Real.exp (-r * quadAt S x)) *
            (M ^ 2 * (quadAt S x + 3 * quadAtR S v) ^ 2 + M * (2 * quadAtR S v)) :=
          mul_le_mul (hbase x t ht) (by nlinarith [pow_nonneg hM0 2]) (by
            have := sq_nonneg (XL S v x t)
            positivity) (mul_nonneg hE0 (Real.exp_pos _).le)
      _ = _ := by ring
  have h0 : Summable fun x : Fin n → ℤ => gL S w v x 0 :=
    Summable.of_norm_bounded ((summable_poly2 hS hr0 E 0 0).congr fun x => by ring)
      fun x => hbase x 0 (by norm_num)
  exact two_deriv_tsum (fun x s => gL S w v x s) (fun x s => g1L S w v x s)
    (fun x s => g2L S w v x s) _ _ hu1 hu2 (fun x t _ => hasDerivAt_gL S w v x t)
    (fun x t _ => hasDerivAt_g1L S w v x t) hb1 hb2 h0

/-! ### The right side: dual lattice -/

private def KR (S : Matrix (Fin n) (Fin n) ℝ) (w : ℂ) (y : Fin n → ℤ) : ℂ :=
  cexp (-Real.pi * w⁻¹ * (quadAt S⁻¹ y : ℂ))

private def DR (v : Fin n → ℝ) (y : Fin n → ℤ) : ℂ :=
  2 * Real.pi * I * ((∑ i, (y i : ℝ) * v i : ℝ) : ℂ)

private def gR (S : Matrix (Fin n) (Fin n) ℝ) (w : ℂ) (v : Fin n → ℝ) (y : Fin n → ℤ) (t : ℝ) : ℂ :=
  KR S w y * cexp (DR v y * (t : ℂ))

private def g1R (S : Matrix (Fin n) (Fin n) ℝ) (w : ℂ) (v : Fin n → ℝ) (y : Fin n → ℤ) (t : ℝ) : ℂ :=
  DR v y * (KR S w y * cexp (DR v y * (t : ℂ)))

private def g2R (S : Matrix (Fin n) (Fin n) ℝ) (w : ℂ) (v : Fin n → ℝ) (y : Fin n → ℤ) (t : ℝ) : ℂ :=
  DR v y * (DR v y * (KR S w y * cexp (DR v y * (t : ℂ))))

private lemma norm_exp_DR (v : Fin n → ℝ) (y : Fin n → ℤ) (t : ℝ) :
    ‖cexp (DR v y * (t : ℂ))‖ = 1 := by
  have : DR v y * (t : ℂ) = ((2 * Real.pi * (∑ i, (y i : ℝ) * v i) * t : ℝ) : ℂ) * I := by
    unfold DR; push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

private lemma norm_DR (v : Fin n → ℝ) (y : Fin n → ℤ) :
    ‖DR v y‖ = 2 * Real.pi * |∑ i, (y i : ℝ) * v i| := by
  unfold DR
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [show ‖(2 : ℂ)‖ = 2 by simp]

private lemma hasDerivAt_gR (S : Matrix (Fin n) (Fin n) ℝ) (w : ℂ) (v : Fin n → ℝ)
    (y : Fin n → ℤ) (t : ℝ) : HasDerivAt (gR S w v y) (g1R S w v y t) t := by
  have h : HasDerivAt (fun s : ℝ => cexp (DR v y * (s : ℂ)))
      (cexp (DR v y * (t : ℂ)) * (DR v y * ((1 : ℝ) : ℂ))) t :=
    ((hasDerivAt_id' t).ofReal_comp.const_mul _).cexp
  exact (h.const_mul (KR S w y)).congr_deriv (by simp only [g1R]; push_cast; ring)

private lemma hasDerivAt_g1R (S : Matrix (Fin n) (Fin n) ℝ) (w : ℂ) (v : Fin n → ℝ)
    (y : Fin n → ℤ) (t : ℝ) : HasDerivAt (g1R S w v y) (g2R S w v y t) t := by
  have := (hasDerivAt_gR S w v y t).const_mul (DR v y)
  exact this.congr_deriv (by simp only [g1R, g2R])

private lemma R_side {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) {w : ℂ} (hw : 0 < w.re)
    (v : Fin n → ℝ) :
    (∀ t ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt (fun s => ∑' y : Fin n → ℤ, gR S w v y s)
        (∑' y : Fin n → ℤ, g1R S w v y t) t) ∧
    HasDerivAt (fun s => ∑' y : Fin n → ℤ, g1R S w v y s) (∑' y : Fin n → ℤ, g2R S w v y 0) 0 := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hwi : 0 < (w⁻¹).re := by
    rw [Complex.inv_re]; exact div_pos hw (Complex.normSq_pos.2 hw0)
  have hSi : S⁻¹.PosDef := hS.inv
  have hK : Summable fun y : Fin n → ℤ => ‖KR S w y‖ := summable_norm_gaussian_quadratic hSi hwi
  have hQ : Summable fun y : Fin n → ℤ =>
      ‖(((∑ i, (y i : ℝ) * v i : ℝ) : ℂ) ^ 2) * KR S w y‖ :=
    summable_sq_aux hSi hwi v
  have hnQ : ∀ y : Fin n → ℤ, ‖(((∑ i, (y i : ℝ) * v i : ℝ) : ℂ) ^ 2) * KR S w y‖ =
      (∑ i, (y i : ℝ) * v i) ^ 2 * ‖KR S w y‖ := by
    intro y
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  refine two_deriv_tsum (fun y s => gR S w v y s) (fun y s => g1R S w v y s)
    (fun y s => g2R S w v y s)
    (fun y => Real.pi * (‖KR S w y‖ + ‖(((∑ i, (y i : ℝ) * v i : ℝ) : ℂ) ^ 2) * KR S w y‖))
    (fun y => 4 * Real.pi ^ 2 * ‖(((∑ i, (y i : ℝ) * v i : ℝ) : ℂ) ^ 2) * KR S w y‖)
    ((hK.add hQ).mul_left Real.pi) (hQ.mul_left (4 * Real.pi ^ 2)) ?_ ?_ ?_ ?_ ?_
  · intro y t _; exact hasDerivAt_gR S w v y t
  · intro y t _; exact hasDerivAt_g1R S w v y t
  · intro y t _
    unfold g1R
    rw [norm_mul, norm_mul, norm_exp_DR, norm_DR, hnQ, mul_one]
    rw [← sq_abs (∑ i, (y i : ℝ) * v i)]
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (norm_nonneg (KR S w y)))
      (sq_nonneg (|∑ i, (y i : ℝ) * v i| - 1))]
  · intro y t _
    unfold g2R
    rw [norm_mul, norm_mul, norm_mul, norm_exp_DR, norm_DR, hnQ, mul_one]
    apply le_of_eq
    rw [← sq_abs (∑ i, (y i : ℝ) * v i)]
    ring
  · refine Summable.of_norm_bounded hK fun y => ?_
    simp [gR]

/-- **Absolute convergence with a square-of-a-linear-form weight**: for $S$ real positive definite,
$\operatorname{Re} w > 0$ and $\vec a \in \mathbb{R}^n$, $\sum_{\vec x \in \mathbb{Z}^n}
\big|(\sum_i x_i a_i)^2\, e^{-\pi w\,\vec x^{\mathsf T}S\vec x}\big| < \infty$. -/
theorem summable_sq_mul_gaussian_quadratic {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) {w : ℂ}
    (hw : 0 < w.re) (a : Fin n → ℝ) :
    Summable fun x : Fin n → ℤ =>
      ‖(((∑ i, (x i : ℝ) * a i : ℝ) : ℂ) ^ 2) * cexp (-Real.pi * w * (quadAt S x : ℂ))‖ :=
  summable_sq_aux hS hw a

/-- **Theta inversion with a quadratic weight** (second derivative of `tsum_gaussian_quadratic_shift` in the shift
direction $\vec v$ at $\vec h = 0$): for $S$ real symmetric positive definite, $\operatorname{Re} w > 0$,
$\vec v \in \mathbb{R}^n$,
$$\sum_{\vec x}\Big(4\pi^2w^2(\vec x^{\mathsf T}S\vec v)^2 - 2\pi w\,\vec v^{\mathsf T}S\vec v\Big)
  e^{-\pi w\,\vec x^{\mathsf T}S\vec x}
  = -4\pi^2\,\frac{(w^{-1})^{n/2}}{\sqrt{\det S}}\sum_{\vec y}(\vec y\cdot\vec v)^2\,e^{-\pi w^{-1}\,\vec y^{\mathsf T}S^{-1}\vec y},$$
principal branch of $(w^{-1})^{n/2}$. -/
@[kb "serre1973" "Ch. VII §6.1, Poisson formula [unverified]"]
theorem tsum_sq_gaussian_quadratic {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) {w : ℂ}
    (hw : 0 < w.re) (v : Fin n → ℝ) :
    ∑' x : Fin n → ℤ, (4 * (Real.pi : ℂ) ^ 2 * w ^ 2 *
          ((((fun i => (x i : ℝ)) ⬝ᵥ S *ᵥ v : ℝ) : ℂ)) ^ 2 - 2 * Real.pi * w * (quadAtR S v : ℂ)) *
        cexp (-Real.pi * w * (quadAt S x : ℂ)) =
      -4 * (Real.pi : ℂ) ^ 2 * (((Real.sqrt S.det)⁻¹ : ℝ) * w⁻¹ ^ ((n : ℂ) / 2)) *
        ∑' y : Fin n → ℤ, ((∑ i, (y i : ℝ) * v i : ℝ) : ℂ) ^ 2 *
          cexp (-Real.pi * w⁻¹ * (quadAt S⁻¹ y : ℂ)) := by
  classical
  obtain ⟨hL1, hL2⟩ := L_side hS hw v
  obtain ⟨hR1, hR2⟩ := R_side hS hw v
  have hLR : ∀ t : ℝ, ∑' x : Fin n → ℤ, gL S w v x t =
      (((Real.sqrt S.det)⁻¹ : ℝ) * w⁻¹ ^ ((n : ℂ) / 2)) * ∑' y : Fin n → ℤ, gR S w v y t := by
    intro t
    have h := tsum_gaussian_quadratic_shift hS hw (t • v)
    have e1 : ∀ x : Fin n → ℤ, cexp (-Real.pi * w *
        (quadAtR S (fun i => (x i : ℝ) + (t • v) i) : ℂ)) = gL S w v x t := fun x => by
      rw [quad_shift_expand hS]; rfl
    have e2 : ∀ y : Fin n → ℤ, cexp (-Real.pi * w⁻¹ * (quadAt S⁻¹ y : ℂ)) *
        cexp (2 * Real.pi * I * ((∑ i, (y i : ℝ) * (t • v) i : ℝ) : ℂ)) = gR S w v y t := by
      intro y
      have hs : (∑ i, (y i : ℝ) * (t • v) i) = t * ∑ i, (y i : ℝ) * v i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by simp [Pi.smul_apply]; ring)
      rw [hs]
      unfold gR KR DR
      congr 2
      push_cast; ring
    simp_rw [e1, e2] at h
    exact h
  have hfun : (fun s => ∑' x : Fin n → ℤ, gL S w v x s) = fun s =>
      (((Real.sqrt S.det)⁻¹ : ℝ) * w⁻¹ ^ ((n : ℂ) / 2)) * ∑' y : Fin n → ℤ, gR S w v y s :=
    funext hLR
  have hEq : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ∑' x : Fin n → ℤ, g1L S w v x t =
      (((Real.sqrt S.det)⁻¹ : ℝ) * w⁻¹ ^ ((n : ℂ) / 2)) * ∑' y : Fin n → ℤ, g1R S w v y t := by
    intro t ht
    have a := hL1 t ht
    have b := (hR1 t ht).const_mul (((Real.sqrt S.det)⁻¹ : ℝ) * w⁻¹ ^ ((n : ℂ) / 2))
    rw [hfun] at a
    exact a.unique b
  have hev : (fun t => (((Real.sqrt S.det)⁻¹ : ℝ) * w⁻¹ ^ ((n : ℂ) / 2)) *
        ∑' y : Fin n → ℤ, g1R S w v y t) =ᶠ[nhds (0 : ℝ)]
      fun t => ∑' x : Fin n → ℤ, g1L S w v x t := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)]
      with t ht
    exact (hEq t ht).symm
  have key := (hL2.congr_of_eventuallyEq hev).unique
    (hR2.const_mul (((Real.sqrt S.det)⁻¹ : ℝ) * w⁻¹ ^ ((n : ℂ) / 2)))
  have hL : ∀ x : Fin n → ℤ, (4 * (Real.pi : ℂ) ^ 2 * w ^ 2 *
          ((((fun i => (x i : ℝ)) ⬝ᵥ S *ᵥ v : ℝ) : ℂ)) ^ 2 - 2 * Real.pi * w * (quadAtR S v : ℂ)) *
        cexp (-Real.pi * w * (quadAt S x : ℂ)) = g2L S w v x 0 := by
    intro x
    simp only [g2L, XL, gL, bL, mul_zero, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    push_cast
    ring
  have hR : ∀ y : Fin n → ℤ, g2R S w v y 0 = -4 * (Real.pi : ℂ) ^ 2 *
      (((∑ i, (y i : ℝ) * v i : ℝ) : ℂ) ^ 2 * cexp (-Real.pi * w⁻¹ * (quadAt S⁻¹ y : ℂ))) := by
    intro y
    simp only [g2R, KR, DR, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
    ring_nf
    simp [Complex.I_sq]
  calc _ = ∑' x : Fin n → ℤ, g2L S w v x 0 := tsum_congr hL
    _ = _ := key
    _ = _ := by
      simp_rw [hR]
      rw [tsum_mul_left]
      ring

end

end QuadFormsKB.Analysis
