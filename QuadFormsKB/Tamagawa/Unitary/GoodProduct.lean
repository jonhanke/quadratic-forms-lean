import QuadFormsKB.Tamagawa.Unitary.GoodPlaces
import QuadFormsKB.Tamagawa.Unitary.Adelic
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryMeasure
import QuadFormsKB.Binary.RelDensities
import QuadFormsKB.Analysis.NFEulerProduct
import QuadFormsKB.Siegel.NFMainTerm

/-!
# The product $\prod_v\beta^h_v/\lambda_v$ converges

**Layer:** $F$ a number field, $E/F$ a quadratic extension with character $\chi = \chi_{E/F}$ (`chiE F E`), and
$\theta\in\mathcal O_E$ with $\bar\theta = -\theta$, $\theta^2 = -D$ (so $E = F(\theta)$ and $\theta$ plays the role of $\omega$);
$H_0$ an integral hermitian $m\times m$ matrix over $\mathcal O_F[\omega]$, $\omega^2 = -D$, $\det H_0\ne0$. For a finite
place $v$ write $q = N\mathfrak p_v$ and $\lambda_v = L_v(1,\chi)^{-1} = 1-\chi(v)q^{-1}$ (`lamL`).

**Proves**
* `hermDensity_eq_good`: at every place $v\nmid2D\,N(\det H_0)$, the hermitian local density is
  $\beta^h_v(\Lambda,\Lambda) = \prod_{i=1}^m\bigl(1-(\chi(v)/q)^i\bigr)$
  (one formula for the split ($\chi(v) = 1$, $|GL_m(\mathbb F_q)|q^{-m^2}$) and inert ($\chi(v) = -1$,
  $|U_m(\mathbb F_q)|q^{-m^2}$) places of `GoodPlaces.lean`);
* **`hermDensity_div_lamL_eq_good`**: for $m\ge1$, $\beta^h_v/\lambda_v = \prod_{i=2}^m\bigl(1-(\chi(v)/q)^i\bigr)$
  (Gan–Hanke–Yu 2001, (2.11) for $U(V)$: $L_v(M^\vee(1))^{-1} = \prod_{i=1}^m L_v(i,\chi^i)^{-1}$, whose $i = 1$ factor is the
  convergence factor);
* **`multipliable_hermDensity_div_lamL`**: for $m\ge1$, $\prod_v\beta^h_v/\lambda_v$ converges unconditionally
  (`Multipliable`), so `finFactorU D H₀ (lamL (chiE F E))` (the normalizing constant of `muFinU` in `muTamU`) is a genuine
  convergent Euler product: `hasProd_finFactorU`.

*The hypothesis $m\ge1$.* For $m = 0$ the group is trivial, $\beta^h_v = 1$ and $\prod_v\lambda_v^{-1} = \prod_vL_v(1,\chi)$ is
not absolutely convergent; Weil's convergence factors $L_v(1,\chi)$ are those of a group whose character module is
that of $U(1)$, which needs $m\ge1$.
-/

open scoped QuadraticAlgebra
open Filter

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Unitary

open NumberField IsDedekindDomain QuadFormsKB.NFEuler QuadFormsKB.Tamagawa.Measure.Weil

/-! ### Elementary products -/

/-- $\bigl|\prod_{i<n}(1-x^{i+2})-1\bigr|\le n\,2^n x^2$ for $|x|\le1$. -/
theorem abs_prod_one_sub_pow_sub_one_le {x : ℝ} (hx : |x| ≤ 1) (n : ℕ) :
    |∏ i ∈ Finset.range n, (1 - x ^ (i + 2)) - 1| ≤ n * 2 ^ n * x ^ 2 := by
  have hP : ∀ n : ℕ, |∏ i ∈ Finset.range n, (1 - x ^ (i + 2))| ≤ 2 ^ n := by
    intro n
    rw [Finset.abs_prod]
    calc ∏ i ∈ Finset.range n, |1 - x ^ (i + 2)| ≤ ∏ _i ∈ Finset.range n, (2 : ℝ) := by
          gcongr with i hi
          have h1 := pow_le_one₀ (abs_nonneg x) hx (n := i + 2)
          calc |1 - x ^ (i + 2)| ≤ |1| + |x ^ (i + 2)| := abs_sub _ _
            _ ≤ 2 := by rw [abs_one, abs_pow]; linarith
      _ = 2 ^ n := by simp
  have hx2 : ∀ i : ℕ, |x ^ (i + 2)| ≤ x ^ 2 := by
    intro i
    calc |x ^ (i + 2)| = |x| ^ i * |x| ^ 2 := by rw [abs_pow, pow_add]
      _ ≤ 1 * |x| ^ 2 := mul_le_mul_of_nonneg_right (pow_le_one₀ (abs_nonneg _) hx) (by positivity)
      _ = x ^ 2 := by rw [one_mul, sq_abs]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ]
    set P := ∏ i ∈ Finset.range n, (1 - x ^ (i + 2))
    have e : P * (1 - x ^ (n + 2)) - 1 = (P - 1) - P * x ^ (n + 2) := by ring
    rw [e]
    have h0 : 0 ≤ ((n : ℝ) + 1) * 2 ^ n * x ^ 2 := by positivity
    calc |(P - 1) - P * x ^ (n + 2)| ≤ |P - 1| + |P * x ^ (n + 2)| := abs_sub _ _
      _ ≤ n * 2 ^ n * x ^ 2 + 2 ^ n * x ^ 2 := by
          gcongr
          rw [abs_mul]; exact mul_le_mul (hP n) (hx2 n) (abs_nonneg _) (by positivity)
      _ ≤ ((n + 1 : ℕ) : ℝ) * 2 ^ (n + 1) * x ^ 2 := by
          push_cast
          have e2 : ((n : ℝ) + 1) * 2 ^ (n + 1) * x ^ 2 = 2 * (((n : ℝ) + 1) * 2 ^ n * x ^ 2) := by ring
          have e3 : (n : ℝ) * 2 ^ n * x ^ 2 + 2 ^ n * x ^ 2 = ((n : ℝ) + 1) * 2 ^ n * x ^ 2 := by ring
          rw [e2, e3]; linarith

/-- $\prod_{i<n+1}(1-x^{i+1})/(1-x) = \prod_{i<n}(1-x^{i+2})$ for $x\ne1$. -/
theorem prod_one_sub_pow_div (x : ℝ) (hx : x ≠ 1) (n : ℕ) :
    (∏ i ∈ Finset.range (n + 1), (1 - x ^ (i + 1))) / (1 - x) = ∏ i ∈ Finset.range n, (1 - x ^ (i + 2)) := by
  have h : (1 - x) ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  rw [Finset.prod_range_succ', zero_add, pow_one, mul_div_assoc, div_self h, mul_one]

/-- **$|GL_m(\mathbb F_q)|/q^{m^2} = \prod_{i=1}^m(1-q^{-i})$**, from Mathlib's $\prod_{i<m}(q^m-q^i)$. -/
theorem prod_GL_div (q : ℕ) (hq : 0 < q) (m : ℕ) :
    (∏ i : Fin m, ((q : ℝ) ^ m - (q : ℝ) ^ (i : ℕ))) / (q : ℝ) ^ m ^ 2 =
      ∏ i ∈ Finset.range m, (1 - (1 / (q : ℝ)) ^ (i + 1)) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [Fin.prod_univ_eq_prod_range (fun i => (q : ℝ) ^ m - (q : ℝ) ^ i)]
  have hfac : ∀ i ∈ Finset.range m, (q : ℝ) ^ m - (q : ℝ) ^ i = (q : ℝ) ^ m * (1 - (1 / (q : ℝ)) ^ (m - i)) := by
    intro i hi
    have hi' : i ≤ m := (Finset.mem_range.1 hi).le
    rw [mul_sub, mul_one, one_div_pow, mul_one_div, pow_sub₀ _ hq0 hi']
    field_simp
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul, ← sq,
    mul_div_cancel_left₀ _ (pow_ne_zero _ hq0)]
  rw [← Finset.prod_range_reflect (fun i => 1 - (1 / (q : ℝ)) ^ (m - i)) m]
  refine Finset.prod_congr rfl fun j hj => ?_
  have : m - (m - 1 - j) = j + 1 := by have := Finset.mem_range.1 hj; omega
  rw [this]

theorem exp_inert (m : ℕ) : m * (m - 1) / 2 + ∑ i ∈ Finset.range m, (i + 1) = m ^ 2 := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one, ← Finset.sum_range_id]
  have hS := Finset.sum_range_id_mul_two m
  cases m with
  | zero => simp
  | succ k =>
    simp only [Nat.add_sub_cancel] at hS ⊢
    nlinarith [hS]

/-- **$q^{m(m-1)/2}\prod_{i=1}^m(q^i-(-1)^i)/q^{m^2} = \prod_{i=1}^m(1-(-1/q)^i)$** (the inert value). -/
theorem prod_U_div (q : ℝ) (hq : q ≠ 0) (m : ℕ) :
    (q ^ (m * (m - 1) / 2) * ∏ i ∈ Finset.range m, (q ^ (i + 1) - (-1) ^ (i + 1))) / q ^ m ^ 2 =
      ∏ i ∈ Finset.range m, (1 - (-1 / q) ^ (i + 1)) := by
  have hfac : ∀ i ∈ Finset.range m, q ^ (i + 1) - (-1) ^ (i + 1) = q ^ (i + 1) * (1 - (-1 / q) ^ (i + 1)) := by
    intro i _
    rw [mul_sub, mul_one, div_pow, mul_div_cancel₀ _ (pow_ne_zero _ hq)]
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← mul_assoc, ← pow_add,
    exp_inert, mul_div_cancel_left₀ _ (pow_ne_zero _ hq)]

/-! ### The good places -/

variable {F : Type} [Field F] [NumberField F] (D : 𝓞 F) {m : ℕ} (H₀ : Matrix (Fin m) (Fin m) (QuadO D))

theorem resQ_det (v : HeightOneSpectrum (𝓞 F)) :
    (H₀.map (resQ D v 1)).det = resQ D v 1 H₀.det := by
  rw [RingHom.map_det]; rfl

theorem norm_resQ (v : HeightOneSpectrum (𝓞 F)) (z : QuadO D) :
    QuadraticAlgebra.norm (resQ D v 1 z) = Ideal.Quotient.mk _ (QuadraticAlgebra.norm z) := by
  simp [QuadraticAlgebra.norm_def, resQ]

/-- The reduction of $\det H_0$ is a unit at every $v$ with $N(\det H_0)\notin\mathfrak p_v$. -/
theorem isUnit_det_resQ (v : HeightOneSpectrum (𝓞 F)) (hN : QuadraticAlgebra.norm H₀.det ∉ v.asIdeal) :
    IsUnit (H₀.map (resQ D v 1)).det := by
  rw [resQ_det, QuadraticAlgebra.isUnit_iff_norm_isUnit, norm_resQ]
  show IsUnit (Ideal.Quotient.mk _ _ : resField v)
  rw [isUnit_iff_ne_zero, Ne, Ideal.Quotient.eq_zero_iff_mem, pow_one]
  exact hN

theorem isSquare_res_iff (v : HeightOneSpectrum (𝓞 F)) (δ : 𝓞 F) :
    IsSquare (Ideal.Quotient.mk (v.asIdeal ^ 1) δ : resField v) ↔ ∃ c : 𝓞 F, δ - c ^ 2 ∈ v.asIdeal := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨c, ?_⟩
    rw [← pow_one v.asIdeal, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hy, sq, sub_self]
  · rintro ⟨c, hc⟩
    refine ⟨Ideal.Quotient.mk _ c, ?_⟩
    rw [← map_mul, Ideal.Quotient.eq, pow_one, ← sq]
    exact hc

/-- $N(z)\ne0$ for $z\ne0$ in $\mathcal O_F[\omega]$ when $-D$ is not a square in $F$. -/
theorem norm_ne_zero_quadO (hsq : ¬ IsSquare (algebraMap (𝓞 F) F (-D))) {z : QuadO D} (hz : z ≠ 0) :
    QuadraticAlgebra.norm z ≠ 0 := by
  intro h0
  rw [QuadraticAlgebra.norm_def] at h0
  have h1 : (algebraMap (𝓞 F) F z.re) ^ 2 + algebraMap (𝓞 F) F D * (algebraMap (𝓞 F) F z.im) ^ 2 = 0 := by
    have := congrArg (algebraMap (𝓞 F) F) h0
    simp only [map_sub, map_add, map_mul, map_zero, map_neg] at this
    linear_combination this
  by_cases him : z.im = 0
  · apply hz
    have hre : algebraMap (𝓞 F) F z.re = 0 := by
      rw [him, map_zero] at h1; simpa using h1
    have hre' : z.re = 0 := (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).1 hre
    exact QuadraticAlgebra.ext hre' him
  · apply hsq
    have hi : algebraMap (𝓞 F) F z.im ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)]; exact him
    refine ⟨algebraMap (𝓞 F) F z.re / algebraMap (𝓞 F) F z.im, ?_⟩
    rw [map_neg]
    field_simp
    linear_combination -h1

/-- $\det H_0\ne0$ in $\mathcal O_F[\omega]$ when its image in $E = F(\omega)$ is nonzero. -/
theorem det_ne_zero_of_HK (hdet : (HK D F H₀).det ≠ 0) : H₀.det ≠ 0 := by
  intro h
  apply hdet
  rw [HK, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]

variable {E : Type} [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E]

/-- **$\beta^h_v = \prod_{i=1}^m(1-(\chi(v)/q)^i)$ at the good places** $v\nmid2D\,N(\det H_0)$, $\chi = \chi_{E/F}$, $E = F(\theta)$,
$\theta^2 = -D$. -/
@[kb "ganhankeyu2001" "(2.11), p. 104 and Table 1 (L_v(M^∨(1))^{-1} = q^{-dim}#H̄_v(𝔽_q), H_v = GL_m or U_m)"]
theorem hermDensity_eq_good (hH : H₀.IsHermitian) {θ : 𝓞 E} (hθ : Binary.Rel.conjO F E θ = -θ)
    (hθD : algebraMap (𝓞 F) (𝓞 E) (-D) = θ ^ 2) (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal)
    (hDv : D ∉ v.asIdeal) (hN : QuadraticAlgebra.norm H₀.det ∉ v.asIdeal) :
    hermDensity D H₀ v = ∏ i ∈ Finset.range m, (1 - (chiE F E v / (normP v : ℝ)) ^ (i + 1)) := by
  have hdet := isUnit_det_resQ D H₀ v hN
  have hδ : -D ∉ v.asIdeal := fun h => hDv (by simpa using v.asIdeal.neg_mem h)
  obtain ⟨h0, hiff⟩ := Binary.Rel.relChar_eq_one_iff_sq hθ hθD h2 hδ
  have hq : 0 < (normP v : ℕ) := by have := two_le_normP v; omega
  by_cases hsq : ∃ c : 𝓞 F, -D - c ^ 2 ∈ v.asIdeal
  · -- split
    have hχ : chiE F E v = 1 := by unfold chiE; rw [hiff.2 hsq]; norm_num
    have hne : (Ideal.Quotient.mk (v.asIdeal ^ 1) (-D) : resField v) ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem, pow_one]; exact hδ
    rw [hermDensity_eq_split D v H₀ hH h2 hdet ((isSquare_res_iff v (-D)).2 hsq) hne, Matrix.card_GL_field,
      card_resField, hχ]
    rw [Nat.cast_prod]
    have := prod_GL_div (normP v) hq m
    convert this using 3 with i
    rw [Nat.cast_sub (Nat.pow_le_pow_right hq i.2.le)]
    push_cast; rfl
  · -- inert
    have hχ : chiE F E v = -1 := by
      unfold chiE
      rcases Binary.Rel.relChar_trichotomy (E := E) v with h | h | h
      · exact absurd (hiff.1 h) hsq
      · rw [h]; norm_num
      · exact absurd h h0
    rw [hermDensity_eq_inert D v H₀ hH h2 hdet (fun h => hsq ((isSquare_res_iff v (-D)).1 h)), hχ]
    exact prod_U_div _ (by exact_mod_cast hq.ne') m

/-- **$\beta^h_v/\lambda_v = \prod_{i=2}^m(1-(\chi(v)/q)^i)$ at the good places** ($m\ge1$, $\lambda_v = L_v(1,\chi)^{-1}$). -/
@[kb "ganhankeyu2001" "(2.11), p. 104 (L_v(M^∨(1)) for U(V): ∏_{i=1}^m L_v(i, χ^i))"]
theorem hermDensity_div_lamL_eq_good (hm : 1 ≤ m) (hH : H₀.IsHermitian) {θ : 𝓞 E}
    (hθ : Binary.Rel.conjO F E θ = -θ) (hθD : algebraMap (𝓞 F) (𝓞 E) (-D) = θ ^ 2) (v : HeightOneSpectrum (𝓞 F))
    (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (hDv : D ∉ v.asIdeal) (hN : QuadraticAlgebra.norm H₀.det ∉ v.asIdeal) :
    hermDensity D H₀ v / lamL (chiE F E) v =
      ∏ i ∈ Finset.range (m - 1), (1 - (chiE F E v / (normP v : ℝ)) ^ (i + 2)) := by
  rw [hermDensity_eq_good D H₀ hH hθ hθD v h2 hDv hN, lamL]
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  refine prod_one_sub_pow_div _ ?_ n
  have h1 := abs_chiE_le (E := E) (Algebra.IsQuadraticExtension.finrank_eq_two F E) v
  have h2 : (2 : ℝ) ≤ normP v := by exact_mod_cast two_le_normP v
  intro h
  have : |chiE F E v| = normP v := by
    rw [div_eq_one_iff_eq (by positivity)] at h; rw [h, abs_of_pos (by positivity)]
  linarith

/-- **$\prod_v\beta^h_v/\lambda_v$ converges unconditionally** ($m\ge1$, $\lambda_v = L_v(1,\chi_{E/F})^{-1}$): the Euler
product defining the finite part of Weil's Tamagawa measure on $U(V)$ (Gan–Hanke–Yu 2001, (2.11); Weil 1982, §2.3). -/
@[kb "ganhankeyu2001" "(2.11), p. 104 [running text: convergence of ∏_v L_v(1,χ)·vol(K_v)]; weil1982 §2.3 [unverified]"]
theorem multipliable_hermDensity_div_lamL (hm : 1 ≤ m) (hD : D ≠ 0) (hsqF : ¬ IsSquare (algebraMap (𝓞 F) F (-D)))
    (hH : H₀.IsHermitian) (hdet : (HK D F H₀).det ≠ 0) {θ : 𝓞 E} (hθ : Binary.Rel.conjO F E θ = -θ)
    (hθD : algebraMap (𝓞 F) (𝓞 E) (-D) = θ ^ 2) :
    Multipliable fun v : HeightOneSpectrum (𝓞 F) => hermDensity D H₀ v / lamL (chiE F E) v := by
  have hN0 : QuadraticAlgebra.norm H₀.det ≠ 0 := norm_ne_zero_quadO D hsqF (det_ne_zero_of_HK D H₀ hdet)
  have hbad : {v : HeightOneSpectrum (𝓞 F) | (2 : 𝓞 F) ∈ v.asIdeal ∨ D ∈ v.asIdeal ∨
      QuadraticAlgebra.norm H₀.det ∈ v.asIdeal}.Finite := by
    refine ((Siegel.finite_mem_asIdeal (two_ne_zero : (2 : 𝓞 F) ≠ 0)).union
      ((Siegel.finite_mem_asIdeal hD).union (Siegel.finite_mem_asIdeal hN0))).subset ?_
    intro v hv; exact hv
  refine multipliable_of_abs_sub_one_le _ (C := (m - 1 : ℕ) * 2 ^ (m - 1)) (σ := 2) (by norm_num) ?_
  filter_upwards [hbad.compl_mem_cofinite] with v hv
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_or] at hv
  rw [hermDensity_div_lamL_eq_good D H₀ hm hH hθ hθD v hv.1 hv.2.1 hv.2.2]
  have hq : (2 : ℝ) ≤ normP v := by exact_mod_cast two_le_normP v
  have hχ := abs_chiE_le (E := E) (Algebra.IsQuadraticExtension.finrank_eq_two F E) v
  have hx : |chiE F E v / (normP v : ℝ)| ≤ 1 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < normP v), div_le_one (by positivity)]; linarith
  refine (abs_prod_one_sub_pow_sub_one_le hx (m - 1)).trans ?_
  gcongr
  rw [div_pow, Real.rpow_neg (by positivity), Real.rpow_two, div_eq_mul_inv]
  have : chiE F E v ^ 2 ≤ 1 := by
    rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) hχ
  calc chiE F E v ^ 2 * ((normP v : ℝ) ^ 2)⁻¹ ≤ 1 * ((normP v : ℝ) ^ 2)⁻¹ := by gcongr
    _ = _ := one_mul _

/-- **The normalizing constant of `muFinU` is a convergent Euler product**: $\prod_v\beta^h_v/\lambda_v$ has product
`∏' v, hermDensity D H₀ v / lamL (chiE F E) v`, so `muTamU` is normalized by a genuine (not junk) value. -/
theorem hasProd_hermDensity_div_lamL (hm : 1 ≤ m) (hD : D ≠ 0) (hsqF : ¬ IsSquare (algebraMap (𝓞 F) F (-D)))
    (hH : H₀.IsHermitian) (hdet : (HK D F H₀).det ≠ 0) {θ : 𝓞 E} (hθ : Binary.Rel.conjO F E θ = -θ)
    (hθD : algebraMap (𝓞 F) (𝓞 E) (-D) = θ ^ 2) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) => hermDensity D H₀ v / lamL (chiE F E) v)
      (∏' v, hermDensity D H₀ v / lamL (chiE F E) v) :=
  (multipliable_hermDensity_div_lamL D H₀ hm hD hsqF hH hdet hθ hθD).hasProd

end QuadFormsKB.Tamagawa.Unitary
