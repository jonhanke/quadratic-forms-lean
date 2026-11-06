/-
# Cassels, Chapter 13, Example 6: a fundamental arc for the representations by an indefinite binary form

Formalization of Cassels, *Rational Quadratic Forms* (1978), Ch. 13, *Examples*, Ex. 6, p. 329. Conventions as in
`Ch13/Sec3.lean`: `cform a b c` $= ax^2 + 2bxy + cy^2$ (classically integral), `pellMat a b c t u` is the automorph
(3.14) $\begin{pmatrix} t - bu & -cu \\ au & t + bu \end{pmatrix}$.
-/
import QuadFormsKB.Literature.Cassels.Ch13.Sec3

open Matrix

namespace QuadFormsKB.Reduction

/-- Helper: the Pell automorph `pellMat a b c t u` as an element of `GL₂(ℤ)`. -/
def pellGL (a b c t u : ℤ) (h : t ^ 2 + (a * c - b ^ 2) * u ^ 2 = 1) : GL (Fin 2) ℤ :=
  ⟨pellMat a b c t u, pellMat a b c t (-u), by
    rw [pellMat_mul]
    have h1 : t * t + (b ^ 2 - a * c) * u * -u = 1 := by linear_combination h
    have h2 : t * -u + t * u = 0 := by ring
    rw [h1, h2, pellMat_one_zero], by
    rw [pellMat_mul]
    have h1 : t * t + (b ^ 2 - a * c) * -u * u = 1 := by linear_combination h
    have h2 : t * u + t * -u = 0 := by ring
    rw [h1, h2, pellMat_one_zero]⟩

theorem pellGL_mem {a b c t u : ℤ} (h : t ^ 2 + (a * c - b ^ 2) * u ^ 2 = 1) :
    pellGL a b c t u h ∈ Siegel.AutPlus (cform a b c) :=
  mem_autPlus_of_pellMat h rfl

theorem pellGL_inv {a b c t u : ℤ} (h : t ^ 2 + (a * c - b ^ 2) * u ^ 2 = 1)
    (h' : t ^ 2 + (a * c - b ^ 2) * (-u) ^ 2 = 1) :
    (pellGL a b c t u h)⁻¹ = pellGL a b c t (-u) h' := by
  rw [inv_eq_iff_mul_eq_one]
  ext1
  simp only [Units.val_mul, Units.val_one, pellGL]
  rw [pellMat_mul]
  have h1 : t * t + (b ^ 2 - a * c) * u * -u = 1 := by linear_combination h
  have h2 : t * -u + t * u = 0 := by ring
  rw [h1, h2, pellMat_one_zero]

/-- Helper: integer vector cast to reals. -/
def cv (w : Fin 2 → ℤ) : Fin 2 → ℝ := fun i => (w i : ℝ)

theorem linL_pellGL {a b c t u : ℤ} (hD : 0 ≤ b ^ 2 - a * c) (h : t ^ 2 + (a * c - b ^ 2) * u ^ 2 = 1)
    (w : Fin 2 → ℤ) :
    linL a b c (cv ((pellGL a b c t u h).val *ᵥ w)) =
      ((t : ℝ) + u * √((b : ℝ) ^ 2 - a * c)) * linL a b c (cv w) := by
  have hv : cv ((pellGL a b c t u h).val *ᵥ w) = pellMat (a : ℝ) b c t u *ᵥ cv w := by
    ext i; fin_cases i <;>
      simp [cv, pellGL, pellMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hv]
  exact (linL_pellMat hD (by exact_mod_cast h) (cv w)).1

/-- Helper: powers of the Pell automorph scale `L` by powers of `η`. -/
theorem linL_pellGL_zpow {a b c t u : ℤ} (hD : 0 ≤ b ^ 2 - a * c)
    (h : t ^ 2 + (a * c - b ^ 2) * u ^ 2 = 1) (h' : t ^ 2 + (a * c - b ^ 2) * (-u) ^ 2 = 1) (n : ℤ)
    (w : Fin 2 → ℤ) :
    linL a b c (cv (((pellGL a b c t u h) ^ n).val *ᵥ w)) =
      ((t : ℝ) + u * √((b : ℝ) ^ 2 - a * c)) ^ n * linL a b c (cv w) := by
  set η : ℝ := (t : ℝ) + u * √((b : ℝ) ^ 2 - a * c) with hη
  have hs : √((b : ℝ) ^ 2 - a * c) ^ 2 = (b : ℝ) ^ 2 - a * c := Real.sq_sqrt (by exact_mod_cast hD)
  have hh : (t : ℝ) ^ 2 + (a * c - b ^ 2) * u ^ 2 = 1 := by exact_mod_cast h
  have hηinv : ((t : ℝ) + ((-u : ℤ) : ℝ) * √((b : ℝ) ^ 2 - a * c)) = η⁻¹ := by
    have : η * ((t : ℝ) + ((-u : ℤ) : ℝ) * √((b : ℝ) ^ 2 - a * c)) = 1 := by
      rw [hη]; push_cast; linear_combination hh + (-(u : ℝ) ^ 2) * hs
    exact (eq_inv_of_mul_eq_one_right this)
  have hne : η ≠ 0 := by
    intro h0; rw [h0] at hηinv; simp at hηinv
    have : η * ((t : ℝ) + ((-u : ℤ) : ℝ) * √((b : ℝ) ^ 2 - a * c)) = 1 := by
      rw [hη]; push_cast; linear_combination hh + (-(u : ℝ) ^ 2) * hs
    rw [h0] at this; simp at this
  induction n using Int.induction_on generalizing w with
  | zero => simp
  | succ i ih =>
    rw [_root_.zpow_add_one, Units.val_mul, ← Matrix.mulVec_mulVec, ih, linL_pellGL hD h, zpow_add_one₀ hne]
    ring
  | pred i ih =>
    rw [_root_.zpow_sub_one, Units.val_mul, ← Matrix.mulVec_mulVec, ih, pellGL_inv h h', linL_pellGL hD h',
      zpow_sub_one₀ hne, hηinv]
    ring

/-- Helper: for `L > 0`, the sign of `y` is the sign of `L² - ae`. -/
theorem linL_sq_sub {a b c e : ℤ} (hD : 0 < b ^ 2 - a * c) {w : Fin 2 → ℤ}
    (hw : a * w 0 ^ 2 + 2 * b * w 0 * w 1 + c * w 1 ^ 2 = e) :
    linL a b c (cv w) ^ 2 - a * e = 2 * √((b : ℝ) ^ 2 - a * c) * linL a b c (cv w) * w 1 := by
  have hD' : 0 ≤ b ^ 2 - a * c := hD.le
  have h1 := linL_mul_linM_int hD' w
  rw [eval_cform, hw] at h1
  have h2 : linL a b c (cv w) - linM a b c (cv w) = 2 * √((b : ℝ) ^ 2 - a * c) * w 1 := by
    simp only [linL, linM, cv]; ring
  have h1' : linL a b c (cv w) * linM a b c (cv w) = a * e := h1
  have : linL a b c (cv w) ^ 2 - a * e = linL a b c (cv w) * (linL a b c (cv w) - linM a b c (cv w)) := by
    linear_combination h1'
  rw [this, h2]; ring

/-- **Example 6** (Cassels, Ch. 13, p. 329): let $f = ax^2 + 2bxy + cy^2$ be classically integral with $a > 0 > c$, and
let $t, u$ be an integral solution of Pell's equation $t^2 + (ac - b^2)u^2 = 1$ with $t > 0$, $u > 0$. Every integral
solution of $f(x, y) = e$, $e > 0$, is in the same orbit under the integral automorphs of $f$ as a solution $(x', y')$
with
$$y' \ge 0, \qquad -aux' + (t - bu)y' < 0.$$
(The two conditions are garbled in the machine-read text; reconstructed: with $T$ the automorph (3.14) of $t, u$, they
say $y' \ge 0$ and that the second coordinate of $T^{-1}(x', y')$ is negative, i.e. $(x', y')$ lies on the arc of the
hyperbola from $(\sqrt{e/a}, 0)$ (included) to its image under $T$ (excluded), a fundamental domain for $\langle T \rangle$
on the branch through $(\sqrt{e/a}, 0)$; the other branch is moved there by $-I$.) -/
@[kb "cassels1978" "Ch. 13, Examples, Ex. 6, p. 329"]
theorem example_6 {a b c : ℤ} (ha : 0 < a) (hc : c < 0) {t u : ℤ} (ht : 0 < t) (hu : 0 < u)
    (hpell : t ^ 2 + (a * c - b ^ 2) * u ^ 2 = 1) {e : ℤ} (he : 0 < e) {x y : ℤ}
    (hxy : a * x ^ 2 + 2 * b * x * y + c * y ^ 2 = e) :
    ∃ T ∈ Siegel.Aut (cform a b c), ∃ x' y' : ℤ, T.val *ᵥ ![x, y] = ![x', y'] ∧
      0 ≤ y' ∧ -a * u * x' + (t - b * u) * y' < 0 := by
  have hD : 0 < b ^ 2 - a * c := by nlinarith
  have hD' : 0 ≤ b ^ 2 - a * c := hD.le
  have hpell' : t ^ 2 + (a * c - b ^ 2) * (-u) ^ 2 = 1 := by linear_combination hpell
  set s : ℝ := √((b : ℝ) ^ 2 - a * c) with hsdef
  have hspos : 0 < s := Real.sqrt_pos.mpr (by exact_mod_cast hD)
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  set S := pellGL a b c t u hpell with hS
  have hSmem : S ∈ Siegel.AutPlus (cform a b c) := pellGL_mem hpell
  set η : ℝ := (t : ℝ) + u * s with hη
  have hη1 : 1 < η := by
    have : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have : (1 : ℝ) ≤ u := by exact_mod_cast hu
    nlinarith
  have hηpos : 0 < η := by linarith
  set w0 : Fin 2 → ℤ := ![x, y] with hw0
  have hw0e : a * w0 0 ^ 2 + 2 * b * w0 0 * w0 1 + c * w0 1 ^ 2 = e := by simpa [hw0] using hxy
  -- sign normalisation
  have hLM0 := linL_mul_linM_int hD' w0
  rw [eval_cform, hw0e] at hLM0
  have hLM0' : linL a b c (cv w0) * linM a b c (cv w0) = a * e := hLM0
  have hL0ne : linL a b c (cv w0) ≠ 0 := by
    intro h0; rw [h0] at hLM0'; nlinarith
  obtain ⟨g0, hg0, hL1⟩ : ∃ g0 ∈ Siegel.AutPlus (cform a b c),
      0 < linL a b c (cv (g0.val *ᵥ w0)) := by
    rcases lt_or_gt_of_ne hL0ne with hneg | hpos
    · refine ⟨-1, neg_mem_autPlus (one_mem _), ?_⟩
      have : cv ((-1 : GL (Fin 2) ℤ).val *ᵥ w0) = -cv w0 := by
        ext i; fin_cases i <;> simp [cv]
      rw [this]
      simp only [linL, Pi.neg_apply] at hneg ⊢
      linarith
    · exact ⟨1, one_mem _, by simpa using hpos⟩
  set w1 : Fin 2 → ℤ := g0.val *ᵥ w0 with hw1
  have hw1e : a * w1 0 ^ 2 + 2 * b * w1 0 * w1 1 + c * w1 1 ^ 2 = e := by
    have := (Siegel.mem_autPlus_iff.mp hg0).1 w0
    rw [eval_cform, eval_cform] at this
    rw [← hw0e]; exact this
  set L1 := linL a b c (cv w1) with hL1def
  set r : ℝ := √((a : ℝ) * e) with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr2 : r ^ 2 = a * e := Real.sq_sqrt (by positivity)
  obtain ⟨k, hk1, hk2⟩ := exists_mem_Ico_zpow (div_pos hL1 hrpos) hη1
  set T1 := S ^ (-k) with hT1
  set T := T1 * g0 with hT
  have hT1mem : T1 ∈ Siegel.AutPlus (cform a b c) := Subgroup.zpow_mem _ hSmem _
  have hTmem : T ∈ Siegel.AutPlus (cform a b c) := Subgroup.mul_mem _ hT1mem hg0
  have hTw : T.val *ᵥ ![x, y] = T1.val *ᵥ w1 := by
    rw [hT, Units.val_mul, ← Matrix.mulVec_mulVec]
  set w' : Fin 2 → ℤ := T1.val *ᵥ w1 with hw'
  have hw'e : a * w' 0 ^ 2 + 2 * b * w' 0 * w' 1 + c * w' 1 ^ 2 = e := by
    have := (Siegel.mem_autPlus_iff.mp hT1mem).1 w1
    rw [eval_cform, eval_cform] at this
    rw [← hw1e]; exact this
  have hL' : linL a b c (cv w') = η ^ (-k) * L1 :=
    linL_pellGL_zpow hD' hpell hpell' (-k) w1
  have hηk : 0 < η ^ k := zpow_pos hηpos k
  have hηk1 : η ^ (k + 1) = η ^ k * η := zpow_add_one₀ hηpos.ne' k
  have hLpos : 0 < linL a b c (cv w') := by
    rw [hL']; exact mul_pos (zpow_pos hηpos _) hL1
  have hηkk : η ^ (-k) * η ^ k = 1 := by rw [← zpow_add₀ hηpos.ne']; simp
  have hrange1 : r ≤ linL a b c (cv w') := by
    rw [hL']
    have : η ^ k * r ≤ L1 := by rwa [le_div_iff₀ hrpos] at hk1
    calc r = η ^ (-k) * (η ^ k * r) := by rw [← mul_assoc, hηkk, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left this (zpow_pos hηpos _).le
  have hrange2 : η⁻¹ * linL a b c (cv w') < r := by
    rw [hL']
    have : L1 < η ^ k * η * r := by rw [hηk1, div_lt_iff₀ hrpos] at hk2; exact hk2
    have h3 : η⁻¹ * (η ^ (-k) * L1) = η ^ (-k) * η⁻¹ * L1 := by ring
    have h4 : η ^ (-k) * η⁻¹ * (η ^ k * η) = 1 := by
      have : η ^ (-k) * η⁻¹ * (η ^ k * η) = (η ^ (-k) * η ^ k) * (η⁻¹ * η) := by ring
      rw [this, hηkk, inv_mul_cancel₀ hηpos.ne']; simp
    have h5 : 0 < η ^ (-k) * η⁻¹ := mul_pos (zpow_pos hηpos _) (inv_pos.mpr hηpos)
    calc η⁻¹ * (η ^ (-k) * L1) = η ^ (-k) * η⁻¹ * L1 := h3
      _ < η ^ (-k) * η⁻¹ * (η ^ k * η * r) := mul_lt_mul_of_pos_left this h5
      _ = (η ^ (-k) * η⁻¹ * (η ^ k * η)) * r := by ring
      _ = r := by rw [h4, one_mul]
  -- y' ≥ 0
  have hy' : 0 ≤ w' 1 := by
    have h1 := linL_sq_sub hD hw'e
    have h2 : 0 ≤ linL a b c (cv w') ^ 2 - a * e := by nlinarith
    have h3 : 0 < 2 * s * linL a b c (cv w') := by positivity
    have h4 : (0 : ℝ) ≤ w' 1 := by
      by_contra hneg; push Not at hneg
      nlinarith [mul_pos_of_neg_of_neg (neg_neg_of_pos h3) hneg]
    exact_mod_cast h4
  -- the second coordinate of S⁻¹ w'
  set w'' : Fin 2 → ℤ := (pellGL a b c t (-u) hpell').val *ᵥ w' with hw''
  have hw''1 : w'' 1 = -a * u * w' 0 + (t - b * u) * w' 1 := by
    simp [hw'', pellGL, pellMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    left; ring
  have hw''e : a * w'' 0 ^ 2 + 2 * b * w'' 0 * w'' 1 + c * w'' 1 ^ 2 = e := by
    have := (Siegel.mem_autPlus_iff.mp (pellGL_mem hpell')).1 w'
    rw [eval_cform, eval_cform] at this
    rw [← hw'e]; exact this
  have hL'' : linL a b c (cv w'') = η⁻¹ * linL a b c (cv w') := by
    have := linL_pellGL hD' hpell' w'
    rw [this]
    congr 1
    have hh : (t : ℝ) ^ 2 + (a * c - b ^ 2) * u ^ 2 = 1 := by exact_mod_cast hpell
    have hs : s ^ 2 = (b : ℝ) ^ 2 - a * c := Real.sq_sqrt (by exact_mod_cast hD')
    apply eq_inv_of_mul_eq_one_right
    rw [hη]; push_cast; linear_combination hh + (-(u : ℝ) ^ 2) * hs
  have hy'' : w'' 1 < 0 := by
    have h1 := linL_sq_sub hD hw''e
    have hpos'' : 0 < linL a b c (cv w'') := by
      rw [hL'']; exact mul_pos (inv_pos.mpr hηpos) hLpos
    have h2 : linL a b c (cv w'') < r := by rw [hL'']; exact hrange2
    have h2' : linL a b c (cv w'') ^ 2 - a * e < 0 := by nlinarith
    have h3 : 0 < 2 * s * linL a b c (cv w'') := by positivity
    have h4 : (w'' 1 : ℝ) < 0 := by
      by_contra hneg; push Not at hneg
      nlinarith [mul_nonneg h3.le hneg]
    exact_mod_cast h4
  refine ⟨T, Siegel.mem_autPlus_iff.mp hTmem |>.1, w' 0, w' 1, ?_, hy', ?_⟩
  · rw [hTw]; ext i; fin_cases i <;> simp
  · rw [hw''1] at hy''; exact hy''

end QuadFormsKB.Reduction
