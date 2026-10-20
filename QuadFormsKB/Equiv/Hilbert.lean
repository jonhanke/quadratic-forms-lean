/-
# Hilbert symbol: comparing the definitions, and the link to isotropy
-/
import QuadFormsKB.Defs.Hilbert

namespace QuadFormsKB

/-- **Conic characterisation of the Hilbert symbol.** Over a field $K$ with $2 \ne 0$ and for
$a, b \in K^\times$:
$$(a,b)_K = 1 \iff a x^2 + b y^2 = 1 \text{ has a solution } (x, y) \in K^2.$$
Some texts (e.g. Lam) take the right-hand side as the definition. Here it is a theorem about
Serre's `hilbertSymbol`. The hypotheses matter: at $a = b = 0$ the right-hand side is false while
$(0,0)_K = 1$ by convention. -/
@[kb "lam2005" "Ch. III, §1"]
theorem hilbertSymbol_eq_one_iff_conic (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSymbol K a b = 1 ↔ ∃ x y : K, a * x ^ 2 + b * y ^ 2 = 1 := by
  unfold hilbertSymbol
  constructor
  · intro h
    split_ifs at h with hc
    obtain ⟨x, y, z, hne, hz⟩ := hc
    by_cases hz0 : z = 0
    · subst hz0
      have hx : x ≠ 0 := by
        rintro rfl
        have : b * y ^ 2 = 0 := by linear_combination -hz
        have hy : y = 0 := by
          rcases mul_eq_zero.mp this with h | h
          · exact absurd h hb
          · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
        exact hne (by simp [hy])
      have hy : y ≠ 0 := by
        rintro rfl
        have : a * x ^ 2 = 0 := by linear_combination -hz
        rcases mul_eq_zero.mp this with h | h
        · exact ha h
        · exact hx (pow_eq_zero_iff two_ne_zero |>.mp h)
      refine ⟨(1/b - 1) * x / (2 * y), (1/b + 1) / 2, ?_⟩
      have hax : a * x ^ 2 = - b * y ^ 2 := by linear_combination -hz
      field_simp
      linear_combination (b - 1) ^ 2 * hax
    · refine ⟨x / z, y / z, ?_⟩
      field_simp
      linear_combination -hz
  · rintro ⟨x, y, h⟩
    have hc : ∃ x y z : K, (x, y, z) ≠ 0 ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2 :=
      ⟨x, y, 1, by simp, by linear_combination -h⟩
    simp only [hc, ite_true]

/-- `(a, b) = 1` iff the ternary form `⟨a, b, -1⟩` is isotropic. This is the bridge from
Hilbert symbols to isotropy that Hasse–Minkowski needs. -/
@[kb "serre1973" "Ch. III, §1.1"]
theorem hilbertSymbol_eq_one_iff_isotropic (K : Type*) [Field K] [CharZero K] (a b : ℚ) :
    hilbertSymbol K (algebraMap ℚ K a) (algebraMap ℚ K b) = 1 ↔
      (QuadForm.diag ![a, b, -1]).IsotropicIn K := by
  have hev : ∀ x : Fin 3 → K, QuadForm.evalIn K (QuadForm.diag ![a, b, -1]) x = algebraMap ℚ K a * x 0 ^ 2 + algebraMap ℚ K b * x 1 ^ 2 - x 2 ^ 2 := by
    intro x
    simp [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_three, Matrix.diagonal]
    ring
  unfold hilbertSymbol QuadForm.IsotropicIn
  constructor
  · intro h
    by_cases hc : ∃ x y z : K, (x, y, z) ≠ 0 ∧ z ^ 2 = algebraMap ℚ K a * x ^ 2 + algebraMap ℚ K b * y ^ 2
    · obtain ⟨x, y, z, hne, heq⟩ := hc
      refine ⟨![x, y, z], ?_, ?_⟩
      · intro h0
        apply hne
        have h0' := congrFun h0
        have e0 := h0' 0
        have e1 := h0' 1
        have e2 := h0' 2
        simp at e0 e1 e2
        simp [e0, e1, e2]
      · rw [hev]
        show algebraMap ℚ K a * x ^ 2 + algebraMap ℚ K b * y ^ 2 - z ^ 2 = 0
        rw [heq]; ring
    · rw [if_neg hc] at h
      norm_num at h
  · rintro ⟨x, hne, hx⟩
    rw [if_pos]
    refine ⟨x 0, x 1, x 2, ?_, ?_⟩
    · intro h0
      apply hne
      simp only [Prod.mk_eq_zero] at h0
      obtain ⟨h0, h1, h2⟩ := h0
      funext i
      fin_cases i <;> simp [h0, h1, h2]
    · rw [hev] at hx
      linear_combination -hx

/-- Symmetry. -/
@[kb "serre1973" "Ch. III, §1.1, Prop. 2"]
theorem hilbertSymbol_comm (K : Type*) [Field K] (a b : K) :
    hilbertSymbol K a b = hilbertSymbol K b a := by
  unfold hilbertSymbol
  have h : (∃ x y z : K, (x, y, z) ≠ 0 ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2) ↔
      (∃ x y z : K, (x, y, z) ≠ 0 ∧ z ^ 2 = b * x ^ 2 + a * y ^ 2) := by
    constructor
    · rintro ⟨x, y, z, hne, he⟩
      refine ⟨y, x, z, ?_, by rw [he]; ring⟩
      intro h0
      apply hne
      simp only [Prod.mk_eq_zero] at h0 ⊢
      exact ⟨h0.2.1, h0.1, h0.2.2⟩
    · rintro ⟨x, y, z, hne, he⟩
      refine ⟨y, x, z, ?_, by rw [he]; ring⟩
      intro h0
      apply hne
      simp only [Prod.mk_eq_zero] at h0 ⊢
      exact ⟨h0.2.1, h0.1, h0.2.2⟩
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (h.mp h1) h2
  · exact absurd (h.mpr h2) h1
  · rfl

/-- `(a, -a) = 1`. -/
@[kb "serre1973" "Ch. III, §1.1, Prop. 2"]
theorem hilbertSymbol_self_neg (K : Type*) [Field K] (a : K) : hilbertSymbol K a (-a) = 1 := by
  unfold hilbertSymbol
  rw [if_pos]
  refine ⟨1, 1, 0, ?_, ?_⟩
  · simp
  · ring

/-- `(a, 1) = 1`. -/
@[kb "serre1973" "Ch. III, §1.1, Prop. 2"]
theorem hilbertSymbol_one_right (K : Type*) [Field K] (a : K) : hilbertSymbol K a 1 = 1 := by
  unfold hilbertSymbol
  rw [if_pos]
  refine ⟨0, 1, 1, ?_, ?_⟩
  · simp
  · ring

/-- Over `ℝ`: `(a, b) = -1` iff `a < 0` and `b < 0`. -/
@[kb "serre1973" "Ch. III, §1.2"]
theorem hilbertSymbol_real (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSymbol ℝ a b = -1 ↔ a < 0 ∧ b < 0 := by
  unfold hilbertSymbol
  constructor
  · intro h
    by_cases hex : ∃ x y z, (x, y, z) ≠ 0 ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2
    · rw [if_pos hex] at h; norm_num at h
    · push_neg at hex
      refine ⟨?_, ?_⟩
      · by_contra hna
        have hpos : 0 < a := lt_of_le_of_ne (not_lt.mp hna) (Ne.symm ha)
        apply hex 1 0 (Real.sqrt a)
        · simp
        · rw [Real.sq_sqrt hpos.le]; ring
      · by_contra hnb
        have hpos : 0 < b := lt_of_le_of_ne (not_lt.mp hnb) (Ne.symm hb)
        apply hex 0 1 (Real.sqrt b)
        · simp
        · rw [Real.sq_sqrt hpos.le]; ring
  · rintro ⟨ha', hb'⟩
    rw [if_neg]
    rintro ⟨x, y, z, hne, heq⟩
    apply hne
    have h1 : a * x ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha'.le (sq_nonneg x)
    have h2 : b * y ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb'.le (sq_nonneg y)
    have hz : z ^ 2 = 0 := le_antisymm (by rw [heq]; linarith) (sq_nonneg z)
    have hx : a * x ^ 2 = 0 := by nlinarith [sq_nonneg z]
    have hy : b * y ^ 2 = 0 := by nlinarith [sq_nonneg z]
    have hx' : x = 0 := by
      rcases mul_eq_zero.mp hx with h | h
      · exact absurd h ha
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    have hy' : y = 0 := by
      rcases mul_eq_zero.mp hy with h | h
      · exact absurd h hb
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    have hz' : z = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz
    simp [hx', hy', hz']

end QuadFormsKB
