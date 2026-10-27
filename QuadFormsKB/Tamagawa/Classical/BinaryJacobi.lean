/-
# Jacobi's two-squares theorem and Dirichlet's count for $x_0^2-2x_1^2$, from Siegel's formula

**Layer:** $\mathbb Q$.

The genus of $\mathbb Z^2$ for $x_0^2+x_1^2$ (resp. $x_0^2-2x_1^2$) has one proper class (`BinaryOneClass.lean`), and the number
of representations of $m$ by that class modulo its units is the number of elements of norm $m$ of $\mathbb Z[i]$ (resp.
$\mathbb Z[\sqrt2]$) modulo the norm-one units (`BinaryCount.lean`). With `dirichlet_sumTwoSq` and `dirichlet_pell2`:
* **`dirichlet_sumTwoSq_r2`** (Jacobi): $r_2(m) = 4\sum_{d\mid m}\chi_{-4}(d)$ for $m\ge1$, $r_2$ = `repNum sumTwoSqZ`;
  `jacobi_two_squares`: the same for $\#\{(x_0,x_1)\in\mathbb Z^2 : x_0^2+x_1^2 = m\}$;
* **`dirichlet_pell2_orbits`** (Dirichlet): for $m\ge1$ represented by $x_0^2-2x_1^2$ over $\mathbb Q$, the number of elements of
  norm $m$ of $\mathbb Z[\sqrt2]$ modulo the norm-one units $\pm(3+2\sqrt2)^k$ (`pell2_units`) is $\sum_{d\mid m}\chi_8(d)$.
Unconditional.
-/
import QuadFormsKB.Tamagawa.Classical.BinaryCount
import QuadFormsKB.Tamagawa.Classical.UnitVolumeRat

open NumberField IsDedekindDomain MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Classical

open QuadFormsKB QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.Binary
  QuadFormsKB.Tamagawa.BinaryNormOne RatBridge LocalDensity

/-! ### The two forms as norm forms -/

theorem up_diag_eq_normForm (c : ℤ) : up (QuadForm.diag ![1, -c]) = normForm c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [up, Siegel.toOQ, QuadForm.map, QuadForm.diag, diagForm1, Matrix.diagonal]

theorem up_sumTwoSqZ_eq : up sumTwoSqZ = normForm (-1) := by
  rw [← up_diag_eq_normForm]; simp [sumTwoSqZ]

theorem up_pell2Z_eq : up pell2Z = normForm 2 := by
  rw [← up_diag_eq_normForm]; rfl

instance subsingleton_DC_normForm_neg_one : Subsingleton (DC (normForm (-1))) := by
  refine subsingleton_DC_of_represents_one _ (by simp) fun M hM => ?_
  obtain ⟨x, hx, h | h⟩ := represents_pm_one (-4) (((-(-1) : ℤ)) : 𝓞 ℚ) (by decide) (by simp) (by simp) M hM
  · exact ⟨x, hx, h⟩
  · exfalso
    rw [eval_formF_diag] at h
    have : algebraMap (𝓞 ℚ) ℚ (((-(-1) : ℤ)) : 𝓞 ℚ) = 1 := by simp
    rw [this] at h
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

instance subsingleton_DC_normForm_two : Subsingleton (DC (normForm 2)) := by
  refine subsingleton_DC_of_represents_one _ (by simp) fun M hM =>
    represents_one_of_neg 8 (((-2 : ℤ)) : 𝓞 ℚ) (by decide) (by rw [map_intCast]; norm_num) (by simp) (y := ![1, 1])
      (fun i => by fin_cases i <;> exact ⟨1, by simp⟩) ?_ M hM
  rw [eval_formF_diag, map_intCast]
  simp
  norm_num

/-- **One proper class in the genus of $x_0^2 + x_1^2$** over $\mathbb Q$: the double cosets
$SO(V)(\mathbb Q)\backslash SO(V)(\mathbb A_f)/SO(\hat{\mathbb Z}^2)$ form one point. -/
@[kb "dirichlet1863" "§§ 89–93 (one class of forms of discriminant −4); omeara1963 §102 (proper classes) [unverified]"]
theorem subsingleton_DC_sumTwoSq : Subsingleton (DC (up sumTwoSqZ)) := by
  rw [up_sumTwoSqZ_eq]; infer_instance

/-- **One proper class in the genus of $x_0^2 - 2x_1^2$** over $\mathbb Q$. -/
@[kb "dirichlet1863" "§§ 89–93 (one class of forms of discriminant 8); omeara1963 §102 (proper classes) [unverified]"]
theorem subsingleton_DC_pell2 : Subsingleton (DC (up pell2Z)) := by
  rw [up_pell2Z_eq]; infer_instance

/-! ### Nonnegativity of the divisor sums -/

theorem locRatio₄_nonneg (p m : ℕ) (hp : p.Prime) : 0 ≤ locRatio₄ p m := by
  unfold locRatio₄
  split_ifs with h2 h
  · norm_num
  · norm_num
  · rcases chi4_pm hp h2 with h | h <;> rw [h]
    · simp; positivity
    · push_cast; rw [sum_range_neg_one_pow]; split_ifs <;> norm_num

theorem locRatio₈_nonneg (p m : ℕ) (hp : p.Prime) : 0 ≤ locRatio₈ p m := by
  unfold locRatio₈
  split_ifs with h2 h
  · norm_num
  · norm_num
  · rcases chi8_pm hp h2 with h | h <;> rw [h]
    · simp; positivity
    · push_cast; rw [sum_range_neg_one_pow]; split_ifs <;> norm_num

theorem sum_chi4_nonneg {m : ℕ} (hm : m ≠ 0) : 0 ≤ ∑ d ∈ m.divisors, (ZMod.χ₄ (d : ZMod 4) : ℝ) := by
  rw [← prod_locRatio₄ hm]
  exact Finset.prod_nonneg fun p hp => locRatio₄_nonneg p m (Nat.prime_of_mem_primeFactors hp)

theorem sum_chi8_nonneg {m : ℕ} (hm : m ≠ 0) : 0 ≤ ∑ d ∈ m.divisors, (ZMod.χ₈ (d : ZMod 8) : ℝ) := by
  rw [← prod_locRatio₈ hm]
  exact Finset.prod_nonneg fun p hp => locRatio₈_nonneg p m (Nat.prime_of_mem_primeFactors hp)

/-! ### The counts -/

/-- **$n(\mathbb Z^2, m)$ for $x_0^2+x_1^2$**: the sum over the (unique) class is the number of Gaussian integers of norm
$m$ modulo the units $\pm1, \pm i$. -/
theorem tsum_repCount_sumTwoSq_eq (m : ℕ) :
    ∑' i, Indefinite.repCount (up sumTwoSqZ) (DVR.unary (((m : ℤ) : 𝓞 ℚ))) i =
      ∑' _ : orbitRel.Quotient (unitary (ℤ√(-1))) (normSet (-1) m), (1 : ℝ≥0∞) := by
  rw [up_sumTwoSqZ_eq, tsum_eq_single (⟦1⟧ : DC (normForm (-1))) fun i hi => absurd (Subsingleton.elim _ _) hi]
  exact repCount_normForm (by norm_num) m _

theorem tsum_repCount_pell2_eq (m : ℕ) :
    ∑' i, Indefinite.repCount (up pell2Z) (DVR.unary (((m : ℤ) : 𝓞 ℚ))) i =
      ∑' _ : orbitRel.Quotient (unitary (ℤ√2)) (normSet 2 m), (1 : ℝ≥0∞) := by
  rw [up_pell2Z_eq, tsum_eq_single (⟦1⟧ : DC (normForm 2)) fun i hi => absurd (Subsingleton.elim _ _) hi]
  exact repCount_normForm (by norm_num) m _

/-- The number of Gaussian integers of norm $m$ is `repNum sumTwoSqZ m`. -/
theorem card_normSet_eq_repNum (m : ℤ) : Nat.card (normSet (-1) m) = Siegel.repNum sumTwoSqZ m := by
  unfold Siegel.repNum Siegel.repSet
  refine Nat.card_congr
    { toFun := fun z => ⟨![z.1.re, z.1.im], ?_⟩
      invFun := fun x => ⟨⟨x.1 0, x.1 1⟩, ?_⟩
      left_inv := fun z => Subtype.ext (Zsqrtd.ext rfl rfl)
      right_inv := fun x => Subtype.ext (by funext i; fin_cases i <;> rfl) }
  · show sumTwoSqZ.eval ![z.1.re, z.1.im] = m
    have h : z.1.re * z.1.re - -1 * z.1.im * z.1.im = m := by rw [← Zsqrtd.norm_def]; exact z.2
    simp [sumTwoSqZ, QuadForm.eval, QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_two, Matrix.diagonal]
    linear_combination h
  · show Zsqrtd.norm ⟨x.1 0, x.1 1⟩ = m
    have h : sumTwoSqZ.eval x.1 = m := x.2
    rw [Zsqrtd.norm_def]
    simp [sumTwoSqZ, QuadForm.eval, QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_two, Matrix.diagonal] at h
    linear_combination h

/-- **Jacobi's two-squares theorem, from Siegel's formula:** for $m\ge1$,
$$r_2(m) = 4\sum_{d\mid m}\chi_{-4}(d),$$
$r_2(m)$ = `repNum sumTwoSqZ m` the number of $x\in\mathbb Z^2$ with $x_0^2+x_1^2 = m$, $\chi_{-4}$ = `ZMod.χ₄`. *Proof:*
Siegel's formula for binary forms (`dirichlet_sumTwoSq`), one proper class in the genus (`subsingleton_DC_sumTwoSq`), and
the four units $\pm1,\pm i$ acting freely. Unconditional. -/
@[kb "jacobi1829" "Fundamenta nova, § 40 (r_2(m) = 4 Σ χ_{-4}(d)) [unverified locator]"]
theorem dirichlet_sumTwoSq_r2 (m : ℕ) (hm : 1 ≤ m) :
    (Siegel.repNum sumTwoSqZ m : ℝ) = 4 * ∑ d ∈ m.divisors, (ZMod.χ₄ (d : ZMod 4) : ℝ) := by
  have hm0 : m ≠ 0 := by omega
  have h := dirichlet_sumTwoSq m hm
  rw [tsum_repCount_sumTwoSq_eq] at h
  have hc := card_normSet_gaussian (m := (m : ℤ)) (by exact_mod_cast hm0)
  rw [h, card_normSet_eq_repNum, ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)] at hc
  have := congrArg ENNReal.toReal hc
  rw [ENNReal.toReal_natCast, ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (sum_chi4_nonneg hm0))] at this
  exact this

/-- **Jacobi's two-squares theorem** for pairs: $\#\{(x_0,x_1)\in\mathbb Z^2 : x_0^2+x_1^2 = m\} = 4\sum_{d\mid m}\chi_{-4}(d)$
for $m \ge 1$. Unconditional. -/
@[kb "jacobi1829" "Fundamenta nova, § 40 (r_2(m) = 4 Σ χ_{-4}(d)) [unverified locator]"]
theorem jacobi_two_squares (m : ℕ) (hm : 1 ≤ m) :
    (Nat.card {x : ℤ × ℤ // x.1 ^ 2 + x.2 ^ 2 = m} : ℝ) = 4 * ∑ d ∈ m.divisors, (ZMod.χ₄ (d : ZMod 4) : ℝ) := by
  rw [← card_normSet_gaussian_eq, card_normSet_eq_repNum]
  exact dirichlet_sumTwoSq_r2 m hm

/-- **Dirichlet's count for $x_0^2 - 2x_1^2$, from Siegel's formula:** for $m \ge 1$ represented by $x_0^2-2x_1^2$ over
$\mathbb Q$, the number of elements of norm $m$ of $\mathbb Z[\sqrt2]$ modulo the norm-one units ($\pm(3+2\sqrt2)^k$,
`pell2_units`), i.e. of solutions of $x_0^2 - 2x_1^2 = m$ in $\mathbb Z^2$ modulo the automorphs
$\begin{psmallmatrix}a&2b\\b&a\end{psmallmatrix}$, $a^2-2b^2 = 1$, is
$$\sum_{d\mid m}\chi_8(d),\qquad\chi_8 = \left(\tfrac8\cdot\right) = \texttt{ZMod.χ₈}.$$
One proper class in the genus (`subsingleton_DC_pell2`). Unconditional. -/
@[kb "dirichlet1863" "Vorlesungen über Zahlentheorie, §§ 89–93 (number of representations by a genus) [unverified locator]"]
theorem dirichlet_pell2_orbits (m : ℕ) (hm : 1 ≤ m) (hrat : ∃ ξ : Fin 2 → ℚ, ξ 0 ^ 2 - 2 * ξ 1 ^ 2 = m) :
    (Nat.card (orbitRel.Quotient (unitary (ℤ√2)) (normSet 2 m)) : ℝ) =
      ∑ d ∈ m.divisors, (ZMod.χ₈ (d : ZMod 8) : ℝ) := by
  have hm0 : m ≠ 0 := by omega
  obtain ⟨ξ, hξ⟩ := hrat
  have Ξ : RatFrame (up pell2Z) (DVR.unary (((m : ℤ) : 𝓞 ℚ))) :=
    (ratFrameEquivRatSphere (n' := 1) (up pell2Z) (((m : ℤ) : 𝓞 ℚ))).symm ⟨ξ, by
      show ((up (QuadForm.diag ![1, -2])).map (algebraMap (𝓞 ℚ) ℚ)).eval ξ = _
      rw [qF_up_diag]; simp; linear_combination hξ⟩
  have h := dirichlet_pell2 m hm Ξ
  rw [tsum_repCount_pell2_eq] at h
  have hfin : Finite (orbitRel.Quotient (unitary (ℤ√2)) (normSet 2 m)) := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    rw [ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero] at h
    exact ENNReal.ofReal_ne_top h.symm
  have := Fintype.ofFinite (orbitRel.Quotient (unitary (ℤ√2)) (normSet 2 m))
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_natCast, ENNReal.toReal_ofReal (sum_chi8_nonneg hm0)] at h'
  rw [Nat.card_eq_fintype_card]
  exact h'

/-! ### Class number one and the unit volumes -/

/-- $h(\mathbb Q(i)) = 1$ (Minkowski's bound, `isPrincipalIdealRing_QField_neg_four`). -/
theorem classNumber_QField_neg_four : NumberField.classNumber (QField (-4)) = 1 :=
  NumberField.classNumber_eq_one_iff.2 inferInstance

/-- $h(\mathbb Q(\sqrt2)) = 1$ (Minkowski's bound, `isPrincipalIdealRing_QField_eight`). -/
theorem classNumber_QField_eight : NumberField.classNumber (QField 8) = 1 :=
  NumberField.classNumber_eq_one_iff.2 inferInstance

/-- **The unit volume of $x_0^2+x_1^2$ with $h = 1$:** $\sum_iv(M_i) = \pi/(4w)$, $w$ = `torsionOrder (QField (-4))` the
number of roots of unity of $\mathbb Q(i)$ (the genus has one class, `subsingleton_DC_sumTwoSq`). -/
theorem unitVolume_sum_sumTwoSq_eq :
    ∑' i, unitVolume (up sumTwoSqZ) nondegenerate_up_sumTwoSq i =
      ENNReal.ofReal (Real.pi / (4 * NumberField.Units.torsionOrder (QField (-4)))) := by
  rw [unitVolume_sum_sumTwoSq_classNumber, classNumber_QField_neg_four]
  simp

/-- **The unit volume of $x_0^2-2x_1^2$ with $h = 1$:** $\sum_iv(M_i) = R/(8\sqrt2)$, $R$ = `regulator (QField 8)` the
regulator of $\mathbb Z[\sqrt2]$ (the genus has one class, `subsingleton_DC_pell2`). -/
theorem unitVolume_sum_pell2_eq :
    ∑' i, unitVolume (up pell2Z) nondegenerate_up_pell2 i =
      ENNReal.ofReal (NumberField.Units.regulator (QField 8) / (8 * Real.sqrt 2)) := by
  rw [unitVolume_sum_pell2_classNumber, classNumber_QField_eight]
  simp

end QuadFormsKB.Tamagawa.Classical
