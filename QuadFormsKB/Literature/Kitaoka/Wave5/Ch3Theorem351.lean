/-
# Kitaoka 1993, Theorems 3.5.1 and 3.5.2: isotropy and classification over $\mathbb Q_p$ by $dU$ and $S(U)$

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §3.5, Theorem 3.5.1 (p. 60) and Theorem 3.5.2
(p. 62) (printed pages).

**Setting.** $p$ is a prime, $F = \mathbb Q_p$ and $(\ ,\ )_p$ its Hilbert symbol (`hilbertSymbol ℚ_[p]`). A regular
quadratic space $U$ of dimension $m$ over $F$ has an orthogonal basis, $U \cong \langle a_0\rangle \perp \dots \perp
\langle a_{m-1}\rangle$ with $a_i \in F^\times$ (Kitaoka's $a_1, \dots, a_m$ are `a 0, …, a (m-1)` here), and is
given here by the coefficient family $a : \mathrm{Fin}\ m \to F$ (`QuadForm.diag a`). Kitaoka's invariants are
the discriminant $dU = \prod_i a_i$ modulo $(F^\times)^2$ (`Kitaoka.Hasse.discK a`; "$dU = c$" means
$dU \in c\,(F^\times)^2$, written `IsSquare (c * discK a)` or `IsSquare (discK a)` for $c = 1$) and the Hasse invariant
$S(U) = \prod_{i \le j}(a_i, a_j)_F$ (`Kitaoka.Hasse.hasseK a`, with $\le$; it differs from Cassels' and Serre's
$\prod_{i < j}$, `PadicClass.hasseVec`, by the factor $(dU, -1)_F$). $U$ is isotropic when $Q(x) = 0$ for some
$x \ne 0$ (`QuadForm.IsotropicIn`).

**Proves** (unconditional).
* `theorem351` (Theorem 3.5.1): $U$ is isotropic if and only if $m \ge 5$, or $m = 2$ and $dU = -1$, or $m = 3$ and
  $S(U) = (-1, -1)_p$, or $m = 4$ and either ($dU = 1$ and $S(U) = (-1, -1)_p$) or $dU \ne 1$.
* `theorem352` (Theorem 3.5.2): two regular spaces $U$, $V$ of the same dimension are isometric if and only if
  $dU = dV$ and $S(U) = S(V)$.
* `theorem351_real` (Theorem 3.5.1 over $\mathbb R$, $m \le 4$): the same criterion without the case $m \ge 5$.

The algebra is done over every field satisfying the library's axioms `PadicClass.LocalHilbertField`
(bimultiplicative Hilbert symbol, nondegenerate, every quinary form isotropic): `theorem351_gen`, `theorem352_gen`.

**Proof.** Kitaoka's argument for $m = 3$ (the Hilbert symbol criterion `FieldGen.isotropic_diag_three_iff` and his
expansion of $(-a_0a_1, -a_0a_2)$) is followed; for $m = 4$ and $m \ge 5$ and for Theorem 3.5.2 the statements are
reduced to the library's versions in terms of Cassels' $c(f) = \prod_{i<j}$ (`Cassels.anisotropic_four_iff_gen`,
`PadicClass.isotropic_of_five_le`, `PadicClass.isometric_iff_invariants`) through $S(U) = c(U)\,(dU, -1)_F$
(`Kitaoka.Hasse.hasseK_eq_lt`).
-/
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch3Hasse342
import QuadFormsKB.Literature.Cassels.Ch4.Invariants

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Kitaoka.Theorem351

open QuadForm PadicClass Hasse

section General

variable {K : Type*} [Field K] [CharZero K] (hK : LocalHilbertField K)
include hK

local notation "hs" => hilbertSymbol K

/-- The library's axioms give a bimultiplicative Hilbert symbol. -/
theorem bimult_of_local : HilbertBimult K := fun _ _ _ ha hb hc => hK.mul_right ha hb hc

/-- $S(U) = c(U)\,(dU, -1)$: Kitaoka's $\prod_{i \le j}$ against Cassels' $\prod_{i < j}$. -/
theorem hasseK_eq_hasseVec {m : ℕ} (a : Fin m → K) (ha : ∀ i, a i ≠ 0) :
    hasseK a = hasseVec a * hs (discK a) (-1) := by
  rw [hasseK_eq_lt (bimult_of_local hK) a ha]
  rfl

theorem discK_ne_zero {m : ℕ} (a : Fin m → K) (ha : ∀ i, a i ≠ 0) : discK a ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => ha i

omit hK in
theorem eq_sq_mul {A B r : K} (hA : A ≠ 0) (h : A * B = r * r) : B = (r / A) ^ 2 * A := by
  rw [div_pow, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hA)]
  linear_combination A * h

omit hK in
/-- A regular space of dimension $\le 1$ is anisotropic. -/
theorem not_isotropic_of_le_one {m : ℕ} (hm : m ≤ 1) (a : Fin m → K) (ha : ∀ i, a i ≠ 0) :
    ¬ (diag a).IsotropicIn K := by
  rw [isotropicIn_diag_iff]
  rintro ⟨y, hy0, hy⟩
  apply hy0
  funext i
  have hm1 : m = 1 := by have := i.2; omega
  subst hm1
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  simp only [Fin.sum_univ_one] at hy
  simpa [ha 0] using hy

omit hK in
/-- $m = 2$: $\langle a_0, a_1\rangle$ is isotropic iff $-a_0a_1$ is a square. -/
theorem isotropic_two_iff {a₀ a₁ : K} (h₀ : a₀ ≠ 0) (_h₁ : a₁ ≠ 0) :
    (diag ![a₀, a₁]).IsotropicIn K ↔ IsSquare (-(a₀ * a₁)) := by
  rw [isotropicIn_diag_iff]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  constructor
  · rintro ⟨y, hy0, hy⟩
    have hy1 : y 1 ≠ 0 := by
      intro h1
      rw [h1] at hy
      have : y 0 = 0 := by simpa [h₀] using hy
      exact hy0 (by funext i; fin_cases i <;> simp [this, h1])
    refine ⟨a₀ * y 0 / y 1, ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hy1 hy1)]
    linear_combination (-a₀) * hy
  · rintro ⟨r, hr⟩
    refine ⟨![r, a₀], fun h => h₀ (by simpa using congrFun h 1), ?_⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination (-a₀) * hr

/-- $m = 3$ (Kitaoka's computation): $\langle a_0, a_1, a_2\rangle$ is isotropic iff $S(U) = (-1, -1)$. -/
theorem isotropic_three_iff {a₀ a₁ a₂ : K} (h₀ : a₀ ≠ 0) (h₁ : a₁ ≠ 0) (h₂ : a₂ ≠ 0) :
    (diag ![a₀, a₁, a₂]).IsotropicIn K ↔ hasseK ![a₀, a₁, a₂] = hs (-1) (-1) := by
  rw [FieldGen.isotropic_diag_three_iff K a₀ a₁ a₂ h₀ h₁ h₂]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  have hi : a₀⁻¹ ≠ 0 := inv_ne_zero h₀
  have e1 : -a₁ / a₀ = a₀⁻¹ ^ 2 * ((-1) * a₀ * a₁) := by field_simp
  have e2 : -a₂ / a₀ = a₀⁻¹ ^ 2 * ((-1) * a₀ * a₂) := by field_simp
  have hm : (-1 : K) ≠ 0 := by norm_num
  have hm0 : (-1 : K) * a₀ ≠ 0 := mul_ne_zero hm h₀
  rw [e1, e2, hs_sq_left _ _ _ hi, hs_sq_right _ _ _ hi,
    hK.mul_left _ _ _ hm0 h₁ (mul_ne_zero hm0 h₂), hK.mul_left _ _ _ hm h₀ (mul_ne_zero hm0 h₂),
    hK.mul_right hm hm0 h₂, hK.mul_right h₀ hm0 h₂, hK.mul_right h₁ hm0 h₂,
    hK.mul_right hm hm h₀, hK.mul_right h₀ hm h₀, hK.mul_right h₁ hm h₀]
  have hS : hasseK ![a₀, a₁, a₂] =
      hs a₀ a₀ * hs a₀ a₁ * hs a₀ a₂ * (hs a₁ a₁ * hs a₁ a₂) * hs a₂ a₂ := by
    simp (config := {decide := true}) [hasseK, Fin.prod_univ_three]
  rw [hS, hK.self h₀, hK.self h₁, hK.self h₂, hilbertSymbol_comm K (-1) a₀, hilbertSymbol_comm K (-1) a₂,
    hilbertSymbol_comm K a₁ a₀]
  have p1 := PadicClass.hs_pm (K := K) (-1) (-1)
  have p2 := PadicClass.hs_pm (K := K) a₀ (-1)
  have p3 := PadicClass.hs_pm (K := K) a₁ (-1)
  have p4 := PadicClass.hs_pm (K := K) a₂ (-1)
  have p5 := PadicClass.hs_pm (K := K) a₀ a₁
  have p6 := PadicClass.hs_pm (K := K) a₀ a₂
  have p7 := PadicClass.hs_pm (K := K) a₁ a₂
  generalize hs (-1) (-1) = A at *
  generalize hs a₀ (-1) = B₀ at *
  generalize hs a₁ (-1) = B₁ at *
  generalize hs a₂ (-1) = B₂ at *
  generalize hs a₀ a₁ = C₀₁ at *
  generalize hs a₀ a₂ = C₀₂ at *
  generalize hs a₁ a₂ = C₁₂ at *
  rcases p1 with rfl | rfl <;> rcases p2 with rfl | rfl <;> rcases p3 with rfl | rfl <;>
    rcases p4 with rfl | rfl <;> rcases p5 with rfl | rfl <;> rcases p6 with rfl | rfl <;>
    rcases p7 with rfl | rfl <;> decide

/-- $m = 4$: $\langle a_0, \dots, a_3\rangle$ is isotropic iff ($dU = 1$ and $S(U) = (-1, -1)$) or $dU \ne 1$. -/
theorem isotropic_four_iff (a : Fin 4 → K) (ha : ∀ i, a i ≠ 0) :
    (diag a).IsotropicIn K ↔
      (IsSquare (discK a) ∧ hasseK a = hs (-1) (-1)) ∨ ¬ IsSquare (discK a) := by
  have h4 := Cassels.anisotropic_four_iff_gen hK (ha 0) (ha 1) (ha 2) (ha 3)
  rw [← Cassels.eq_vec_four a] at h4
  have hd : discK a = a 0 * a 1 * a 2 * a 3 := by simp [discK, Fin.prod_univ_four]
  rw [← hd] at h4
  rw [hasseK_eq_hasseVec hK a ha]
  by_cases hsq : IsSquare (discK a)
  · have h1 : hs (discK a) (-1) = 1 := by
      rw [hilbertSymbol_comm]; exact hs_of_isSquare _ _ (discK_ne_zero hK a ha) hsq
    rw [h1, mul_one]
    simp only [hsq, true_and, not_true_eq_false, or_false] at h4 ⊢
    have pA := PadicClass.hs_pm (K := K) (-1) (-1)
    have pV := hasseVec_pm a
    constructor
    · intro hiso
      rcases pA with hA | hA <;> rcases pV with hV | hV <;> rw [hA, hV] at h4 ⊢ <;> simp_all
    · intro h
      by_contra hiso
      have h' := h4.mp hiso
      rw [h] at h'
      rcases pA with hA | hA <;> rw [hA] at h' <;> norm_num at h'
  · simp only [hsq, false_and, not_false_eq_true, or_true, iff_true]
    by_contra hiso
    exact hsq (h4.mp hiso).1

/-- **Kitaoka, Theorem 3.5.1, over an abstract `LocalHilbertField`.** -/
theorem theorem351_gen {m : ℕ} (a : Fin m → K) (ha : ∀ i, a i ≠ 0) :
    (diag a).IsotropicIn K ↔
      5 ≤ m ∨ (m = 2 ∧ IsSquare (-discK a)) ∨ (m = 3 ∧ hasseK a = hs (-1) (-1)) ∨
        (m = 4 ∧ ((IsSquare (discK a) ∧ hasseK a = hs (-1) (-1)) ∨ ¬ IsSquare (discK a))) := by
  rcases Nat.lt_or_ge m 5 with hm | hm
  · interval_cases m
    · simpa using not_isotropic_of_le_one (by norm_num) a ha
    · simpa using not_isotropic_of_le_one (by norm_num) a ha
    · rw [eq_vec_two a] at ha ⊢
      have := isotropic_two_iff (ha 0) (ha 1)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
      simp [this, discK, Fin.prod_univ_two]
    · have h3 := isotropic_three_iff hK (ha 0) (ha 1) (ha 2)
      rw [← eq_vec_three a] at h3
      simp [h3]
    · simp [isotropic_four_iff hK a ha]
  · simp only [hm, true_or, iff_true]
    exact isotropic_of_five_le hK ha hm

/-- **Kitaoka, Theorem 3.5.2, over an abstract `LocalHilbertField`.** -/
theorem theorem352_gen {m : ℕ} (a b : Fin m → K) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    (diag a).IsometricIn K (diag b) ↔ IsSquare (discK a * discK b) ∧ hasseK a = hasseK b := by
  rw [isometric_iff_invariants hK ha hb, hasseK_eq_hasseVec hK a ha, hasseK_eq_hasseVec hK b hb]
  have hda := discK_ne_zero hK a ha
  have hdb := discK_ne_zero hK b hb
  have hD : (∃ t : K, t ≠ 0 ∧ ∏ i, b i = t ^ 2 * ∏ i, a i) ↔ IsSquare (discK a * discK b) := by
    unfold discK at *
    constructor
    · rintro ⟨t, -, ht⟩
      exact ⟨t * ∏ i, a i, by rw [ht]; ring⟩
    · rintro ⟨r, hr⟩
      have hr0 : r ≠ 0 := by rintro rfl; simp at hr; exact (mul_ne_zero hda hdb) (by simpa using hr)
      exact ⟨r / ∏ i, a i, div_ne_zero hr0 hda, eq_sq_mul hda hr⟩
  rw [hD]
  constructor
  · rintro ⟨hsq, hv⟩
    refine ⟨hsq, ?_⟩
    rw [hv]
    congr 1
    obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by rintro rfl; simp at hr; exact (mul_ne_zero hda hdb) (by simpa using hr)
    have : discK b = (r / discK a) ^ 2 * discK a := eq_sq_mul hda hr
    rw [this, hs_sq_left _ _ _ (div_ne_zero hr0 hda)]
  · rintro ⟨hsq, hS⟩
    refine ⟨hsq, ?_⟩
    obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by rintro rfl; simp at hr; exact (mul_ne_zero hda hdb) (by simpa using hr)
    have : discK b = (r / discK a) ^ 2 * discK a := eq_sq_mul hda hr
    rw [this, hs_sq_left _ _ _ (div_ne_zero hr0 hda)] at hS
    have p := PadicClass.hs_pm (K := K) (discK a) (-1)
    rcases p with h | h <;> rw [h] at hS <;> simpa using hS

end General

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- **Kitaoka 1993, Theorem 3.5.1** (p. 60). Let $U = \langle a_0\rangle \perp \dots \perp \langle a_{m-1}\rangle$
($a_i \in \mathbb Q_p^\times$) be a regular quadratic space over $\mathbb Q_p$ with $\dim U = m$. Then $U$ is isotropic
if and only if $m \ge 5$, or
* $m = 2$ and $dU = -1$ (that is, $-dU \in (\mathbb Q_p^\times)^2$),
* $m = 3$ and $S(U) = (-1, -1)_p$,
* $m = 4$ and either $dU = 1$ and $S(U) = (-1, -1)_p$, or $dU \ne 1$ (modulo squares).

Unconditional. -/
@[kb "kitaoka1993" "§3.5, Thm. 3.5.1, p. 60"]
theorem theorem351 {m : ℕ} (a : Fin m → ℚ_[p]) (ha : ∀ i, a i ≠ 0) :
    (diag a).IsotropicIn ℚ_[p] ↔
      5 ≤ m ∨ (m = 2 ∧ IsSquare (-discK a)) ∨ (m = 3 ∧ hasseK a = hilbertSymbol ℚ_[p] (-1) (-1)) ∨
        (m = 4 ∧ ((IsSquare (discK a) ∧ hasseK a = hilbertSymbol ℚ_[p] (-1) (-1)) ∨
          ¬ IsSquare (discK a))) :=
  theorem351_gen (localHilbertField_padic p) a ha

/-- **Kitaoka 1993, Theorem 3.5.2** (p. 62). Regular quadratic spaces $U = \perp_i \langle a_i\rangle$ and
$V = \perp_i \langle b_i\rangle$ over $\mathbb Q_p$ of the same dimension $m$ are isometric if and only if
$dU = dV$ (that is, $dU \cdot dV \in (\mathbb Q_p^\times)^2$) and $S(U) = S(V)$. (Kitaoka also lists
$\dim U = \dim V$; spaces of different dimension are never isometric, and the two forms here are taken on the same
$\mathbb Q_p^m$.) Unconditional. -/
@[kb "kitaoka1993" "§3.5, Thm. 3.5.2, p. 62"]
theorem theorem352 {m : ℕ} (a b : Fin m → ℚ_[p]) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    (diag a).IsometricIn ℚ_[p] (diag b) ↔ IsSquare (discK a * discK b) ∧ hasseK a = hasseK b :=
  theorem352_gen (localHilbertField_padic p) a b ha hb

end Padic

section Real

/-- Over $\mathbb R$ the Hilbert symbol of nonzero $x, y$ is $-1$ exactly when both are negative. -/
theorem hs_real_eq (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    hilbertSymbol ℝ x y = if x < 0 ∧ y < 0 then -1 else 1 := by
  split_ifs with h
  · exact (hilbertSymbol_real x y hx hy).mpr h
  · rcases PadicClass.hs_pm x y with h1 | h1
    · exact h1
    · exact absurd ((hilbertSymbol_real x y hx hy).mp h1) h

/-- A positive definite diagonal form has no nonzero zero. -/
theorem real_pos_aux {m : ℕ} (a y : Fin m → ℝ) (h : ∀ i, 0 < a i) (hy : ∑ i, a i * y i ^ 2 = 0) :
    y = 0 := by
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ a i * y i ^ 2 := fun i _ => by have := h i; positivity
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hy
  funext i
  have := h0 i (Finset.mem_univ i)
  have hai := (h i).ne'
  simpa [hai] using this

/-- Over $\mathbb R$, a diagonal form with nonzero coefficients is isotropic iff it has coefficients of both
signs. -/
theorem real_isotropic_iff {m : ℕ} (a : Fin m → ℝ) (ha : ∀ i, a i ≠ 0) :
    (diag a).IsotropicIn ℝ ↔ ∃ i j, a i < 0 ∧ 0 < a j := by
  rw [isotropicIn_diag_iff]
  constructor
  · rintro ⟨y, hy0, hy⟩
    by_contra hcon
    push Not at hcon
    by_cases hpos : ∃ j, 0 < a j
    · obtain ⟨j, hj⟩ := hpos
      have hall : ∀ i, 0 < a i := fun i => by
        rcases lt_or_gt_of_ne (ha i) with h | h
        · exact absurd (hcon i j h) (not_le.mpr hj)
        · exact h
      exact hy0 (real_pos_aux a y hall hy)
    · push Not at hpos
      have hall : ∀ i, 0 < -a i := fun i => by
        have := lt_of_le_of_ne (hpos i) (ha i); linarith
      refine hy0 (real_pos_aux (fun i => -a i) y hall ?_)
      simp only [neg_mul, Finset.sum_neg_distrib, hy, neg_zero]
  · rintro ⟨i, j, hi, hj⟩
    have hij : i ≠ j := by rintro rfl; linarith
    refine ⟨fun k => if k = i then √(a j) else if k = j then √(-a i) else 0, ?_, ?_⟩
    · intro h
      have := congrFun h i
      simp [Real.sqrt_eq_zero', not_le.mpr hj] at this
    · rw [Finset.sum_eq_add i j hij]
      · simp [hij.symm, Real.sq_sqrt hj.le, Real.sq_sqrt (neg_nonneg.mpr hi.le)]
        ring
      · intro c _ hc; simp [hc.1, hc.2]
      · intro h; exact absurd (Finset.mem_univ i) h
      · intro h; exact absurd (Finset.mem_univ j) h

theorem hasseK_three {K : Type*} [Field K] (a₀ a₁ a₂ : K) :
    hasseK ![a₀, a₁, a₂] = hilbertSymbol K a₀ a₀ * hilbertSymbol K a₀ a₁ * hilbertSymbol K a₀ a₂ *
      (hilbertSymbol K a₁ a₁ * hilbertSymbol K a₁ a₂) * hilbertSymbol K a₂ a₂ := by
  simp (config := {decide := true}) [hasseK, Fin.prod_univ_three]

theorem hasseK_four {K : Type*} [Field K] (a₀ a₁ a₂ a₃ : K) :
    hasseK ![a₀, a₁, a₂, a₃] = hilbertSymbol K a₀ a₀ * hilbertSymbol K a₀ a₁ * hilbertSymbol K a₀ a₂ *
      hilbertSymbol K a₀ a₃ * (hilbertSymbol K a₁ a₁ * hilbertSymbol K a₁ a₂ * hilbertSymbol K a₁ a₃) *
      (hilbertSymbol K a₂ a₂ * hilbertSymbol K a₂ a₃) * hilbertSymbol K a₃ a₃ := by
  simp (config := {decide := true}) [hasseK, Fin.prod_univ_four]

/-- **Kitaoka 1993, Theorem 3.5.1, real case** (p. 61: "The above proof for $m \le 4$ shows that the theorem is
also valid for $\mathbb R$"). Let $U = \langle a_0\rangle \perp \dots \perp \langle a_{m-1}\rangle$
($a_i \in \mathbb R^\times$) with $m \le 4$. Then $U$ is isotropic over $\mathbb R$ if and only if
* $m = 2$ and $dU = -1$ (that is, $-dU > 0$),
* $m = 3$ and $S(U) = (-1, -1)_\infty = -1$,
* $m = 4$ and either $dU = 1$ and $S(U) = (-1, -1)_\infty$, or $dU \ne 1$ (modulo squares, i.e. $dU < 0$).

(For $m \ge 5$ the statement fails over $\mathbb R$: positive definite forms are anisotropic.) Unconditional. -/
@[kb "kitaoka1993" "§3.5, Thm. 3.5.1, p. 61 (over ℝ, m ≤ 4)"]
theorem theorem351_real {m : ℕ} (hm : m ≤ 4) (a : Fin m → ℝ) (ha : ∀ i, a i ≠ 0) :
    (diag a).IsotropicIn ℝ ↔
      (m = 2 ∧ IsSquare (-discK a)) ∨ (m = 3 ∧ hasseK a = hilbertSymbol ℝ (-1) (-1)) ∨
        (m = 4 ∧ ((IsSquare (discK a) ∧ hasseK a = hilbertSymbol ℝ (-1) (-1)) ∨
          ¬ IsSquare (discK a))) := by
  have hsq : ∀ d : ℝ, IsSquare d ↔ 0 ≤ d := fun d =>
    ⟨fun ⟨r, hr⟩ => by rw [hr]; exact mul_self_nonneg r, fun h => ⟨√d, (Real.mul_self_sqrt h).symm⟩⟩
  have hmm : hilbertSymbol ℝ (-1) (-1) = -1 := by
    rw [hs_real_eq _ _ (by norm_num) (by norm_num)]; norm_num
  interval_cases m
  · simpa using not_isotropic_of_le_one (by norm_num) a ha
  · simpa using not_isotropic_of_le_one (by norm_num) a ha
  · rw [eq_vec_two a] at ha ⊢
    have := isotropic_two_iff (ha 0) (ha 1)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
    simp [this, discK, Fin.prod_univ_two]
  · have h0 := ha 0
    have h1 := ha 1
    have h2 := ha 2
    rw [eq_vec_three a] at ha ⊢
    rw [real_isotropic_iff _ ha, hasseK_three, hmm]
    simp only [Fin.exists_fin_succ]
    rcases lt_or_gt_of_ne h0 with p0 | p0 <;> rcases lt_or_gt_of_ne h1 with p1 | p1 <;>
      rcases lt_or_gt_of_ne h2 with p2 | p2 <;>
      simp [hs_real_eq, h0, h1, h2, p0, p1, p2, p0.not_gt, p1.not_gt, p2.not_gt]
  · have h0 := ha 0
    have h1 := ha 1
    have h2 := ha 2
    have h3 := ha 3
    rw [Cassels.eq_vec_four a] at ha ⊢
    have hd : discK ![a 0, a 1, a 2, a 3] = a 0 * a 1 * a 2 * a 3 := by
      simp [discK, Fin.prod_univ_four]
    rw [real_isotropic_iff _ ha, hasseK_four, hmm]
    simp only [hsq, hd]
    simp only [Fin.exists_fin_succ]
    rcases lt_or_gt_of_ne h0 with p0 | p0 <;> rcases lt_or_gt_of_ne h1 with p1 | p1 <;>
      rcases lt_or_gt_of_ne h2 with p2 | p2 <;> rcases lt_or_gt_of_ne h3 with p3 | p3 <;>
      simp [hs_real_eq, h0, h1, h2, h3, p0, p1, p2, p3, p0.not_gt, p1.not_gt, p2.not_gt, p3.not_gt, mul_nonneg_iff, mul_neg_iff, mul_pos_iff, mul_nonpos_iff, p0.le, p1.le, p2.le, p3.le,
        p0.not_ge, p1.not_ge, p2.not_ge, p3.not_ge]

end Real

end QuadFormsKB.Kitaoka.Theorem351
