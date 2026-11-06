/-
# Cassels, Chapter 4, §§1–2: which invariants occur, and anisotropic quaternary forms over $\mathbb Q_p$

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 4, Theorem 1.3 (p. 56, proved pp. 61–62),
Lemma 2.6 (pp. 59–60) and the Note after it (p. 60).

**Setting.** $p$ is a prime and the field is $\mathbb Q_p$ (Cassels' $p \ne \infty$). As in the rest of the library
(`PadicClass`), a regular form over $\mathbb Q_p$ is taken diagonal, $f = \langle a_0, \dots, a_{n-1}\rangle =
\sum_i a_i x_i^{2}$ with all $a_i \ne 0$ (`QuadForm.diag a`; Cassels: "without loss of generality $f$ is diagonal",
Chapter 2, Lemma 1.4). Its invariants (Cassels, Ch. 4, §1, p. 55) are the dimension $n$, the determinant
$d(f) = \prod_i a_i$ modulo squares, and Cassels' Hasse invariant
$$c(f) = \prod_{0 \le i < j < n} (a_i, a_j)_p$$
(`PadicClass.hasseVec a`, the library's Serre $\varepsilon$; independent of the diagonalization by
`PadicClass.hasseVec_eq_of_isometric`). Indices are $0$-based: Cassels' $a_1, \dots, a_n$ are `a 0, …, a (n-1)`.

**Proves.**
* Theorem 1.3 (p. 56): $c(f) = 1$ if $n = 1$ (`hasseVec_eq_one_of_dim_one`), and if $n = 2$ and
  $d(f) = -1$ modulo squares (`hasseVec_eq_one_of_dim_two`); for every other triple $(n, d, c)$ with $n \ge 1$,
  $d \in \mathbb Q_p^{\times}$ and $c = \pm 1$ there is a form with these invariants (`exists_of_invariants`).
* Lemma 2.6 (p. 59): a regular quaternary form is anisotropic if and only if $d(f)$ is a square and
  $c(f) = -(-1, -1)_p$ (`anisotropic_four_iff`).
* Note after Lemma 2.6 (p. 60): there is exactly one class of anisotropic quaternary forms over $\mathbb Q_p$,
  represented by $x_0^{2} - a x_1^{2} - b x_2^{2} + ab x_3^{2}$ for any $a, b$ with $(a, b)_p = -1$
  (`anisotropic_norm_form`, `exists_hilbertSymbol_eq_neg_one`, `isometric_of_anisotropic_four`).
-/
import QuadFormsKB.Literature.LocalGlobal.PadicClassification
import QuadFormsKB.Literature.OMeara.Sec63C

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Cassels

open PadicClass QuadForm

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### Helper lemmas over an abstract local Hilbert field -/

section Helpers

variable {K : Type*} [Field K] [CharZero K]

/-- A one-variable form has empty Hasse product. -/
theorem hasseVec_dim_one_gen (a : Fin 1 → K) : hasseVec a = 1 := by
  simp [hasseVec]

/-- Hasse invariant of a quaternary form in terms of the ternary one. -/
theorem hasseVec_four_gen (hK : LocalHilbertField K) {a₀ a₁ a₂ a₃ : K} (h₀ : a₀ ≠ 0) (h₁ : a₁ ≠ 0)
    (h₂ : a₂ ≠ 0) (h₃ : a₃ ≠ 0) :
    hasseVec ![a₀, a₁, a₂, a₃] =
      hasseVec ![a₀, a₁, a₂] * hilbertSymbol K (a₀ * a₁ * a₂) a₃ := by
  rw [hasseVec_three, hK.mul_left _ _ _ (mul_ne_zero h₀ h₁) h₂ h₃, hK.mul_left _ _ _ h₀ h₁ h₃]
  simp [hasseVec, Fin.prod_univ_four]
  ring

/-- Lemma 2.6 over an abstract local Hilbert field. -/
theorem anisotropic_four_iff_gen (hK : LocalHilbertField K) {a₀ a₁ a₂ a₃ : K} (h₀ : a₀ ≠ 0)
    (h₁ : a₁ ≠ 0) (h₂ : a₂ ≠ 0) (h₃ : a₃ ≠ 0) :
    ¬ (diag ![a₀, a₁, a₂, a₃]).IsotropicIn K ↔
      IsSquare (a₀ * a₁ * a₂ * a₃) ∧
        hasseVec ![a₀, a₁, a₂, a₃] = -hilbertSymbol K (-1) (-1) := by
  have ha : ∀ i, (![a₀, a₁, a₂] : Fin 3 → K) i ≠ 0 := fun i => by fin_cases i <;> simpa
  have hd : a₀ * a₁ * a₂ ≠ 0 := mul_ne_zero (mul_ne_zero h₀ h₁) h₂
  have hrep : (diag ![a₀, a₁, a₂, a₃]).IsotropicIn K ↔
      (diag ![a₀, a₁, a₂]).RepresentsIn K (-a₃) := by
    rw [representsIn_diag_iff_isotropic ha, append_three_one, neg_neg]
  rw [hrep, represents_three_iff hK h₀ h₁ h₂ (neg_ne_zero.mpr h₃)]
  have hE : (∃ t : K, t ≠ 0 ∧ -a₃ = t ^ 2 * (-(a₀ * a₁ * a₂))) ↔ IsSquare (a₀ * a₁ * a₂ * a₃) := by
    constructor
    · rintro ⟨t, -, ht⟩
      exact ⟨t * (a₀ * a₁ * a₂), by linear_combination (-(a₀ * a₁ * a₂)) * ht⟩
    · rintro ⟨r, hr⟩
      have hr0 : r ≠ 0 := by
        rintro rfl
        simp at hr
        rcases hr with ((h | h) | h) | h <;> simp_all
      refine ⟨r / (a₀ * a₁ * a₂), div_ne_zero hr0 hd, ?_⟩
      field_simp
      linear_combination -hr
  rw [← hE]
  have h4 := hasseVec_four_gen hK h₀ h₁ h₂ h₃
  by_cases hEx : ∃ t : K, t ≠ 0 ∧ -a₃ = t ^ 2 * (-(a₀ * a₁ * a₂))
  · have hEx' := hEx
    obtain ⟨t, ht, hta⟩ := hEx
    have ha3 : a₃ = t ^ 2 * (a₀ * a₁ * a₂) := by linear_combination -hta
    have hs1 : hilbertSymbol K (a₀ * a₁ * a₂) a₃ = hilbertSymbol K (-1) (a₀ * a₁ * a₂) := by
      rw [ha3, hs_sq_right _ _ _ ht, hK.self hd, hilbertSymbol_comm]
    have hs2 : hilbertSymbol K (-1) (-(a₀ * a₁ * a₂)) =
        hilbertSymbol K (-1) (-1) * hilbertSymbol K (-1) (a₀ * a₁ * a₂) := by
      rw [show -(a₀ * a₁ * a₂) = -1 * (a₀ * a₁ * a₂) by ring]
      exact hK.mul_right (by norm_num) (by norm_num) hd
    rw [h4, hs1, hs2, hasseVec_three]
    simp only [hEx', true_imp_iff, true_and]
    have p1 := hs_pm (K := K) (-1) (-1)
    have p2 := hs_pm (K := K) (-1) (a₀ * a₁ * a₂)
    have p3 := hs_pm (K := K) a₀ a₁
    have p4 := hs_pm (K := K) a₀ a₂
    have p5 := hs_pm (K := K) a₁ a₂
    generalize hilbertSymbol K (-1) (-1) = A at *
    generalize hilbertSymbol K (-1) (a₀ * a₁ * a₂) = B at *
    generalize hilbertSymbol K a₀ a₁ = C at *
    generalize hilbertSymbol K a₀ a₂ = D at *
    generalize hilbertSymbol K a₁ a₂ = E at *
    rcases p1 with rfl | rfl <;> rcases p2 with rfl | rfl <;> rcases p3 with rfl | rfl <;>
      rcases p4 with rfl | rfl <;> rcases p5 with rfl | rfl <;> decide
  · simp only [hEx, false_imp_iff, not_true_eq_false, false_and]

/-- A quaternary vector is `![a 0, a 1, a 2, a 3]`. -/
theorem eq_vec_four (a : Fin 4 → K) : a = ![a 0, a 1, a 2, a 3] := by
  funext i; fin_cases i <;> rfl

/-- Existence of a form with prescribed invariants over a field with a nonsquare. -/
theorem exists_of_invariants_gen (hK : LocalHilbertField K) (hns : ∃ x : K, ¬ IsSquare x) {n : ℕ}
    (hn : 1 ≤ n) {d : K} (hd : d ≠ 0) {c : ℤ} (hc : c = 1 ∨ c = -1)
    (h1 : n = 1 → c = 1) (h2 : n = 2 → IsSquare (-d) → c = 1) :
    ∃ a : Fin n → K, (∀ i, a i ≠ 0) ∧ (∃ t : K, t ≠ 0 ∧ ∏ i, a i = t ^ 2 * d) ∧ hasseVec a = c := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set a0 : Fin (m + 1) → K := Fin.cons d (fun _ : Fin m => (1 : K)) with ha0def
  have ha0 : ∀ i, a0 i ≠ 0 := cons_ne_zero hd (fun _ => one_ne_zero)
  have hprod : ∏ i, a0 i = d := by simp [a0, Fin.prod_cons]
  have h1' : hasseVec (fun _ : Fin m => (1 : K)) = 1 := by
    simp [hasseVec, hilbertSymbol_one_right]
  have hV0 : hasseVec a0 = 1 := by
    rw [ha0def, hasseVec_cons hK hd (fun _ => one_ne_zero), h1']
    simp [hilbertSymbol_one_right]
  rcases hc with rfl | rfl
  · exact ⟨a0, ha0, ⟨1, one_ne_zero, by rw [hprod]; ring⟩, hV0⟩
  · have hexc : ¬ (m + 1 = 1 ∨ (m + 1 = 2 ∧ IsSquare (-d))) := by
      rintro (h | ⟨h, hsq⟩)
      · exact absurd (h1 h) (by norm_num)
      · exact absurd (h2 h hsq) (by norm_num)
    obtain ⟨b, hb, ⟨t, ht, hdt⟩, hSb⟩ := QuadFormsKB.OMeara.exists_hasseS_neg_gen hK hns
      (by omega) a0 ha0 (fun h2' hsq => hexc (Or.inr ⟨h2', by rwa [hprod] at hsq⟩))
    refine ⟨b, hb, ⟨t, ht, by rw [hdt, hprod]⟩, ?_⟩
    rw [QuadFormsKB.OMeara.hasseS_eq_vec_mul hK b hb, QuadFormsKB.OMeara.hasseS_eq_vec_mul hK a0 ha0,
      hdt, hs_sq_right _ _ _ ht, hV0] at hSb
    have hp := hs_pm (K := K) (-1) (∏ i, a0 i)
    have hq := hasseVec_pm b
    rcases hp with hp | hp <;> rw [hp] at hSb <;> rcases hq with hq | hq <;> rw [hq] at hSb ⊢ <;>
      omega

/-- The quaternary norm form is anisotropic when $(a, b) = -1$. -/
theorem anisotropic_norm_form_gen (hK : LocalHilbertField K) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : hilbertSymbol K a b = -1) :
    ¬ (diag ![1, -a, -b, a * b]).IsotropicIn K := by
  have hm1 : (-1 : K) ≠ 0 := by norm_num
  have ha' : -a ≠ 0 := neg_ne_zero.mpr ha
  have hb' : -b ≠ 0 := neg_ne_zero.mpr hb
  have hab0 : a * b ≠ 0 := mul_ne_zero ha hb
  rw [anisotropic_four_iff_gen hK one_ne_zero ha' hb' hab0]
  refine ⟨⟨a * b, by ring⟩, ?_⟩
  rw [hasseVec_four_gen hK one_ne_zero ha' hb' hab0, hasseVec_three]
  have e1 : hilbertSymbol K 1 (-a) = 1 := hs_one_left _
  have e2 : hilbertSymbol K 1 (-b) = 1 := hs_one_left _
  have e3 : hilbertSymbol K (1 * -a * -b) (a * b) = hilbertSymbol K (a * b) (a * b) := by
    rw [show 1 * -a * -b = a * b by ring]
  have f1 : hilbertSymbol K (-a) (-b) = hilbertSymbol K (-1) (-1) * hilbertSymbol K (-1) b *
      hilbertSymbol K a (-1) * hilbertSymbol K a b := by
    rw [show -a = -1 * a by ring, show -b = -1 * b by ring, hK.mul_left _ _ _ hm1 ha (mul_ne_zero hm1 hb),
      hK.mul_right hm1 hm1 hb, hK.mul_right ha hm1 hb]
    ring
  have g1 : hilbertSymbol K (a * b) (a * b) = hilbertSymbol K a (-1) * hilbertSymbol K b (-1) := by
    rw [hK.self hab0, hK.mul_left _ _ _ ha hb hm1]
  rw [e1, e2, e3, f1, g1, hab, hilbertSymbol_comm K (-1) b]
  have p1 := hs_pm (K := K) (-1) (-1)
  have p2 := hs_pm (K := K) a (-1)
  have p3 := hs_pm (K := K) b (-1)
  generalize hilbertSymbol K (-1) (-1) = A at *
  generalize hilbertSymbol K a (-1) = B at *
  generalize hilbertSymbol K b (-1) = C at *
  rcases p1 with rfl | rfl <;> rcases p2 with rfl | rfl <;> rcases p3 with rfl | rfl <;> decide

end Helpers

/-- $\mathbb Q_p$ has a non-square: $p$ has odd valuation. -/
theorem exists_nonsquare_padic : ∃ x : ℚ_[p], ¬ IsSquare x := by
  refine ⟨(p : ℚ_[p]), ?_⟩
  rintro ⟨r, hr⟩
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr; exact hp.out.ne_zero hr
  have := congrArg Padic.valuation hr
  rw [Padic.valuation_p, Padic.valuation_mul hr0 hr0] at this
  omega

/-! ### Theorem 1.3 -/

/-- **Cassels, Ch. 4, Theorem 1.3 (first statement).** A regular form in one variable has $c(f) = 1$ (the
product defining $c$ is empty). -/
@[kb "cassels1978" "Ch. 4, Thm. 1.3, p. 56 (n = 1: c(f) = 1)"]
theorem hasseVec_eq_one_of_dim_one (a : Fin 1 → ℚ_[p]) : hasseVec a = 1 := by
  exact hasseVec_dim_one_gen a

/-- **Cassels, Ch. 4, Theorem 1.3 (second statement).** A regular binary form $\langle a_0, a_1\rangle$ over
$\mathbb Q_p$ with $d(f) = a_0a_1 \in -(\mathbb Q_p^{\times})^{2}$ has $c(f) = (a_0, a_1)_p = 1$. -/
@[kb "cassels1978" "Ch. 4, Thm. 1.3, p. 56 (n = 2 and d(f) = −1: c(f) = 1)"]
theorem hasseVec_eq_one_of_dim_two (a : Fin 2 → ℚ_[p]) (ha : ∀ i, a i ≠ 0) (hd : IsSquare (-∏ i, a i)) :
    hasseVec a = 1 := by
  have h0 : a 0 ≠ 0 := ha 0
  have h1 : a 1 ≠ 0 := ha 1
  rw [eq_vec_two a, hasseVec_two]
  refine hs_eq_one_of_isSquare_neg_mul (localHilbertField_padic p) h0 h1 ?_
  simpa [Fin.prod_univ_two] using hd

/-- **Cassels, Ch. 4, Theorem 1.3 (existence).** Let $p \ne \infty$. Every triple $(n, d, c)$ not excluded by the
first two statements occurs: given $n \ge 1$, $d \in \mathbb Q_p^{\times}$ and $c = \pm 1$, with $c = 1$ if $n = 1$,
and $c = 1$ if $n = 2$ and $d \in -(\mathbb Q_p^{\times})^{2}$, there is a regular diagonal form
$\langle a_0, \dots, a_{n-1}\rangle$ with $\prod_i a_i \in d\,(\mathbb Q_p^{\times})^{2}$ and $c(f) = c$.
(Cassels' $n(f)$ is a positive integer; the form of dimension $0$ is left out, as in O'Meara 63:23.) -/
@[kb "cassels1978" "Ch. 4, Thm. 1.3, pp. 56, 61–62 (every other triple (n, d, c) occurs over ℚ_p)"]
theorem exists_of_invariants {n : ℕ} (hn : 1 ≤ n) {d : ℚ_[p]} (hd : d ≠ 0) {c : ℤ} (hc : c = 1 ∨ c = -1)
    (h1 : n = 1 → c = 1) (h2 : n = 2 → IsSquare (-d) → c = 1) :
    ∃ a : Fin n → ℚ_[p], (∀ i, a i ≠ 0) ∧ (∃ t : ℚ_[p], t ≠ 0 ∧ ∏ i, a i = t ^ 2 * d) ∧ hasseVec a = c := by
  exact exists_of_invariants_gen (localHilbertField_padic p) (exists_nonsquare_padic p) hn hd hc h1 h2

/-! ### Lemma 2.6 and the Note after it -/

/-- **Cassels, Ch. 4, Lemma 2.6.** A regular quaternary form $f = \langle a_0, a_1, a_2, a_3\rangle$ over
$\mathbb Q_p$ is anisotropic if and only if (i) $d(f) \in (\mathbb Q_p^{\times})^{2}$ and
(ii) $c(f) = -(-1, -1)_p$. -/
@[kb "cassels1978" "Ch. 4, Lemma 2.6, pp. 59–60 (anisotropic iff d(f) is a square and c(f) = −(−1, −1))"]
theorem anisotropic_four_iff (a : Fin 4 → ℚ_[p]) (ha : ∀ i, a i ≠ 0) :
    ¬ (diag a).IsotropicIn ℚ_[p] ↔
      IsSquare (∏ i, a i) ∧ hasseVec a = -hilbertSymbol ℚ_[p] (-1) (-1) := by
  have hK := localHilbertField_padic p
  rw [eq_vec_four a] at *
  have := anisotropic_four_iff_gen hK (ha 0) (ha 1) (ha 2) (ha 3)
  simpa [Fin.prod_univ_four] using this

/-- There are $a, b \in \mathbb Q_p^{\times}$ with $(a, b)_p = -1$ (used in the Note after Cassels, Ch. 4,
Lemma 2.6). -/
theorem exists_hilbertSymbol_eq_neg_one :
    ∃ a b : ℚ_[p], a ≠ 0 ∧ b ≠ 0 ∧ hilbertSymbol ℚ_[p] a b = -1 := by
  obtain ⟨x, hx⟩ := exists_nonsquare_padic p
  have hx0 : x ≠ 0 := by rintro rfl; exact hx ⟨0, by simp⟩
  obtain ⟨y, hy0, hy⟩ := (localHilbertField_padic p).exists_neg_one x hx0 hx
  exact ⟨x, y, hx0, hy0, hy⟩

/-- **Cassels, Ch. 4, Note after Lemma 2.6 (p. 60), the representative.** If $a, b \in \mathbb Q_p^{\times}$ and
$(a, b)_p = -1$, then $x_0^{2} - a x_1^{2} - b x_2^{2} + ab x_3^{2}$ is anisotropic over $\mathbb Q_p$. -/
@[kb "cassels1978" "Ch. 4, Note after Lemma 2.6, p. 60 (x₀² − a x₁² − b x₂² + ab x₃² is anisotropic when (a, b) = −1)"]
theorem anisotropic_norm_form {a b : ℚ_[p]} (ha : a ≠ 0) (hb : b ≠ 0) (hab : hilbertSymbol ℚ_[p] a b = -1) :
    ¬ (diag ![1, -a, -b, a * b]).IsotropicIn ℚ_[p] := by
  exact anisotropic_norm_form_gen (localHilbertField_padic p) ha hb hab

/-- **Cassels, Ch. 4, Note after Lemma 2.6 (p. 60), uniqueness.** Any two anisotropic regular quaternary forms
over $\mathbb Q_p$ are equivalent: there is precisely one anisotropic class of quaternary forms. -/
@[kb "cassels1978" "Ch. 4, Note after Lemma 2.6, p. 60 (exactly one anisotropic quaternary class)"]
theorem isometric_of_anisotropic_four {a b : Fin 4 → ℚ_[p]} (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hai : ¬ (diag a).IsotropicIn ℚ_[p]) (hbi : ¬ (diag b).IsotropicIn ℚ_[p]) :
    (diag a).IsometricIn ℚ_[p] (diag b) := by
  have hK := localHilbertField_padic p
  have ka := (anisotropic_four_iff p a ha).mp hai
  have kb := (anisotropic_four_iff p b hb).mp hbi
  refine (isometric_iff_invariants hK ha hb).mpr ⟨?_, ka.2.trans kb.2.symm⟩
  obtain ⟨r, hr⟩ := ka.1
  obtain ⟨u, hu⟩ := kb.1
  have hr0 : r ≠ 0 := by
    rintro rfl
    have : ∏ i, a i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => ha i
    exact this (by simpa using hr)
  refine ⟨u / r, ?_, ?_⟩
  · intro h
    have hu0 : u = 0 := by
      rcases div_eq_zero_iff.mp h with h | h
      · exact h
      · exact absurd h hr0
    have : ∏ i, b i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hb i
    exact this (by rw [hu, hu0]; simp)
  · rw [hu, hr]; field_simp

end QuadFormsKB.Cassels
