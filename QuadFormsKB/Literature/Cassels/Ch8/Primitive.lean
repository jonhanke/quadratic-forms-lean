/-
# Cassels, Chapter 8, §§1–2: primitive forms and primitive vectors over $\mathbb Z_p$

**Setting** (as in `Ch8/Bases.lean`): a $\mathbb Q_p$-valued form $f(\vec x) = \sum_{i,j} f_{ij}x_ix_j$ is given by its
matrix $F = (f_{ij}) \in M_n(\mathbb Q_p)$ (`qf F`); Cassels' integrality in this chapter is the classical one,
$f_{ij} \in \mathbb Z_p$ (p. 111). Vectors of $\mathbb Z_p^n$ are `Fin n → ℤ_[p]`.

**Defines** (8.r1, p. 111) classically integral (`IsClassIntegral`), primitive (`IsPrimitiveForm`), properly and
improperly primitive (`IsProperlyPrimitive`, `IsImproperlyPrimitive`; Cassels uses these for $p = 2$).

**Proves**
* `isPrimitiveForm_iff`: $f$ is primitive if and only if $f$ is integral and $p^{-1}f$ is not (Cassels' gloss);
* `isProperlyPrimitive_example`, `isImproperlyPrimitive_example` (p. 111): for $p = 2$, $x_1^{2} + 2x_1x_2$ is properly
  primitive and $2x_1^{2} + 2x_1x_2$ is improperly primitive;
* `isPrimitiveVec_padic_iff` (**Cor. to Lemma 2.1**, p. 112): a vector $\vec a \in \mathbb Z_p^n$ is part of a basis of
  $\mathbb Z_p^n$ (`IsPrimitiveVec`, Chapter 7) if and only if it is primitive, $\max_i\lvert a_i\rvert_p = 1$.
-/
import QuadFormsKB.Literature.Cassels.Ch8.Bases
import QuadFormsKB.Literature.Cassels.Ch7.Thm31

namespace QuadFormsKB.Cassels

open Matrix

variable {n : ℕ} {p : ℕ} [hp : Fact p.Prime]

/-- A form $f$ with matrix $F \in M_n(\mathbb Q_p)$ is *(classically) integral* (Cassels, Ch. 8, p. 111): every
$f_{ij} \in \mathbb Z_p$, i.e. $\lvert f_{ij}\rvert_p \le 1$. -/
@[kb "cassels1978" "Ch. 8, §1, p. 111 (classically integral p-adic form)"]
def IsClassIntegral (F : Matrix (Fin n) (Fin n) ℚ_[p]) : Prop := ∀ i j, ‖F i j‖ ≤ 1

/-- A *primitive* form (Cassels, Ch. 8, p. 111): $\max_{i,j}\lvert f_{ij}\rvert_p = 1$, i.e. $f$ is integral and some
coefficient is a unit. -/
@[kb "cassels1978" "Ch. 8, §1, p. 111 (primitive form)"]
def IsPrimitiveForm (F : Matrix (Fin n) (Fin n) ℚ_[p]) : Prop := IsClassIntegral F ∧ ∃ i j, ‖F i j‖ = 1

/-- A *properly primitive* form (Cassels, Ch. 8, p. 111, for $p = 2$): primitive with $\lvert f_{jj}\rvert_p = 1$ for
some $j$ (some diagonal coefficient is a unit). -/
@[kb "cassels1978" "Ch. 8, §1, p. 111 (properly primitive form, p = 2)"]
def IsProperlyPrimitive (F : Matrix (Fin n) (Fin n) ℚ_[p]) : Prop := IsPrimitiveForm F ∧ ∃ j, ‖F j j‖ = 1

/-- An *improperly primitive* form (Cassels, Ch. 8, p. 111, for $p = 2$): primitive but not properly primitive, i.e.
every diagonal coefficient lies in $p\mathbb Z_p$. -/
@[kb "cassels1978" "Ch. 8, §1, p. 111 (improperly primitive form, p = 2)"]
def IsImproperlyPrimitive (F : Matrix (Fin n) (Fin n) ℚ_[p]) : Prop := IsPrimitiveForm F ∧ ¬ IsProperlyPrimitive F

/-- Cassels' gloss on "primitive" (Ch. 8, p. 111): *$f$ is primitive when $f$ is integral but $p^{-1}f$ is not.* -/
@[kb "cassels1978" "Ch. 8, §1, p. 111 (primitive: f integral, p⁻¹f not)"]
theorem isPrimitiveForm_iff (F : Matrix (Fin n) (Fin n) ℚ_[p]) :
    IsPrimitiveForm F ↔ IsClassIntegral F ∧ ¬ IsClassIntegral ((p : ℚ_[p])⁻¹ • F) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hnorm : ∀ i j, ‖((p : ℚ_[p])⁻¹ • F) i j‖ = p * ‖F i j‖ := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, Padic.norm_p, inv_inv]
  unfold IsPrimitiveForm IsClassIntegral
  constructor
  · rintro ⟨hint, i, j, h1⟩
    refine ⟨hint, fun h => ?_⟩
    have := h i j
    rw [hnorm, h1, mul_one] at this
    exact absurd this (not_le.2 (by exact_mod_cast hp.out.one_lt))
  · rintro ⟨hint, hnot⟩
    refine ⟨hint, ?_⟩
    by_contra hcon
    push Not at hcon
    apply hnot
    intro i j
    rw [hnorm]
    have hlt : ‖F i j‖ < 1 := lt_of_le_of_ne (hint i j) (hcon i j)
    have hle : ‖F i j‖ ≤ (p : ℝ) ^ (-1 : ℤ) :=
      (Padic.norm_le_pow_iff_norm_lt_pow_add_one _ _).2 (by simpa using hlt)
    calc (p : ℝ) * ‖F i j‖ ≤ p * (p : ℝ) ^ (-1 : ℤ) := by gcongr
      _ = 1 := by rw [_root_.zpow_neg_one, mul_inv_cancel₀ hp0.ne']

/-- Cassels' first example (Ch. 8, p. 111): *$x_1^{2} + 2x_1x_2$ is properly primitive* ($p = 2$); its matrix is
$\begin{pmatrix} 1 & 1 \\ 1 & 0 \end{pmatrix}$. -/
@[kb "cassels1978" "Ch. 8, §1, p. 111 (example: x₁² + 2x₁x₂ properly primitive)"]
theorem isProperlyPrimitive_example : IsProperlyPrimitive (p := 2) !![(1 : ℚ_[2]), 1; 1, 0] := by
  refine ⟨⟨fun i j => ?_, 0, 0, by simp⟩, 0, by simp⟩
  fin_cases i <;> fin_cases j <;> simp

private theorem norm_two_padic_two : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by
  have := Padic.norm_p (p := 2)
  exact_mod_cast this

/-- Cassels' second example (Ch. 8, p. 111): *$2x_1^{2} + 2x_1x_2$ is improperly primitive* ($p = 2$); its matrix is
$\begin{pmatrix} 2 & 1 \\ 1 & 0 \end{pmatrix}$. -/
@[kb "cassels1978" "Ch. 8, §1, p. 111 (example: 2x₁² + 2x₁x₂ improperly primitive)"]
theorem isImproperlyPrimitive_example : IsImproperlyPrimitive (p := 2) !![(2 : ℚ_[2]), 1; 1, 0] := by
  refine ⟨⟨fun i j => ?_, 0, 1, by simp⟩, fun ⟨_, j, hj⟩ => ?_⟩
  · fin_cases i <;> fin_cases j <;> norm_num [norm_two_padic_two]
  · fin_cases j <;> simp [norm_two_padic_two] at hj

/-- **Cassels, Ch. 8, Corollary to Lemma 2.1**: *a necessary and sufficient condition that a vector
$\vec a \in \mathbb Z_p^n$ form a part of some basis is that $\vec a$ be primitive*, where (p. 112) $\vec a$ is
primitive if $\max_i\lvert a_i\rvert_p = 1$. "Part of some basis" is Chapter 7's `IsPrimitiveVec` (a member of a set
that is a $\mathbb Z_p$-basis of $\mathbb Z_p^n$); since every $\lvert a_i\rvert_p \le 1$, the maximum is $1$ if and
only if some $\lvert a_i\rvert_p = 1$. -/
@[kb "cassels1978" "Ch. 8, Cor. to Lemma 2.1, p. 112"]
theorem isPrimitiveVec_padic_iff (a : Fin n → ℤ_[p]) : IsPrimitiveVec ℤ_[p] a ↔ ∃ i, ‖a i‖ = 1 := by
  rw [isPrimitiveVec_iff_coprime (Pi.basisFun ℤ_[p] (Fin n)) a]
  have hrepr : ⇑((Pi.basisFun ℤ_[p] (Fin n)).repr a) = a := by ext i; simp
  rw [hrepr]
  simp_rw [← PadicInt.isUnit_iff]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have hle : Ideal.span (Set.range a) ≤ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact (IsLocalRing.mem_maximalIdeal _).2 (hcon i)
    rw [h] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal ℤ_[p]).ne_top (top_le_iff.1 hle)
  · rintro ⟨i, hi⟩
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) hi

end QuadFormsKB.Cassels
