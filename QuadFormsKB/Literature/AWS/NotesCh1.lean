/-
# Hanke, Arizona Winter School 2009 notes, Ch. 1: background on quadratic forms

J. Hanke, *Quadratic Forms and Automorphic Forms*, notes from the 2009 Arizona Winter School,
arXiv:1105.5759 v3 (bibkey `hanke2011aws`; PDF page = printed page), Chapter 1, pp. 11–23.

Most results of Ch. 1 are quoted by the notes from Cassels, O'Meara and Lam; the library already proves
them, and `AWS/NotesCitations.lean` attaches the notes' locators to those declarations. This file
proves the items that had no library counterpart in the notes' form:

- §1.4 (1.4)–(1.6): the Hessian scale and the norm of a form, and their behaviour under scaling.
  *Erratum:* the notes print $\mathrm{Norm}(a\cdot Q) = a^2\cdot\mathrm{Norm}(Q)$; for the scaled form
  $(a\cdot Q)(\vec x) = a\,Q(\vec x)$ the correct identity is $\mathrm{Norm}(a\cdot Q) = a\cdot\mathrm{Norm}(Q)$
  (`normSet_smul`, and `normSet_smul_ne_sq` refutes the printed version).
- Lemma 1.5.2 (`lemma_1_5_2`).
- Thm 1.6.1 (`theorem_1_6_1`, `theorem_1_6_1_unique`).
- Thm 1.6.4: the three anisotropic-dimension statements (`theorem_1_6_4_complex`,
  `theorem_1_6_4_complex_one`, `theorem_1_6_4_real`, `theorem_1_6_4_padic_four`, `theorem_1_6_4_padic_five`).
- Remark 1.9.4: at most two proper classes in a class, and class = proper class for odd $n$
  (`remark_1_9_4_le_two`, `remark_1_9_4_odd`).

Indices are 0-based (`Fin n`).
-/
import QuadFormsKB.Witt.Bridge
import QuadFormsKB.Literature.Cassels.Ch9Sec1
import QuadFormsKB.Literature.Cassels.Ch4.Invariants
import QuadFormsKB.Tamagawa.LocalRankFive
import Mathlib.LinearAlgebra.QuadraticForm.AlgClosed

open Matrix

namespace QuadFormsKB.AWS.Notes

/-! ### §1.4 Scale and norm -/

section Scale

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **The Hessian scale** of a form $Q$ over $R$ (notes (1.4), p. 13):
$\mathrm{Scale}_H(Q) := \{H(\vec x,\vec y) : \vec x,\vec y \in R^n\}$, where $H(\vec x,\vec y) = \vec x^{\mathsf T}H\vec y$ is the
Hessian bilinear form ($H = $ `QuadForm.hessian`). As in the notes this is a set of values, not the ideal it
generates. -/
@[kb "hanke2011aws" "§1.4, (1.4), p. 13"]
def scaleH (Q : QuadForm R n) : Set R := {c | ∃ x y : Fin n → R, x ⬝ᵥ (Q.hessian *ᵥ y) = c}

/-- **The Gram scale** (notes (1.5), p. 13): $\mathrm{Scale}_G(Q) := \{B(\vec x,\vec y)\}$ with the Gram bilinear form
$B = \frac12 H$; defined when $2$ is invertible in $R$. -/
@[kb "hanke2011aws" "§1.4, (1.5), p. 13"]
def scaleG [Invertible (2 : R)] (Q : QuadForm R n) : Set R :=
  {c | ∃ x y : Fin n → R, ⅟2 * x ⬝ᵥ (Q.hessian *ᵥ y) = c}

/-- **The norm** of a form (notes (1.6), p. 13): $\mathrm{Norm}(Q) := \{Q(\vec x) : \vec x \in R^n\}$, the set of values. -/
@[kb "hanke2011aws" "§1.4, (1.6), p. 13"]
def normSet (Q : QuadForm R n) : Set R := Set.range Q.eval

theorem eval_smul (a : R) (Q : QuadForm R n) (x : Fin n → R) : (a • Q).eval x = a * Q.eval x := by
  simp only [QuadForm.eval, QuadForm.evalIn, QuadForm.smul_coeff, Matrix.smul_apply, smul_eq_mul,
    Algebra.algebraMap_self, RingHom.id_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem hessian_smul (a : R) (Q : QuadForm R n) : (a • Q).hessian = a • Q.hessian := by
  simp [QuadForm.hessian, Matrix.transpose_smul, smul_add]

/-- **Notes p. 14:** $\mathrm{Scale}_H(a\cdot Q) = a\cdot\mathrm{Scale}_H(Q)$. -/
@[kb "hanke2011aws" "§1.4, p. 14 (Scale_H(a·Q) = a·Scale_H(Q))"]
theorem scaleH_smul (a : R) (Q : QuadForm R n) : scaleH (a • Q) = (a * ·) '' scaleH Q := by
  ext c
  simp only [scaleH, Set.mem_ofPred_eq, Set.mem_image, hessian_smul, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul]
  constructor
  · rintro ⟨x, y, rfl⟩; exact ⟨_, ⟨x, y, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, y, rfl⟩, rfl⟩; exact ⟨x, y, rfl⟩

/-- **Notes p. 14:** $\mathrm{Scale}_G(a\cdot Q) = a\cdot\mathrm{Scale}_G(Q)$. -/
@[kb "hanke2011aws" "§1.4, p. 14 (Scale_G(a·Q) = a·Scale_G(Q))"]
theorem scaleG_smul [Invertible (2 : R)] (a : R) (Q : QuadForm R n) :
    scaleG (a • Q) = (a * ·) '' scaleG Q := by
  ext c
  simp only [scaleG, Set.mem_ofPred_eq, Set.mem_image, hessian_smul, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul]
  constructor
  · rintro ⟨x, y, rfl⟩; exact ⟨_, ⟨x, y, rfl⟩, by ring⟩
  · rintro ⟨_, ⟨x, y, rfl⟩, rfl⟩; exact ⟨x, y, by ring⟩

/-- **Notes p. 14, corrected:** $\mathrm{Norm}(a\cdot Q) = a\cdot\mathrm{Norm}(Q)$ for the scaled form
$(a\cdot Q)(\vec x) = a\,Q(\vec x)$. *Erratum:* the notes print $a^2\cdot\mathrm{Norm}(Q)$, which is the norm of the
scaled lattice $aL$, i.e. of $\vec x \mapsto Q(a\vec x)$ (see `normSet_smul_ne_sq`). -/
@[kb "hanke2011aws" "§1.4, p. 14 (Norm(a·Q); corrected from a²·Norm(Q))"]
theorem normSet_smul (a : R) (Q : QuadForm R n) : normSet (a • Q) = (a * ·) '' normSet Q := by
  ext c
  simp only [normSet, Set.mem_range, Set.mem_image, eval_smul]
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨_, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨x, rfl⟩

/-- **The printed identity $\mathrm{Norm}(a\cdot Q) = a^2\cdot\mathrm{Norm}(Q)$ is false:** for $Q = x_0^2$ over $\mathbb Z$ and
$a = 2$, $2 = (2Q)(1) \in \mathrm{Norm}(2Q)$ but $2 \notin 4\cdot\mathrm{Norm}(Q)$. -/
@[kb "hanke2011aws" "§1.4, p. 14 (erratum: Norm(a·Q) ≠ a²·Norm(Q))"]
theorem normSet_smul_ne_sq :
    normSet ((2 : ℤ) • QuadForm.diag (fun _ : Fin 1 => (1 : ℤ))) ≠
      ((2 : ℤ) ^ 2 * ·) '' normSet (QuadForm.diag fun _ : Fin 1 => (1 : ℤ)) := by
  intro h
  have h2 : (2 : ℤ) ∈ normSet ((2 : ℤ) • QuadForm.diag (fun _ : Fin 1 => (1 : ℤ))) := by
    refine ⟨fun _ => 1, ?_⟩
    rw [eval_smul]
    simp [QuadForm.eval, QuadForm.evalIn, QuadForm.diag]
  rw [h] at h2
  obtain ⟨c, -, hc⟩ := h2
  have : (4 : ℤ) ∣ 2 := ⟨c, by simpa [eq_comm] using hc⟩
  omega

end Scale

/-! ### §1.5 Quadratic spaces -/

section Spaces

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- **Lemma 1.5.2 (p. 15).** *If a quadratic space $(V,Q)$ is degenerate, then there is some non-zero vector
$\vec v \in V$ perpendicular to $V$.* Here "degenerate" is the failure of nondegeneracy of the Gram bilinear form
$B = $ `QuadraticMap.associated Q` ($2$ invertible in $K$, as in the notes, which assume $\operatorname{char} K \ne 2$). -/
@[kb "hanke2011aws" "§1.5, Lemma 1.5.2, p. 15"]
theorem lemma_1_5_2 [Invertible (2 : K)] (Q : QuadraticForm K V)
    (hQ : ¬ (QuadraticMap.associated Q).SeparatingLeft) :
    ∃ v : V, v ≠ 0 ∧ ∀ w : V, QuadraticMap.associated Q v w = 0 := by
  unfold LinearMap.SeparatingLeft at hQ
  push Not at hQ
  obtain ⟨v, hv, hv0⟩ := hQ
  exact ⟨v, hv0, hv⟩

end Spaces

/-! ### §1.6 Local fields -/

section Local

/-- **Theorem 1.6.1 (p. 16).** *There is exactly one non-degenerate quadratic space over $\mathbb C$ of each dimension
$n$:* every nondegenerate quadratic form on an $n$-dimensional complex space is equivalent to
$x_0^2 + \dots + x_{n-1}^2$. (Existence: the sum of squares itself; uniqueness: `theorem_1_6_1_unique`.) -/
@[kb "hanke2011aws" "§1.6, Thm. 1.6.1, p. 16"]
theorem theorem_1_6_1 {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] {n : ℕ}
    (hn : Module.finrank ℂ V = n) (Q : QuadraticForm ℂ V)
    (hQ : (QuadraticMap.associated Q).SeparatingLeft) :
    Q.Equivalent (QuadraticMap.weightedSumSquares ℂ (1 : Fin n → ℂ)) := by
  subst hn
  exact QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed Q hQ

/-- **Theorem 1.6.1, uniqueness:** two nondegenerate complex quadratic spaces of the same dimension are equivalent. -/
@[kb "hanke2011aws" "§1.6, Thm. 1.6.1, p. 16 (uniqueness)"]
theorem theorem_1_6_1_unique {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (Q : QuadraticForm ℂ V) (Q' : QuadraticForm ℂ W)
    (hQ : (QuadraticMap.associated Q).SeparatingLeft) (hQ' : (QuadraticMap.associated Q').SeparatingLeft)
    (hdim : Module.finrank ℂ V = Module.finrank ℂ W) : Q.Equivalent Q' :=
  (theorem_1_6_1 hdim Q hQ).trans (theorem_1_6_1 rfl Q' hQ').symm

/-- **Theorem 1.6.4, over $\mathbb C$, dimension $\ge 2$ (p. 17):** *over $\mathbb C$ any form in $n \ge 2$ variables is
isotropic.* (Any form, degenerate or not.) The vector is $t\,e_0 + e_1$ with $t$ a root of
$c_{00}t^2 + c_{01}t + c_{11}$, or $e_0$ if $c_{00} = 0$. -/
@[kb "hanke2011aws" "§1.6, Thm. 1.6.4 and proof, p. 17 (ℂ: every form in n ≥ 2 variables is isotropic)"]
theorem theorem_1_6_4_complex {n : ℕ} (hn : 2 ≤ n) (Q : QuadForm ℂ n) : Q.IsotropicIn ℂ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have key : ∀ x : Fin (m + 2) → ℂ, Q.evalIn ℂ x = x ⬝ᵥ (Q.coeff *ᵥ x) := fun x => by
    simpa using QuadForm.evalIn_eq_dotProduct ℂ Q x
  have h10 : Q.coeff 1 0 = 0 := Q.upper (by simp)
  by_cases h0 : Q.coeff 0 0 = 0
  · refine ⟨Pi.single 0 1, by simp, ?_⟩
    rw [key]
    simp [Matrix.mulVec_single, h0]
  · -- solve c₀₀ t² + c₀₁ t + c₁₁ = 0
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq
      (Q.coeff 0 1 * Q.coeff 0 1 - 4 * Q.coeff 0 0 * Q.coeff 1 1) two_pos
    have hdisc : discrim (Q.coeff 0 0) (Q.coeff 0 1) (Q.coeff 1 1) = s * s := by
      rw [discrim, ← sq s, hs]; ring
    obtain ⟨t, ht⟩ : ∃ t, Q.coeff 0 0 * (t * t) + Q.coeff 0 1 * t + Q.coeff 1 1 = 0 :=
      ⟨_, (quadratic_eq_zero_iff h0 hdisc _).mpr (Or.inl rfl)⟩
    refine ⟨Pi.single 0 t + Pi.single 1 1, fun h => ?_, ?_⟩
    · have := congrFun h 1
      simp at this
    · rw [key]
      simp only [Matrix.mulVec_add, Matrix.mulVec_single, add_dotProduct, dotProduct_add,
        single_dotProduct]
      simp [h10]
      linear_combination ht

/-- **Theorem 1.6.4, over $\mathbb C$, dimension $1$:** the non-zero form $a x_0^2$ ($a \ne 0$) is anisotropic, so the
maximal anisotropic dimension of $\mathbb C$ is exactly $1$. -/
@[kb "hanke2011aws" "§1.6, Thm. 1.6.4 and proof, p. 17 (ℂ: a non-zero form of dimension 1 is anisotropic)"]
theorem theorem_1_6_4_complex_one {a : ℂ} (ha : a ≠ 0) : ¬ (QuadForm.diag fun _ : Fin 1 => a).IsotropicIn ℂ := by
  rintro ⟨x, hx, h⟩
  apply hx
  funext i
  fin_cases i
  simp [QuadForm.evalIn, QuadForm.diag, ha] at h
  simpa using h

/-- **Theorem 1.6.4, over $\mathbb R$ (p. 17):** *$x_0^2 + \dots + x_{n-1}^2$ is anisotropic over $\mathbb R$ for every $n$*, so
the maximal anisotropic dimension of $\mathbb R$ is $\infty$. -/
@[kb "hanke2011aws" "§1.6, Thm. 1.6.4 and proof, p. 17 (ℝ: the sum of n squares is anisotropic)"]
theorem theorem_1_6_4_real (n : ℕ) : ¬ (QuadForm.diag fun _ : Fin n => (1 : ℝ)).IsotropicIn ℝ := by
  rintro ⟨x, hx, h⟩
  apply hx
  have hsum : ∑ i, x i * x i = 0 := by
    rw [← h]
    simp only [QuadForm.evalIn, QuadForm.diag, Matrix.diagonal_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (x i))).mp hsum
  funext i
  simpa using this i (Finset.mem_univ _)

variable (p : ℕ) [Fact p.Prime]

/-- **Theorem 1.6.4, over $\mathbb Q_p$, dimension $4$ (p. 17):** *there is always an anisotropic form in four variables*
over $\mathbb Q_p$ (the norm form $x_0^2 - a x_1^2 - b x_2^2 + ab x_3^2$ of the quaternion division algebra $(a,b)_p = -1$;
Cassels Ch. 4, Lemma 2.6). -/
@[kb "hanke2011aws" "§1.6, Thm. 1.6.4 and proof, p. 17 (ℚ_p: an anisotropic quaternary form exists)"]
theorem theorem_1_6_4_padic_four :
    ∃ a : Fin 4 → ℚ_[p], (∀ i, a i ≠ 0) ∧ ¬ (QuadForm.diag a).IsotropicIn ℚ_[p] := by
  obtain ⟨a, b, ha, hb, hab⟩ := Cassels.exists_hilbertSymbol_eq_neg_one p
  refine ⟨![1, -a, -b, a * b], fun i => ?_, Cassels.anisotropic_norm_form p ha hb hab⟩
  fin_cases i <;> simp [ha, hb]

/-- **Theorem 1.6.4, over $\mathbb Q_p$, dimension $\ge 5$ (p. 17):** *over $\mathbb Q_p$ any (nondegenerate) form in $n \ge 5$
variables is isotropic.* Coefficients in $\mathbb Q_p$; from the library's rank-five theorem for completions of number
fields, here via O'Meara 63:19 over $\mathbb Q_p$ (`PadicClass.isotropic_of_five_le`) after diagonalizing. -/
@[kb "hanke2011aws" "§1.6, Thm. 1.6.4 and proof, p. 17 (ℚ_p: every form in n ≥ 5 variables is isotropic)"]
theorem theorem_1_6_4_padic_five {n : ℕ} (hn : 5 ≤ n) (Q : QuadForm ℚ_[p] n) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn ℚ_[p] := by
  obtain ⟨a, ha, hiso⟩ := FieldGen.exists_isometric_diag Q hQ
  rw [FieldGen.isotropicIn_iff_of_isometricIn ℚ_[p] hiso]
  exact PadicClass.isotropic_of_five_le (PadicClass.localHilbertField_padic p) ha hn

end Local

/-! ### Remark 1.9.4: proper classes -/

section Proper

open Siegel

/-- **Remark 1.9.4 (p. 21), first claim:** *there are at most two proper classes in a class.* -/
@[kb "hanke2011aws" "§1.9, Remark 1.9.4, p. 21 (at most two proper classes in a class)"]
theorem remark_1_9_4_le_two {n : ℕ} (hn : 0 < n) (Q : QuadForm ℤ n) : (properClassesIn Q).ncard ≤ 2 := by
  rw [ncard_properClassesIn hn]
  split_ifs <;> norm_num

/-- **Remark 1.9.4 (p. 21), $n$ odd:** *$-1_n$ has determinant $-1$, so $\mathrm{Cls}(Q) = \mathrm{Cls}^+(Q)$:* every form in an
odd number of variables has an improper automorph, and so $\mathbb Z$-equivalence and proper equivalence agree. -/
@[kb "hanke2011aws" "§1.9, Remark 1.9.4, p. 21 (n odd: Cls(Q) = Cls⁺(Q))"]
theorem remark_1_9_4_odd {n : ℕ} (hn : Odd n) (Q Q' : QuadForm ℤ n) : IntEquiv Q Q' ↔ ProperIntEquiv Q Q' := by
  refine intEquiv_iff_properIntEquiv_of_hasImproperAut ⟨-1, fun x => ?_, ?_⟩ Q'
  · simp only [QuadForm.eval, QuadForm.evalIn, Units.val_neg, Units.val_one, Matrix.neg_mulVec,
      Matrix.one_mulVec, Pi.neg_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  · simp [Matrix.det_neg, hn.neg_one_pow]

end Proper

end QuadFormsKB.AWS.Notes
