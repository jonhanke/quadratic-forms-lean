/-
# Hanke 2005, §4.3 and Lemma A1: the symmetric space $Z_{\mathbb C}$ of $SO_n(\mathbb C)$

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

At a complex place $G_{\mathbb C} = SO_n(\mathbb C) = \{\alpha : {}^t\alpha\alpha = 1_n,\ \det\alpha = 1\}$ (for $\varphi_v = 1_n$, (2.9)), and
Hanke (§4.3, pp. 13–14) lets it act on
$$Z_{\mathbb C} = \{z\in\mathbb R^n_n : {}^tz = -z,\ {}^tzz < 1\}$$
through $\iota(\alpha)B(z) = B(\alpha z)\,\mathrm{diag}[\mu_\alpha(z),\mu_\alpha(z)]$, $B(z) = \begin{pmatrix}1_n&z\\-z&1_n\end{pmatrix}$,
$\iota(a+bi) = \begin{pmatrix}a&-b\\b&a\end{pmatrix}$ ((4.3.1)–(4.3.2)); with $\alpha = a + bi$ ($a, b\in\mathbb R^n_n$) this is
$$\alpha z = (az - b)(a + bz)^{-1},\qquad\mu_\alpha(z) = a + bz.$$

**Defines** `ZC n`, `actC α z`.
**Proves** that the action is well defined (`actC_mem`: for $\alpha\in SO_n(\mathbb C)$, $a + bz$ is invertible and
$\alpha z\in Z_{\mathbb C}$, from ${}^t(a+bz)(a+bz) = {}^t(az-b)(az-b) + (1_n - {}^tzz)$), is an action (`actC_one`, `actC_mul`),
(4.3.4) `actC_zero` ($\alpha\cdot0 = -ba^{-1}$), (4.3.5) `actC_zero_eq_zero_iff` (the stabilizer of $p_{\mathbb C} = 0$ is
$\{b = 0\}\cong SO_n(\mathbb R)$), and **Lemma A1** at a complex place (`lemmaA1_complex`): for $n\ge3$ the elements of
$G_{\mathbb C}$ fixing every point of $Z_{\mathbb C}$ are $\pm1_n$.
*Update (hypothesis):* Lemma A1 needs $n\ge3$: for $n = 2$, $SO_2(\mathbb R)$ commutes with the skew-symmetric matrices and
fixes $Z_{\mathbb C}$ pointwise (`lemmaA1_complex_two_false`). Hanke uses it only for $n\ge3$.
Not formalized: the invariant volume form (4.3.9) and the volume computation of §4.3 (`volCComplex` is the closed form).
-/
import Mathlib
import QuadFormsKB.Citation

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

variable {n : ℕ}

/-- **The symmetric space $Z_{\mathbb C}$** (Hanke thesis, §4.3, p. 13): real skew-symmetric $n\times n$ matrices $z$ with
${}^tzz < 1$, i.e. $1_n - {}^tzz$ positive definite. -/
@[kb "hanke2005crelle" "§4.3, p. 13 (Z_C)"]
def ZC (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {z | zᵀ = -z ∧ (1 - zᵀ * z).PosDef}

/-- The real and imaginary parts $a$, $b$ of $\alpha = a + bi\in M_n(\mathbb C)$. -/
def reM (α : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℝ := α.map Complex.re

/-- The imaginary part $b$ of $\alpha = a + bi$. -/
def imM (α : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℝ := α.map Complex.im

/-- **The action of $SO_n(\mathbb C)$ on $Z_{\mathbb C}$** (Hanke thesis, (4.3.1)–(4.3.2), p. 13): $\alpha z = (az - b)(a + bz)^{-1}$
for $\alpha = a + bi$. -/
@[kb "hanke2005crelle" "(4.3.1)–(4.3.2), p. 13 (the G_C-action on Z_C)"]
def actC (α : Matrix (Fin n) (Fin n) ℂ) (z : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (reM α * z - imM α) * (reM α + imM α * z)⁻¹

/-- $SO_n(\mathbb C)$ as a set of matrices: ${}^t\alpha\alpha = 1_n$, $\det\alpha = 1$. -/
def SOC (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ) := {α | αᵀ * α = 1 ∧ α.det = 1}

/-! ### Helper lemmas -/

theorem soc_re_im {α : Matrix (Fin n) (Fin n) ℂ} (hα : α ∈ SOC n) :
    (reM α)ᵀ * reM α - (imM α)ᵀ * imM α = 1 ∧ (reM α)ᵀ * imM α + (imM α)ᵀ * reM α = 0 := by
  have h := hα.1
  constructor <;> ext i j
  · have := congrArg (fun M => (M i j).re) h
    simp [Matrix.mul_apply, Matrix.one_apply, Complex.re_sum, reM, imM] at this ⊢
    rw [this]; split_ifs <;> simp
  · have := congrArg (fun M => (M i j).im) h
    simp [Matrix.mul_apply, Matrix.one_apply, Complex.im_sum, reM, imM] at this ⊢
    have h0 : (if i = j then (1:ℂ) else 0).im = 0 := by split_ifs <;> simp
    rw [h0, Finset.sum_add_distrib] at this
    linarith

theorem reM_mul (α β : Matrix (Fin n) (Fin n) ℂ) : reM (α * β) = reM α * reM β - imM α * imM β := by
  ext i j; simp [Matrix.mul_apply, Complex.re_sum, reM, imM, Finset.sum_sub_distrib]

theorem imM_mul (α β : Matrix (Fin n) (Fin n) ℂ) : imM (α * β) = reM α * imM β + imM α * reM β := by
  ext i j; simp [Matrix.mul_apply, Complex.im_sum, reM, imM, Finset.sum_add_distrib]

theorem key_id (a b z : Matrix (Fin n) (Fin n) ℝ) (h1 : aᵀ * a - bᵀ * b = 1) (h2 : aᵀ * b + bᵀ * a = 0)
    (_hz : zᵀ = -z) :
    (a + b * z)ᵀ * (a + b * z) = (a * z - b)ᵀ * (a * z - b) + (1 - zᵀ * z) := by
  have e : (a + b * z)ᵀ * (a + b * z) - ((a * z - b)ᵀ * (a * z - b) + (1 - zᵀ * z)) =
      (aᵀ * a - bᵀ * b - 1) + (aᵀ * b + bᵀ * a) * z + zᵀ * (bᵀ * a + aᵀ * b)
        - zᵀ * (aᵀ * a - bᵀ * b - 1) * z := by
    simp only [transpose_add, transpose_mul, transpose_sub]
    noncomm_ring
  have h3 : aᵀ * a - bᵀ * b - 1 = 0 := by rw [h1]; simp
  rw [h3, add_comm (bᵀ * a), h2] at e
  have e' : (a + b * z)ᵀ * (a + b * z) - ((a * z - b)ᵀ * (a * z - b) + (1 - zᵀ * z)) = 0 := by
    rw [e]; simp
  exact sub_eq_zero.mp e'

theorem key_id2 (a b z : Matrix (Fin n) (Fin n) ℝ) (h1 : aᵀ * a - bᵀ * b = 1)
    (h2 : aᵀ * b + bᵀ * a = 0) (hz : zᵀ = -z) :
    (a + b * z)ᵀ * (a * z - b) + (a * z - b)ᵀ * (a + b * z) = 0 := by
  have e : (a + b * z)ᵀ * (a * z - b) + (a * z - b)ᵀ * (a + b * z) =
      (aᵀ * a - bᵀ * b - 1) * z + zᵀ * (aᵀ * a - bᵀ * b - 1) + zᵀ * (aᵀ * b + bᵀ * a) * z
        - (aᵀ * b + bᵀ * a) + (z + zᵀ) := by
    simp only [transpose_add, transpose_mul, transpose_sub]
    noncomm_ring
  have h3 : aᵀ * a - bᵀ * b - 1 = 0 := by rw [h1]; simp
  rw [e, h3, h2, hz]
  simp

/-- **The action is well defined** (Hanke thesis, p. 13, "by a direct calculation"): for $\alpha\in SO_n(\mathbb C)$ and
$z\in Z_{\mathbb C}$, $\mu_\alpha(z) = a + bz$ is invertible and $\alpha z\in Z_{\mathbb C}$. -/
@[kb "hanke2005crelle" "§4.3, p. 13 (the action on Z_C is well defined)"]
theorem actC_mem {α : Matrix (Fin n) (Fin n) ℂ} (hα : α ∈ SOC n) {z : Matrix (Fin n) (Fin n) ℝ} (hz : z ∈ ZC n) :
    IsUnit (reM α + imM α * z).det ∧ actC α z ∈ ZC n := by
  obtain ⟨h1, h2⟩ := soc_re_im hα
  obtain ⟨hzs, hzp⟩ := hz
  have k1 := key_id (reM α) (imM α) z h1 h2 hzs
  have k2 := key_id2 (reM α) (imM α) z h1 h2 hzs
  unfold actC
  set μ := reM α + imM α * z with hμ
  set ν := reM α * z - imM α with hν
  have hPSD : (νᵀ * ν).PosSemidef := by
    simpa using Matrix.posSemidef_conjTranspose_mul_self ν
  have hPD : (μᵀ * μ).PosDef := by
    rw [k1]; exact Matrix.PosDef.posSemidef_add hPSD hzp
  have hU : IsUnit μ := isUnit_of_mul_isUnit_right hPD.isUnit
  have hdet : IsUnit μ.det := (isUnit_iff_isUnit_det _).mp hU
  refine ⟨hdet, ?_⟩
  have hT : (μ⁻¹)ᵀ * μᵀ = 1 := by
    rw [← transpose_mul, mul_nonsing_inv _ hdet, transpose_one]
  have hI : μ⁻¹ * μ = 1 := nonsing_inv_mul _ hdet
  have hIr : μ * μ⁻¹ = 1 := mul_nonsing_inv _ hdet
  refine ⟨?_, ?_⟩
  · have h3 : νᵀ * μ = -(μᵀ * ν) := eq_neg_of_add_eq_zero_right k2
    have hνt : νᵀ = -(μᵀ * ν * μ⁻¹) := by
      calc νᵀ = νᵀ * (μ * μ⁻¹) := by rw [hIr, mul_one]
        _ = (νᵀ * μ) * μ⁻¹ := by rw [mul_assoc]
        _ = _ := by rw [h3]; simp
    calc (ν * μ⁻¹)ᵀ = (μ⁻¹)ᵀ * νᵀ := transpose_mul _ _
      _ = (μ⁻¹)ᵀ * (-(μᵀ * ν * μ⁻¹)) := by rw [← hνt]
      _ = -(((μ⁻¹)ᵀ * μᵀ) * ν * μ⁻¹) := by noncomm_ring
      _ = -(ν * μ⁻¹) := by rw [hT]; simp
  · have e : (1 : Matrix (Fin n) (Fin n) ℝ) - zᵀ * z = μᵀ * μ - νᵀ * ν := by
      rw [k1]; abel
    have e2 : (1 : Matrix (Fin n) (Fin n) ℝ) - (ν * μ⁻¹)ᵀ * (ν * μ⁻¹)
        = (μ⁻¹)ᵀ * (1 - zᵀ * z) * μ⁻¹ := by
      rw [e]
      have : (μ⁻¹)ᵀ * (μᵀ * μ - νᵀ * ν) * μ⁻¹
          = ((μ⁻¹)ᵀ * μᵀ) * (μ * μ⁻¹) - (μ⁻¹)ᵀ * νᵀ * ν * μ⁻¹ := by noncomm_ring
      rw [this, hT, hIr, transpose_mul]
      noncomm_ring
    rw [e2]
    have hinj : Function.Injective (μ⁻¹).mulVec :=
      Matrix.mulVec_injective_of_isUnit (isUnit_nonsing_inv_iff.mpr hU)
    simpa using hzp.conjTranspose_mul_mul_same hinj

theorem reM_one : reM (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext i j; by_cases h : i = j <;> simp [reM, Matrix.one_apply, h]

theorem imM_one : imM (1 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  ext i j; by_cases h : i = j <;> simp [imM, Matrix.one_apply, h]

theorem actC_one (z : Matrix (Fin n) (Fin n) ℝ) : actC 1 z = z := by
  simp [actC, reM_one, imM_one]

/-- The action law $(\alpha\beta)z = \alpha(\beta z)$ on $Z_{\mathbb C}$. -/
theorem actC_mul {α β : Matrix (Fin n) (Fin n) ℂ} (hα : α ∈ SOC n) (hβ : β ∈ SOC n) {z : Matrix (Fin n) (Fin n) ℝ}
    (hz : z ∈ ZC n) : actC (α * β) z = actC α (actC β z) := by
  have hβ' := actC_mem hβ hz
  have hαw := actC_mem hα hβ'.2
  obtain ⟨hMdet, _⟩ := hβ'
  set a := reM α
  set b := imM α
  set c := reM β
  set d := imM β
  set M := c + d * z with hM
  set N := c * z - d with hN
  have hMM : M * M⁻¹ = 1 := mul_nonsing_inv _ hMdet
  have hMM' : M⁻¹ * M = 1 := nonsing_inv_mul _ hMdet
  have e1 : (a * M + b * N) * M⁻¹ = a + b * (N * M⁻¹) := by
    rw [add_mul, mul_assoc a, mul_assoc b, hMM, mul_one]
  have e2 : (a * N - b * M) * M⁻¹ = a * (N * M⁻¹) - b := by
    rw [sub_mul, mul_assoc a, mul_assoc b, hMM, mul_one]
  have hw : actC β z = N * M⁻¹ := rfl
  have lhs : actC (α * β) z = (a * N - b * M) * (a * M + b * N)⁻¹ := by
    unfold actC
    rw [reM_mul, imM_mul]
    have q1 : (a * c - b * d) * z - (a * d + b * c) = a * N - b * M := by
      rw [hN, hM]; noncomm_ring
    have q2 : a * c - b * d + (a * d + b * c) * z = a * M + b * N := by
      rw [hN, hM]; noncomm_ring
    rw [q1, q2]
  rw [lhs, hw]
  unfold actC
  change _ = (a * (N * M⁻¹) - b) * (a + b * (N * M⁻¹))⁻¹
  rw [← e1, ← e2, Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hMdet, mul_assoc, ← mul_assoc M⁻¹,
    hMM', one_mul]

/-- **(4.3.4)** (Hanke thesis, p. 14): $F_{\mathbb C}(\alpha) = \alpha p_{\mathbb C} = -ba^{-1}$, $p_{\mathbb C} = 0$. -/
@[kb "hanke2005crelle" "(4.3.4), p. 14"]
theorem actC_zero (α : Matrix (Fin n) (Fin n) ℂ) : actC α 0 = -imM α * (reM α)⁻¹ := by
  simp [actC]

/-- **(4.3.5)** (Hanke thesis, p. 14): the stabilizer of $p_{\mathbb C} = 0$ is $C_{\mathbb C} = \{\alpha = a + bi : b = 0\}$
($\cong SO_n(\mathbb R)$). -/
@[kb "hanke2005crelle" "(4.3.5), p. 14"]
theorem actC_zero_eq_zero_iff {α : Matrix (Fin n) (Fin n) ℂ} (hα : α ∈ SOC n) : actC α 0 = 0 ↔ imM α = 0 := by
  have h0 : (0 : Matrix (Fin n) (Fin n) ℝ) ∈ ZC n :=
    ⟨by simp, by simpa using (Matrix.PosDef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef)⟩
  have hd : IsUnit (reM α).det := by simpa using (actC_mem hα h0).1
  have hu : IsUnit (reM α) := (isUnit_iff_isUnit_det _).mpr hd
  rw [actC_zero]
  constructor
  · intro h
    have := congrArg (· * reM α) h
    simpa [mul_assoc, nonsing_inv_mul _ hd] using this
  · intro h; simp [h]

/-! ### Helpers for Lemma A1 -/

/-- The skew matrix $E_{ij} - E_{ji}$. -/
def skewE (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ := Matrix.single i j 1 - Matrix.single j i 1

theorem skewE_mem {i j : Fin n} (hij : i ≠ j) : ((1 / 2 : ℝ) • skewE i j) ∈ ZC n := by
  have hT : (skewE i j)ᵀ = -skewE i j := by
    simp [skewE, transpose_sub]
  have hSS : (skewE i j)ᵀ * skewE i j = Matrix.single i i 1 + Matrix.single j j 1 := by
    rw [hT]; unfold skewE
    simp [sub_mul, mul_sub, hij, hij.symm]
    abel
  refine ⟨by rw [transpose_smul, hT]; simp, ?_⟩
  have e : (1 : Matrix (Fin n) (Fin n) ℝ) - ((1 / 2 : ℝ) • skewE i j)ᵀ * ((1 / 2 : ℝ) • skewE i j)
      = Matrix.diagonal (fun p => if p = i ∨ p = j then (3 / 4 : ℝ) else 1) := by
    rw [transpose_smul, smul_mul_smul_comm, hSS]
    ext p q
    by_cases hpq : p = q
    · subst hpq
      by_cases h1 : p = i
      · subst h1; simp [Matrix.single_apply_of_ne, hij, hij.symm, Matrix.single]; norm_num
      · by_cases h2 : p = j
        · subst h2; simp [Matrix.single, h1, hij, hij.symm]; norm_num
        · simp [Matrix.single, h1, h2, Ne.symm h1, Ne.symm h2]
    · simp [Matrix.single, hpq, Matrix.one_apply, Matrix.diagonal_apply]
      have h3 : ¬(j = p ∧ j = q) := fun h => hpq (h.1.symm.trans h.2)
      have h4 : ¬(i = p ∧ i = q) := fun h => hpq (h.1.symm.trans h.2)
      simp [h3, h4]
  rw [e, Matrix.posDef_diagonal_iff]
  intro p
  split_ifs <;> norm_num

theorem comm_entries {a : Matrix (Fin n) (Fin n) ℝ} {i j : Fin n} (hij : i ≠ j)
    (h : a * skewE i j = skewE i j * a) :
    (∀ p, p ≠ i → p ≠ j → a p i = 0) ∧ a i i = a j j := by
  constructor
  · intro p hpi hpj
    have := congrFun (congrFun h p) j
    simp [skewE, Matrix.mul_apply, Matrix.sub_apply, Matrix.single, hij, hij.symm, hpi, hpj,
      Ne.symm hpi, Ne.symm hpj] at this
    exact this
  · have := congrFun (congrFun h i) j
    simp [skewE, Matrix.mul_apply, Matrix.sub_apply, Matrix.single, hij, hij.symm] at this
    exact this

theorem commute_scalar (hn : 3 ≤ n) {a : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ i j, i ≠ j → a * skewE i j = skewE i j * a) : ∃ c : ℝ, a = c • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  have off : ∀ p q, p ≠ q → a p q = 0 := by
    intro p q hpq
    obtain ⟨r, hrp, hrq⟩ : ∃ r : Fin n, r ≠ p ∧ r ≠ q := by
      by_contra hcon
      push Not at hcon
      have hsub : (Finset.univ : Finset (Fin n)) ⊆ {p, q} := fun r _ => by
        by_cases hr : r = p
        · simp [hr]
        · simp [hcon r hr]
      have h1 := Finset.card_le_card hsub
      have h2 : ({p, q} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
      simp at h1
      omega
    exact (comm_entries (i := q) (j := r) (Ne.symm hrq) (h q r (Ne.symm hrq))).1 p hpq (Ne.symm hrp)
  have diag : ∀ i j, a i i = a j j := by
    intro i j
    by_cases hij : i = j
    · subst hij; rfl
    · exact (comm_entries hij (h i j hij)).2
  refine ⟨a ⟨0, by omega⟩ ⟨0, by omega⟩, ?_⟩
  ext p q
  by_cases hpq : p = q
  · subst hpq; simp [diag p ⟨0, by omega⟩]
  · simp [hpq, off p q hpq]

theorem reM_neg (α : Matrix (Fin n) (Fin n) ℂ) : reM (-α) = -reM α := by
  ext i j; simp [reM]

theorem imM_neg (α : Matrix (Fin n) (Fin n) ℂ) : imM (-α) = -imM α := by
  ext i j; simp [imM]

theorem zero_mem_ZC : (0 : Matrix (Fin n) (Fin n) ℝ) ∈ ZC n :=
  ⟨by simp, by simpa using (Matrix.PosDef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef)⟩

/-- **Lemma A1 at a complex place** (Hanke thesis, Lemma A1, p. 21): for $n\ge3$, the $\alpha\in SO_n(\mathbb C)$ with
$\alpha z = z$ for every $z\in Z_{\mathbb C}$ are $\pm1_n$ (Hanke: "the analogous statement of [Shi2, Prop. 6.4(5)]"). -/
@[kb "hanke2005crelle" "Lemma A1, p. 21 (complex places)"]
theorem lemmaA1_complex (hn : 3 ≤ n) {α : Matrix (Fin n) (Fin n) ℂ} (hα : α ∈ SOC n) :
    (∀ z ∈ ZC n, actC α z = z) ↔ (α = 1 ∨ α = -1) := by
  constructor
  · intro hz
    have hb : imM α = 0 := (actC_zero_eq_zero_iff hα).mp (hz 0 zero_mem_ZC)
    obtain ⟨h1, -⟩ := soc_re_im hα
    have hd : IsUnit (reM α).det := by simpa using (actC_mem hα (zero_mem_ZC (n := n))).1
    have hcomm : ∀ z ∈ ZC n, reM α * z = z * reM α := by
      intro z hz'
      have := hz z hz'
      simp only [actC, hb] at this
      simp only [sub_zero, zero_mul, add_zero] at this
      calc reM α * z = (reM α * z * (reM α)⁻¹) * reM α := by
            rw [mul_assoc, nonsing_inv_mul _ hd, mul_one]
        _ = z * reM α := by rw [this]
    have hc : ∀ i j, i ≠ j → reM α * skewE i j = skewE i j * reM α := by
      intro i j hij
      have := hcomm _ (skewE_mem hij)
      rw [mul_smul_comm, smul_mul_assoc] at this
      exact smul_right_injective _ (by norm_num : (1 / 2 : ℝ) ≠ 0) this
    obtain ⟨c, hc'⟩ := commute_scalar hn hc
    have hcc : c * c = 1 := by
      have := congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩
      rw [hb] at this
      simpa [hc'] using this
    have hre : ∀ i j, (α i j).re = c * (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
      intro i j
      have := congrFun (congrFun hc' i) j
      simpa [reM] using this
    have him : ∀ i j, (α i j).im = 0 := by
      intro i j
      have := congrFun (congrFun hb i) j
      simpa [imM] using this
    rcases mul_self_eq_one_iff.mp hcc with h | h
    · left
      ext i j
      apply Complex.ext
      · rw [hre i j]; by_cases hij : i = j <;> simp [h, hij, Matrix.one_apply]
      · rw [him i j]; by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
    · right
      ext i j
      apply Complex.ext
      · rw [hre i j]; by_cases hij : i = j <;> simp [h, hij, Matrix.one_apply]
      · rw [him i j]; by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  · rintro (rfl | rfl) z _
    · exact actC_one z
    · have h : ((-1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ = -1 :=
        Matrix.inv_eq_left_inv (by simp)
      simp [actC, reM_neg, imM_neg, reM_one, imM_one, h]

/-- **Lemma A1 fails for $n = 2$**: the rotation by $\pi/2$ (any element of $SO_2(\mathbb R)$, viewed in $SO_2(\mathbb C)$) fixes
$Z_{\mathbb C}$ pointwise but is not $\pm1_2$. -/
@[kb "hanke2005crelle" "Lemma A1, p. 21 (n = 2 excluded)"]
theorem lemmaA1_complex_two_false :
    ∃ α ∈ SOC 2, (∀ z ∈ ZC 2, actC α z = z) ∧ α ≠ 1 ∧ α ≠ -1 := by
  refine ⟨!![0, -1; 1, 0], ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.det_fin_two]
  · rintro z ⟨hzt, -⟩
    have h00 := congrFun (congrFun hzt 0) 0
    have h11 := congrFun (congrFun hzt 1) 1
    have h01 := congrFun (congrFun hzt 0) 1
    simp at h00 h11 h01
    have hA : reM (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) = !![0, -1; 1, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [reM]
    have hB : imM (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [imM]
    have hdet : IsUnit (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ).det := by
      simp [Matrix.det_fin_two]
    have hcomm : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) * z
        = z * !![0, -1; 1, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith
    unfold actC
    rw [hA, hB]
    simp only [sub_zero, zero_mul, add_zero, hcomm]
    rw [mul_assoc, mul_nonsing_inv _ hdet, mul_one]
  · intro h
    have := congrFun (congrFun h 0) 1
    simp at this
  · intro h
    have := congrFun (congrFun h 0) 0
    simp at this

end QuadFormsKB.Hanke2005
