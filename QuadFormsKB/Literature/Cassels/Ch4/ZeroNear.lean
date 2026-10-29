/-
# Cassels, Chapter 4, Lemma 2.8: zeros of a regular form near a given zero, off a hyperplane

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 4, *Quadratic forms over local fields*, §2,
Lemma 2.8, pp. 62–63.

**Setting.** A quadratic form in $n$ variables $x_0, \dots, x_{n-1}$ over $\mathbb{Q}_p$ is given by its coefficients
$F = (f_{ij})_{0 \le i, j < n}$, stored as a function `Fin n → Fin n → ℚ_[p]`, and takes the value
$f(\vec x) = \sum_{i,j} f_{ij} x_i x_j$ (`coeffQf F x`, from `Ch4/Perturb.lean`). It is *regular* if $f_{ij} = f_{ji}$
and $\det(f_{ij}) \ne 0$. A linear form $h(\vec x) = \sum_i h_i x_i$ is given by its coefficient vector
$(h_0, \dots, h_{n-1})$, and $h \ne 0$ means that some $h_i \ne 0$. The space $\mathbb{Q}_p^n$ carries the product
topology, which is the topology of the norm $\max_i |x_i|_p$. Indices are 0-based.

**Proves** Lemma 2.8 (`exists_zero_near_linear_ne_zero`): let $f$ be a regular form over $\mathbb{Q}_p$ in $n \ge 3$
variables, $h \ne 0$ a linear form and $\vec b$ a nontrivial zero of $f$. Then every neighbourhood of $\vec b$ contains
a zero $\vec c$ of $f$ with $h(\vec c) \ne 0$. (Then $\vec c \ne \vec 0$.) The hypothesis $n \ge 3$ is needed: for
$f = x_0 x_1$, $\vec b = (1, 0)$ and $h = x_1$ the zeros near $\vec b$ are the vectors $(t, 0)$.

**Proof** (written here; it does not follow the book's argument). Write $B(\vec x, \vec y) = \vec x \cdot F \vec y$ and
$\vec u = F \vec b \ne \vec 0$. If $h(\vec b) \ne 0$ take $\vec c = \vec b$; so assume $h(\vec b) = 0$.
1. There is $\vec e$ with $\vec u \cdot \vec e \ne 0$ and $h(\vec e) \ne 0$ (two proper hyperplanes do not cover
   $\mathbb{Q}_p^n$).
2. There is $\vec w$ with $\vec u \cdot \vec w = 0$ and $f(\vec w) \ne 0$. Since $n \ge 3$ there is $\vec v \ne \vec 0$
   with $\vec u \cdot \vec v = 0$ and $(F \vec e_0) \cdot \vec v = 0$, where $\vec u \cdot \vec e_0 = 1$. As
   $F \vec v \ne \vec 0$ there is $\vec y$ with $\vec y \cdot F \vec v \ne 0$; then
   $\vec y' = \vec y - (\vec u \cdot \vec y) \vec e_0$ satisfies $\vec u \cdot \vec y' = 0$ and
   $B(\vec y', \vec v) \ne 0$, so one of $\vec v$, $\vec y'$, $\vec v + \vec y'$ works.
3. For $\mu \in \mathbb{Q}_p$ put $\vec q_\mu = \mu \vec e + \vec w$ and
   $\vec z_\mu = \vec b - \frac{2 \mu B(\vec b, \vec e)}{f(\vec q_\mu)} \vec q_\mu$. Since $B(\vec b, \vec q_\mu)
   = \mu B(\vec b, \vec e)$, one has $f(\vec z_\mu) = 0$, and $h(\vec z_\mu) \ne 0$ whenever $\mu \ne 0$,
   $f(\vec q_\mu) \ne 0$ and $h(\vec q_\mu) \ne 0$. These hold for all small $\mu \ne 0$, and
   $\vec z_\mu \to \vec z_0 = \vec b$ as $\mu \to 0$.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Cassels.Ch4.Perturb

open Matrix Filter Topology

namespace QuadFormsKB.Cassels

section

variable {K : Type*} [Field K] {n : ℕ}

/-- The form with coefficients $F$ as a dot product: $f(\vec x) = \vec x \cdot F \vec x$. -/
theorem coeffQf_eq_dotProduct (F : Fin n → Fin n → K) (x : Fin n → K) :
    coeffQf F x = x ⬝ᵥ (Matrix.of F *ᵥ x) := by
  simp only [coeffQf, dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- For symmetric coefficients $F$, $\vec x \cdot F \vec y = \vec y \cdot F \vec x$. -/
theorem dotProduct_mulVec_comm_of_symm {F : Fin n → Fin n → K} (hsymm : ∀ i j, F i j = F j i)
    (x y : Fin n → K) : x ⬝ᵥ (Matrix.of F *ᵥ y) = y ⬝ᵥ (Matrix.of F *ᵥ x) := by
  have hT : (Matrix.of F)ᵀ = Matrix.of F := by ext i j; simp [hsymm j i]
  rw [dotProduct_mulVec, ← mulVec_transpose, hT, dotProduct_comm]

/-- For symmetric coefficients $F$, the polar value is $\sum_{i,j} f_{ij}(x_i y_j + y_i x_j) = 2\, \vec x \cdot F \vec y$. -/
theorem coeffPolar_eq_two_mul_dotProduct {F : Fin n → Fin n → K} (hsymm : ∀ i j, F i j = F j i)
    (x y : Fin n → K) : coeffPolar F x y = 2 * (x ⬝ᵥ (Matrix.of F *ᵥ y)) := by
  have h := coeffQf_add_smul F x y 1
  rw [one_smul, coeffQf_eq_dotProduct, coeffQf_eq_dotProduct, coeffQf_eq_dotProduct, mulVec_add,
    dotProduct_add, add_dotProduct, add_dotProduct, dotProduct_mulVec_comm_of_symm hsymm y x] at h
  linear_combination -h

end

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/-- **Cassels, Ch. 4, Lemma 2.8.** Let $f(\vec x) = \sum_{i,j} f_{ij} x_i x_j$ be a regular quadratic form over
$\mathbb{Q}_p$ in $n \ge 3$ variables ($f_{ij} = f_{ji}$ and $\det(f_{ij}) \ne 0$), let
$h(\vec x) = \sum_i h_i x_i$ be a linear form with coefficients $h = (h_0, \dots, h_{n-1}) \ne 0$, and let
$\vec b \ne \vec 0$ with $f(\vec b) = 0$. Then every neighbourhood $U$ of $\vec b$ in $\mathbb{Q}_p^n$ (product
topology, that is, the topology of the norm $\max_i |x_i|_p$) contains a vector $\vec c$ with $f(\vec c) = 0$ and
$h(\vec c) \ne 0$. Indices are 0-based. -/
@[kb "cassels1978" "Ch. 4, §2, Lemma 2.8, pp. 62–63"]
theorem exists_zero_near_linear_ne_zero (hn : 3 ≤ n) (F : Fin n → Fin n → ℚ_[p])
    (hsymm : ∀ i j, F i j = F j i) (hdet : (Matrix.of F).det ≠ 0)
    (h : Fin n → ℚ_[p]) (hh : h ≠ 0) (b : Fin n → ℚ_[p]) (hb : b ≠ 0) (hfb : coeffQf F b = 0) :
    ∀ U ∈ 𝓝 b, ∃ c ∈ U, coeffQf F c = 0 ∧ ∑ i, h i * c i ≠ 0 := by
  intro U hU
  by_cases hhb : h ⬝ᵥ b ≠ 0
  · exact ⟨b, mem_of_mem_nhds hU, hfb, hhb⟩
  push Not at hhb
  set M := Matrix.of F with hM
  have hsym := dotProduct_mulVec_comm_of_symm hsymm
  set u := M *ᵥ b with hu_def
  have hu : u ≠ 0 := fun h0 => hb (eq_zero_of_mulVec_eq_zero hdet h0)
  have exists_ne : ∀ v : Fin n → ℚ_[p], v ≠ 0 → ∃ x, v ⬝ᵥ x ≠ 0 := fun v hv => by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    exact ⟨Pi.single i 1, by simpa [dotProduct_single] using hi⟩
  -- Step 1: a vector off both hyperplanes `u ⬝ᵥ x = 0` and `h ⬝ᵥ x = 0`.
  obtain ⟨e, hue, hhe⟩ : ∃ e, u ⬝ᵥ e ≠ 0 ∧ h ⬝ᵥ e ≠ 0 := by
    obtain ⟨x, hx⟩ := exists_ne u hu
    obtain ⟨y, hy⟩ := exists_ne h hh
    by_cases h1 : h ⬝ᵥ x = 0
    · by_cases h2 : u ⬝ᵥ y = 0
      · exact ⟨x + y, by simpa [dotProduct_add, h2] using hx, by simpa [dotProduct_add, h1] using hy⟩
      · exact ⟨y, h2, hy⟩
    · exact ⟨x, hx, h1⟩
  -- Step 2: a vector `w` orthogonal to `b` with `f(w) ≠ 0` (uses `n ≥ 3`).
  obtain ⟨w, huw, hfw⟩ : ∃ w, u ⬝ᵥ w = 0 ∧ coeffQf F w ≠ 0 := by
    set e₀ := (u ⬝ᵥ e)⁻¹ • e with he₀
    have hue₀ : u ⬝ᵥ e₀ = 1 := by
      rw [he₀, dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hue]
    set L := Matrix.toLin' (Matrix.of ![u, M *ᵥ e₀]) with hL
    have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simp; omega)
    obtain ⟨v, hvker, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    rw [LinearMap.mem_ker, hL, Matrix.toLin'_apply] at hvker
    have hv1 : u ⬝ᵥ v = 0 := by
      have := congrFun hvker 0
      exact this
    have hv2 : (M *ᵥ e₀) ⬝ᵥ v = 0 := by
      have := congrFun hvker 1
      exact this
    have hMv : M *ᵥ v ≠ 0 := fun h0 => hv0 (eq_zero_of_mulVec_eq_zero hdet h0)
    obtain ⟨y, hy⟩ := exists_ne _ hMv
    set y' := y - (u ⬝ᵥ y) • e₀ with hy'_def
    have huy' : u ⬝ᵥ y' = 0 := by
      rw [hy'_def, dotProduct_sub, dotProduct_smul, smul_eq_mul, hue₀, mul_one, sub_self]
    have he₀v : e₀ ⬝ᵥ (M *ᵥ v) = 0 := by rw [hsym, dotProduct_comm]; exact hv2
    have hy' : y' ⬝ᵥ (M *ᵥ v) ≠ 0 := by
      rw [hy'_def, sub_dotProduct, smul_dotProduct, he₀v, smul_zero, sub_zero, dotProduct_comm]
      exact hy
    have hexp : coeffQf F (v + y') = coeffQf F v + coeffQf F y' + 2 * (y' ⬝ᵥ (M *ᵥ v)) := by
      rw [coeffQf_eq_dotProduct, coeffQf_eq_dotProduct, coeffQf_eq_dotProduct, ← hM, mulVec_add,
        dotProduct_add, add_dotProduct, add_dotProduct, hsym v y']
      ring
    by_cases h1 : coeffQf F v = 0
    · by_cases h2 : coeffQf F y' = 0
      · refine ⟨v + y', by rw [dotProduct_add, hv1, huy', add_zero], ?_⟩
        rw [hexp, h1, h2, zero_add, zero_add]
        exact mul_ne_zero two_ne_zero hy'
      · exact ⟨y', huy', h2⟩
    · exact ⟨v, hv1, h1⟩
  -- Step 3: the zeros `z μ = b + s(μ) • (μ • e + w)` of `f`, which tend to `b` as `μ → 0`.
  set P := u ⬝ᵥ e with hP
  set q : ℚ_[p] → (Fin n → ℚ_[p]) := fun μ => μ • e + w with hq
  set z : ℚ_[p] → (Fin n → ℚ_[p]) := fun μ => b + (-(2 * μ * P) / coeffQf F (q μ)) • q μ with hz
  have hqc : Continuous fun μ => coeffQf F (q μ) := by
    show Continuous fun μ : ℚ_[p] => coeffQf F (μ • e + w)
    unfold coeffQf; fun_prop
  have hq0 : coeffQf F (q 0) ≠ 0 := by simpa [hq] using hfw
  have hzc : ContinuousAt z 0 := by
    show ContinuousAt (fun μ : ℚ_[p] => b + (-(2 * μ * P) / coeffQf F (μ • e + w)) • (μ • e + w)) 0
    have hd : ContinuousAt (fun μ : ℚ_[p] => -(2 * μ * P) / coeffQf F (μ • e + w)) 0 :=
      ContinuousAt.div (by fun_prop) hqc.continuousAt hq0
    exact continuousAt_const.add (hd.smul (by fun_prop))
  have hz0 : z 0 = b := by simp [hz]
  have h1 : ∀ᶠ μ in 𝓝 (0 : ℚ_[p]), z μ ∈ U := hzc (by rw [hz0]; exact hU)
  have h2 : ∀ᶠ μ in 𝓝 (0 : ℚ_[p]), coeffQf F (q μ) ≠ 0 := hqc.continuousAt.eventually_ne hq0
  have h3 : ∀ᶠ μ in 𝓝[≠] (0 : ℚ_[p]), h ⬝ᵥ q μ ≠ 0 := by
    by_cases hw : h ⬝ᵥ w = 0
    · filter_upwards [self_mem_nhdsWithin] with μ hμ
      simp only [hq, dotProduct_add, dotProduct_smul, hw, add_zero, smul_eq_mul]
      exact mul_ne_zero hμ hhe
    · refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
      have : Continuous fun μ : ℚ_[p] => h ⬝ᵥ q μ := by
        show Continuous fun μ : ℚ_[p] => ∑ i, h i * (μ • e + w) i
        fun_prop
      exact this.continuousAt.eventually_ne (by simpa [hq] using hw)
  obtain ⟨μ, hμ0, hzU, hfq, hhq⟩ := ((eventually_mem_nhdsWithin).and ((h1.filter_mono nhdsWithin_le_nhds).and
    ((h2.filter_mono nhdsWithin_le_nhds).and h3))).exists
  have hμ0' : μ ≠ 0 := hμ0
  refine ⟨z μ, hzU, ?_, ?_⟩
  · have hbq : b ⬝ᵥ (M *ᵥ q μ) = μ * P := by
      rw [hsym, ← hu_def, hq]
      simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_comm w u, huw, add_zero,
        dotProduct_comm e u, hP]
    simp only [hz]
    rw [coeffQf_add_smul, hfb, coeffPolar_eq_two_mul_dotProduct hsymm, ← hM, hbq]
    field_simp
    ring
  · show h ⬝ᵥ z μ ≠ 0
    simp only [hz, dotProduct_add, dotProduct_smul, hhb, zero_add, smul_eq_mul]
    exact mul_ne_zero (div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero two_ne_zero hμ0') hue)) hfq) hhq

end QuadFormsKB.Cassels
