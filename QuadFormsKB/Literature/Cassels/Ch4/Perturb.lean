/-
# Cassels, Chapter 4, §2: small perturbations of a form with a nontrivial zero over $\mathbb{Q}_p$

Source: none (a lemma derived in this repository). It is filed with Cassels, *Rational Quadratic Forms* (1978),
Chapter 4, *Quadratic forms over local fields*, §2, pp. 62–63, as context only: the statement is not in the book.

**Setting.** A quadratic form in $n$ variables $x_0, \dots, x_{n-1}$ over $\mathbb{Q}_p$ is given by its coefficients
$F = (f_{ij})_{0 \le i, j < n}$, stored as a function `Fin n → Fin n → ℚ_[p]`, and takes the value
$f(\vec x) = \sum_{i,j} f_{ij} x_i x_j$ (`coeffQf F x`). It is *nondegenerate* if $f_{ij} = f_{ji}$ and
$\det(f_{ij}) \ne 0$. Indices are 0-based.

**Proves** `exists_delta_isotropic_of_nondegenerate` (stability of isotropy under small perturbation of the
coefficients): if a nondegenerate form $f$ over $\mathbb{Q}_p$ has a nontrivial zero, there is $\delta > 0$ such that
every form $g$ with $|g_{ij} - f_{ij}|_p < \delta$ for all $i, j$ has a nontrivial zero. The perturbed coefficient
matrix $G$ is not required to be symmetric.

*Erratum (in this repository's citation):* this theorem was first tagged as Cassels, Ch. 4, Lemma 2.8, pp. 62–63. The
printed page check of 2026-10-27 showed that the printed Lemma 2.8 is a different statement (for a regular form $f$
over $\mathbb{Q}_p$ in $n \ge 3$ variables, a linear form $h \ne 0$ and a nontrivial zero $\vec b$ of $f$, every
neighbourhood of $\vec b$ contains a zero $\vec c$ of $f$ with $h(\vec c) \ne 0$). That statement is formalized as
`exists_zero_near_linear_ne_zero` in `Ch4/ZeroNear.lean`; the tag here now has relation *background*.

**Proof.** Let $\vec a \ne 0$ be a zero of $f$. Since $F$ is invertible, $F \vec a \ne 0$, so for a suitable standard
basis vector $\vec c = \vec e_j$ the polar value $L_f = \sum f_{ik}(a_i c_k + c_i a_k) = 2 (F\vec a)_j$ is nonzero. For
any $g$ one has $g(\vec a + t\vec c) = g(\vec a) + t L_g + t^{2} g(\vec c)$, with discriminant
$D_g = L_g^{2} - 4 g(\vec a) g(\vec c)$. The map $G \mapsto D_G$ is continuous and $D_F = L_f^{2}$, so for $G$ near $F$
the ratio $D_G / L_f^{2}$ is within $|2|^{2}/8$ of $1$, hence is a square (contraction mapping, `isSquare_near_one`),
so $D_G = \sigma^{2}$. If $g(\vec c) = 0$ then $\vec c$ is a nontrivial zero. Otherwise
$t = (\sigma - L_g) / (2 g(\vec c))$ gives $g(\vec a + t\vec c) = 0$, and $\vec a + t\vec c \neq 0$ since otherwise
$D_g = 0$, contradicting $D_G \ne 0$ (which holds because $D_G$ is close to $L_f^{2} \ne 0$).
-/
import Mathlib
import QuadFormsKB.Citation

open Matrix

namespace QuadFormsKB.Cassels

/-- Squares near $1$ in a complete normed field in which $2 \ne 0$ (contraction mapping): if
$\lVert u - 1 \rVert < \lVert 2 \rVert^{2} / 8$ then $u$ is a square. -/
theorem isSquare_near_one {K : Type*} [NormedField K] [CompleteSpace K] (h2 : (2 : K) ≠ 0) {u : K}
    (hu : ‖u - 1‖ < ‖(2 : K)‖ ^ 2 / 8) : IsSquare u := by
  have hn : 0 < ‖(2:K)‖ := norm_pos_iff.mpr h2
  set nn := ‖(2:K)‖ with hn_def
  set c := u - 1
  let f : K → K := fun y => (c - y ^ 2) / 2
  let s := Metric.closedBall (0:K) (nn / 4)
  have hmaps : Set.MapsTo f s s := by
    intro y hy
    simp only [s, Metric.mem_closedBall, dist_zero_right] at hy ⊢
    simp only [f, norm_div]
    rw [div_le_iff₀ hn]
    calc ‖c - y ^ 2‖ ≤ ‖c‖ + ‖y‖ ^ 2 := by
          refine (norm_sub_le _ _).trans ?_; rw [norm_pow]
      _ ≤ nn ^ 2 / 8 + (nn / 4) ^ 2 := by gcongr
      _ ≤ nn / 4 * nn := by nlinarith
  have hcon : ContractingWith (1/2 : NNReal) (hmaps.restrict f s s) := by
    refine ⟨one_half_lt_one, LipschitzWith.of_dist_le_mul fun y y' => ?_⟩
    have hy := y.2; have hy' := y'.2
    simp only [s, Metric.mem_closedBall, dist_zero_right] at hy hy'
    change dist (f (y:K)) (f y') ≤ ((1/2 : NNReal) : ℝ) * dist (y:K) y'
    simp only [dist_eq_norm, f]
    have : (c - (y:K) ^ 2) / 2 - (c - (y':K) ^ 2) / 2 = -((y:K) - y') * ((y:K) + y') / 2 := by ring
    rw [this, norm_div, norm_mul, norm_neg, div_le_iff₀ hn]
    have : ‖(y:K) + y'‖ ≤ nn / 2 := (norm_add_le _ _).trans (by linarith)
    push_cast
    calc ‖(y:K) - y'‖ * ‖(y:K) + y'‖ ≤ ‖(y:K) - y'‖ * (nn / 2) := by gcongr
      _ = 1/2 * ‖(y:K) - ↑y'‖ * nn := by ring
  obtain ⟨y, -, hfix, -⟩ := ContractingWith.exists_fixedPoint' (Metric.isClosed_closedBall.isComplete)
    hmaps hcon (x := 0) (by simp [s]; positivity) (edist_ne_top _ _)
  refine ⟨1 + y, ?_⟩
  have : f y = y := hfix
  simp only [f] at this
  have h2' : (2:K) * y = c - y ^ 2 := by
    have h3 : (2:K) * ((c - y ^ 2) / 2) = 2 * y := by rw [this]
    rw [mul_div_cancel₀ _ h2] at h3
    exact h3.symm
  simp only [c] at h2'
  linear_combination -h2'

section

variable {K : Type*} [Field K] {n : ℕ}

/-- The quadratic form with coefficients $F = (f_{ij})$: $f(\vec x) = \sum_{i,j} f_{ij} x_i x_j$. -/
def coeffQf (F : Fin n → Fin n → K) (x : Fin n → K) : K := ∑ i, ∑ j, F i j * x i * x j

/-- The polar value of the form with coefficients $F = (f_{ij})$:
$\sum_{i,j} f_{ij} (x_i y_j + y_i x_j)$, which equals $2 B_f(\vec x, \vec y)$ when $F$ is symmetric. -/
def coeffPolar (F : Fin n → Fin n → K) (x y : Fin n → K) : K :=
  ∑ i, ∑ j, F i j * (x i * y j + y i * x j)

theorem coeffQf_add_smul (F : Fin n → Fin n → K) (a c : Fin n → K) (t : K) :
    coeffQf F (a + t • c) = coeffQf F a + t * coeffPolar F a c + t ^ 2 * coeffQf F c := by
  simp only [coeffQf, coeffPolar, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem coeffQf_smul (F : Fin n → Fin n → K) (c : Fin n → K) (t : K) : coeffQf F (t • c) = t ^ 2 * coeffQf F c := by
  simp only [coeffQf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

theorem continuous_discr (a c : Fin n → ℚ_[p]) :
    Continuous (fun G : Fin n → Fin n → ℚ_[p] => coeffPolar G a c ^ 2 - 4 * coeffQf G a * coeffQf G c) := by
  unfold coeffPolar coeffQf
  fun_prop

/-- **Stability of isotropy under perturbation** (derived in this repository; not a statement of Cassels; context:
Cassels, Ch. 4, §2, pp. 62–63; the printed Lemma 2.8 there is `exists_zero_near_linear_ne_zero`). Let
$f(\vec x) = \sum_{i,j} f_{ij} x_i x_j$ be a nondegenerate quadratic form over $\mathbb{Q}_p$ in $n$ variables
($f_{ij} = f_{ji}$ and $\det(f_{ij}) \ne 0$) which has a nontrivial zero. Then there is $\delta > 0$ such that every
quadratic form $g(\vec x) = \sum_{i,j} g_{ij} x_i x_j$ over $\mathbb{Q}_p$ with $|g_{ij} - f_{ij}|_p < \delta$ for
all $i, j$ also has a nontrivial zero. -/
@[kb "cassels1978" "Ch. 4, §2, pp. 62–63 (context only; this statement is not in the book)"]
theorem exists_delta_isotropic_of_nondegenerate (F : Fin n → Fin n → ℚ_[p])
    (hsymm : ∀ i j, F i j = F j i) (hdet : (Matrix.of F).det ≠ 0)
    (hiso : ∃ x : Fin n → ℚ_[p], x ≠ 0 ∧ coeffQf F x = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ G : Fin n → Fin n → ℚ_[p], (∀ i j, ‖G i j - F i j‖ < δ) →
      ∃ x : Fin n → ℚ_[p], x ≠ 0 ∧ coeffQf G x = 0 := by
  obtain ⟨a, ha0, haF⟩ := hiso
  have hFa : (Matrix.of F) *ᵥ a ≠ 0 := fun h => ha0 (Matrix.eq_zero_of_mulVec_eq_zero hdet h)
  obtain ⟨j, hj⟩ : ∃ j, ((Matrix.of F) *ᵥ a) j ≠ 0 := by
    by_contra h; push_neg at h; exact hFa (funext h)
  set c : Fin n → ℚ_[p] := Pi.single j 1 with hc
  have hc0 : c ≠ 0 := by
    intro h; have := congrFun h j; simp [hc] at this
  have hL : coeffPolar F a c = 2 * ((Matrix.of F) *ᵥ a) j := by
    simp only [coeffPolar, hc, mul_add, Finset.sum_add_distrib, Pi.single_apply, mulVec, dotProduct,
      Matrix.of_apply]
    simp [mul_ite, Finset.sum_ite_eq', hsymm _ j]
    ring
  have h2 : (2 : ℚ_[p]) ≠ 0 := two_ne_zero
  have hL0 : coeffPolar F a c ≠ 0 := by rw [hL]; exact mul_ne_zero h2 hj
  have hD : coeffPolar F a c ^ 2 - 4 * coeffQf F a * coeffQf F c = coeffPolar F a c ^ 2 := by rw [haF]; ring
  have hLn : 0 < ‖coeffPolar F a c ^ 2‖ := norm_pos_iff.mpr (pow_ne_zero 2 hL0)
  have h2le : ‖(2 : ℚ_[p])‖ ≤ 1 := by exact_mod_cast Padic.norm_int_le_one (p := p) 2
  set ε₀ := ‖coeffPolar F a c ^ 2‖ * (‖(2 : ℚ_[p])‖ ^ 2 / 8) with hε₀
  have h2pos : 0 < ‖(2 : ℚ_[p])‖ := norm_pos_iff.mpr h2
  have hε₀pos : 0 < ε₀ := by positivity
  have hopen : IsOpen {G : Fin n → Fin n → ℚ_[p] |
      ‖(coeffPolar G a c ^ 2 - 4 * coeffQf G a * coeffQf G c) - coeffPolar F a c ^ 2‖ < ε₀} :=
    isOpen_lt (by have := continuous_discr (p := p) a c; fun_prop) continuous_const
  have hFmem : F ∈ {G : Fin n → Fin n → ℚ_[p] |
      ‖(coeffPolar G a c ^ 2 - 4 * coeffQf G a * coeffQf G c) - coeffPolar F a c ^ 2‖ < ε₀} := by
    simp only [Set.mem_setOf_eq, hD, sub_self, norm_zero]; exact hε₀pos
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen F hFmem
  refine ⟨ε, hε, fun G hG => ?_⟩
  have hGmem : G ∈ Metric.ball F ε := by
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro i
    rw [dist_pi_lt_iff hε]
    intro k
    simpa [dist_eq_norm] using hG i k
  have hclose := hball hGmem
  simp only [Set.mem_setOf_eq] at hclose
  set D := coeffPolar G a c ^ 2 - 4 * coeffQf G a * coeffQf G c with hDdef
  have hratio : ‖D / coeffPolar F a c ^ 2 - 1‖ < ‖(2 : ℚ_[p])‖ ^ 2 / 8 := by
    have : D / coeffPolar F a c ^ 2 - 1 = (D - coeffPolar F a c ^ 2) / coeffPolar F a c ^ 2 := by
      field_simp
    rw [this, norm_div, div_lt_iff₀ hLn]
    simpa [hε₀, mul_comm] using hclose
  obtain ⟨s, hs⟩ := isSquare_near_one h2 hratio
  have hDsq : D = (s * coeffPolar F a c) ^ 2 := by
    have : D / coeffPolar F a c ^ 2 = s * s := hs
    field_simp at this
    linear_combination this
  have hD0 : D ≠ 0 := by
    intro h0
    rw [h0, zero_sub, norm_neg] at hclose
    have : ε₀ ≤ ‖coeffPolar F a c ^ 2‖ := by
      rw [hε₀]
      have : ‖(2 : ℚ_[p])‖ ^ 2 / 8 ≤ 1 := by nlinarith
      nlinarith
    linarith
  by_cases hqc : coeffQf G c = 0
  · exact ⟨c, hc0, hqc⟩
  · set σ := s * coeffPolar F a c with hσ
    set L := coeffPolar G a c
    set t := (σ - L) / (2 * coeffQf G c) with ht
    refine ⟨a + t • c, ?_, ?_⟩
    · intro hx
      have hat : a = (-t) • c := by
        rw [neg_smul]; exact eq_neg_of_add_eq_zero_left hx
      have h1 : coeffQf G a = t ^ 2 * coeffQf G c := by rw [hat, coeffQf_smul]; ring
      have h3 : coeffQf G (a + (1 : ℚ_[p]) • c) = (1 - t) ^ 2 * coeffQf G c := by
        have : a + (1 : ℚ_[p]) • c = (1 - t) • c := by
          rw [hat, sub_smul, one_smul, neg_smul]; abel
        rw [this, coeffQf_smul]
      rw [coeffQf_add_smul, h1] at h3
      have hLt : L = -2 * t * coeffQf G c := by
        have : coeffPolar G a c = (1 - t) ^ 2 * coeffQf G c - t ^ 2 * coeffQf G c - 1 ^ 2 * coeffQf G c := by
          linear_combination h3
        show coeffPolar G a c = _
        linear_combination this
      apply hD0
      rw [hDdef, h1, hLt]; ring
    · rw [coeffQf_add_smul]
      have hq2 : (2 : ℚ_[p]) * coeffQf G c ≠ 0 := mul_ne_zero h2 hqc
      have hDs : D = σ ^ 2 := hDsq
      have hDe : D = L ^ 2 - 4 * coeffQf G a * coeffQf G c := rfl
      have : coeffQf G a = (L ^ 2 - σ ^ 2) / (4 * coeffQf G c) := by
        field_simp; linear_combination hDe.symm.trans hDs |>.symm
      rw [this, ht]
      field_simp
      ring

end QuadFormsKB.Cassels
