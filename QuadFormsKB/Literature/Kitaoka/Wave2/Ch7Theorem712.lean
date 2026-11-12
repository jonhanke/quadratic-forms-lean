/-
# Kitaoka 1993, Section 7.1: Theorem 7.1.2 (positive lattices with small minimum are of E-type)

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §7.1, Theorem 7.1.2, p. 194 (printed page).

**Proves**
* `false_of_large_rank`: a minimal vector $X = PR$ of $L \otimes M$ with $P$ injective and $R$ of full row rank
  $r \ge 40$ cannot exist when $\mu_r < r/6$, $L$ is integral and $\min(L) \le 6$;
* `theorem712_of_lemmas`: **conditional** on the stated inputs `Lemma712` ($\mu_r < \sqrt r$ for $2 \le r < 43$) and
  `Lemma714` ($\mu_n < n/6$ for $n \ge 40$), every positive lattice with integral Gram matrix and a nonzero vector
  $x$ with $Q(x) \le 6$ is of E-type (`Theorem712`).

**Proof** (Kitaoka's). Let $X$ be a minimal vector of $L \otimes M$ and write $X = PR$ with $P$ injective and $R$ of
full row rank $r$ (`exists_factor`). If $r = 0$ then $X = 0$, excluded; if $r = 1$ then $X$ is split. If
$2 \le r \le 42$, `false_of_rank_ge_two` and `Lemma712` give a contradiction. If $r \ge 43$ (so $r \ge 40$), the Gram
matrix $G_A = P^{\mathsf T} A P$ is a positive definite integer matrix, so $\det G_A \ge 1$. By Hermite's bound
(`exists_lt_hermite`) and `Lemma714`, for $\mu_r < c < r/6$ there is $y \ne 0$ with
$G_B[y] < c(\det G_B)^{1/r}$ where $G_B = R B R^{\mathsf T}$, and $G_B[y] = Q_B(R^{\mathsf T}y) \ge \min(M)$.
Hence, by Lemma 7.1.3 (`lemma713`), $Q(X) = \operatorname{tr}(G_A G_B) \ge r(\det G_A\det G_B)^{1/r}
\ge r(\det G_B)^{1/r} > 6\min(M)$, whereas $Q(X) \le Q(x \otimes y_0) = Q_A(x)\min(M) \le 6\min(M)$ for a minimal
vector $y_0$ of $M$. All indices are 0-based.
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import QuadFormsKB.Literature.Kitaoka.Ch7EType
import QuadFormsKB.Literature.Kitaoka.Ch7TraceInequality
import QuadFormsKB.Literature.Kitaoka.Wave2.Ch7Theorem711
import QuadFormsKB.Literature.Kitaoka.Wave2.Ch7Lemma711

open Matrix

noncomputable section

namespace QuadFormsKB.Kitaoka.EType

/-- **Core of Kitaoka's argument for Theorem 7.1.2.** A minimal vector $X = PR$ of $L \otimes M$ with $P$ injective
and $R$ of full row rank $r \ge 40$ cannot exist when $\mu_r < r/6$, the Gram matrix $A$ of $L$ is integral, and
$Q_A(x) \le 6$ for some nonzero $x$. -/
theorem false_of_large_rank {n m r : ℕ} (hr : 40 ≤ r) (hμ : Reduction.hermiteConst r < (r : ℝ) / 6)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsPosGram A) (hAint : ∀ i j, ∃ z : ℤ, A i j = z)
    (B : Matrix (Fin m) (Fin m) ℚ) (hB : IsPosGram B)
    (X : Matrix (Fin n) (Fin m) ℤ) (hX : IsMinimalTensor A B X)
    (P : Matrix (Fin n) (Fin r) ℤ) (R : Matrix (Fin r) (Fin m) ℤ) (hXPR : X = P * R)
    (hP : ∀ v, P *ᵥ v = 0 → v = 0) (hR : ∀ y : Fin r → ℤ, y ᵥ* R = 0 → y = 0)
    (x : Fin n → ℤ) (hx0 : x ≠ 0) (hx6 : gramQ A x ≤ 6) : False := by
  have hr2 : 2 ≤ r := by omega
  obtain ⟨A', hA'⟩ : ∃ A' : Matrix (Fin n) (Fin n) ℤ, A = A'.map (Int.cast : ℤ → ℚ) :=
    ⟨fun i j => (hAint i j).choose, by ext i j; exact (hAint i j).choose_spec⟩
  have hC : ∀ y, Rᵀ *ᵥ y = 0 → y = 0 := fun y h => hR y (by rwa [Matrix.mulVec_transpose] at h)
  set GA := (qmat P)ᵀ * A * qmat P with hGA
  set GB := (qmat Rᵀ)ᵀ * B * qmat Rᵀ with hGB
  have hGApos : IsPosGram GA := isPosGram_conj P hP A hA
  have hGBpos : IsPosGram GB := isPosGram_conj Rᵀ hC B hB
  set GAr := GA.map (Rat.cast : ℚ → ℝ) with hGAr
  set GBr := GB.map (Rat.cast : ℚ → ℝ) with hGBr
  have hAr : GAr.PosDef := posDef_ratCast GA hGApos
  have hBr : GBr.PosDef := posDef_ratCast GB hGBpos
  have hT : (tensorQ A B X : ℝ) = (GAr * GBr).trace := by
    rw [tensorQ_factor A B hB.1 X P R hXPR]
    have hmap : (GA * GB).map (Rat.cast : ℚ → ℝ) = GAr * GBr := Matrix.map_mul (f := Rat.castHom ℝ)
    have hGG : (qmat P)ᵀ * A * qmat P * ((qmat Rᵀ)ᵀ * B * qmat Rᵀ) = GA * GB := rfl
    rw [hGG, ← hmap]
    simp [Matrix.trace, Matrix.diag]
  have h713 := lemma713 r GAr GBr hAr hBr
  rw [← hT] at h713
  -- det G_A ≥ 1
  have hdA1 : (1 : ℝ) ≤ GAr.det := by
    have hGAint : GAr = (Pᵀ * A' * P).map (Int.cast : ℤ → ℝ) := by
      ext i j
      simp [hGAr, hGA, hA', qmat, Matrix.mul_apply, Matrix.transpose_apply]
    have h1 : GAr.det = (((Pᵀ * A' * P).det : ℤ) : ℝ) := by
      rw [hGAint]
      have := (Int.castRingHom ℝ).map_det (Pᵀ * A' * P)
      simpa using this.symm
    have hpos := hAr.det_pos
    rw [h1] at hpos ⊢
    have : (0 : ℤ) < (Pᵀ * A' * P).det := by exact_mod_cast hpos
    exact_mod_cast this
  have hdB := hBr.det_pos
  -- Hermite for G_B
  set μ := Reduction.hermiteConst r with hμdef
  set c : ℝ := (μ + (r : ℝ) / 6) / 2 with hc
  have hc1 : μ < c := by rw [hc]; linarith
  have hc2 : c < (r : ℝ) / 6 := by rw [hc]; linarith
  obtain ⟨y', hy'0, hy'⟩ := exists_lt_hermite hr2 GBr hBr c hc1
  have hb : (fun i => (y' i : ℝ)) ⬝ᵥ (GBr *ᵥ fun i => (y' i : ℝ)) = ((gramQ B (Rᵀ *ᵥ y') : ℚ) : ℝ) := by
    rw [hGBr, cast_quad, hGB, quad_conj_gramQ]
  rw [hb] at hy'
  have hRy : Rᵀ *ᵥ y' ≠ 0 := fun h => hy'0 (hC _ h)
  obtain ⟨y0, hy0⟩ := exists_isMinimalVector hB hRy
  have hq0 : (0 : ℚ) < gramQ B y0 := gramQ_pos hB hy0.1
  have hq0le : gramQ B y0 ≤ gramQ B (Rᵀ *ᵥ y') := hy0.2 _ hRy
  have hmin : tensorQ A B X ≤ gramQ A x * gramQ B y0 := by
    rw [← tensorQ_vecMulVec]
    exact hX.2 _ (vecMulVec_ne_zero hx0 hy0.1)
  have hmin6 : tensorQ A B X ≤ 6 * gramQ B y0 :=
    hmin.trans (mul_le_mul_of_nonneg_right hx6 hq0.le)
  have hmin6R : (tensorQ A B X : ℝ) ≤ 6 * ((gramQ B y0 : ℚ) : ℝ) := by exact_mod_cast hmin6
  have hq0leR : ((gramQ B y0 : ℚ) : ℝ) ≤ ((gramQ B (Rᵀ *ᵥ y') : ℚ) : ℝ) := by exact_mod_cast hq0le
  have hd : 0 < GBr.det ^ ((1 : ℝ) / r) := Real.rpow_pos_of_pos hdB _
  have hmono : GBr.det ^ ((1 : ℝ) / r) ≤ (GAr.det * GBr.det) ^ ((1 : ℝ) / r) :=
    Real.rpow_le_rpow hdB.le (le_mul_of_one_le_left hdB.le hdA1) (by positivity)
  have hrpos : (0 : ℝ) ≤ r := by positivity
  have h1 : (r : ℝ) * GBr.det ^ ((1 : ℝ) / r) ≤ (tensorQ A B X : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left hmono hrpos) h713
  have h2 : 6 * c * GBr.det ^ ((1 : ℝ) / r) < (r : ℝ) * GBr.det ^ ((1 : ℝ) / r) :=
    mul_lt_mul_of_pos_right (by linarith) hd
  nlinarith

/-- **Kitaoka 1993, Theorem 7.1.2 from Lemmas 7.1.2 and 7.1.4** (p. 194): a positive lattice with integral Gram
matrix and a nonzero vector $x$ with $Q(x) \le 6$ is of E-type, *conditional on the stated inputs* `Lemma712`
($\mu_r < \sqrt r$ for $2 \le r < 43$) and `Lemma714` ($\mu_n < n/6$ for $n \ge 40$). *Proof* (Kitaoka's): for a
minimal vector $X = PR$ of $L \otimes M$ of rank $r$, $r \le 1$ gives a split vector, $2 \le r \le 42$ is excluded by
`false_of_rank_ge_two`, and $r \ge 43$ by `false_of_large_rank`. -/
@[kb "kitaoka1993" "§7.1, Thm. 7.1.2, p. 194 (from Lemmas 7.1.2, 7.1.4)"]
theorem theorem712_of_lemmas (h712 : Lemma712) (h714 : Lemma714) : Theorem712 := by
  intro n A hA hAint ⟨x, hx0, hx6⟩ m B hB X hX
  obtain ⟨r, P, R, hXPR, hP, hR⟩ := exists_factor X
  rcases Nat.lt_or_ge r 2 with h | h
  · interval_cases r
    · exfalso
      apply hX.1
      rw [hXPR]
      ext i j
      simp [Matrix.mul_apply]
    · exact ⟨fun i => P i 0, R 0, by ext i j; simp [hXPR, Matrix.mul_apply, vecMulVec_apply]⟩
  · exfalso
    rcases Nat.lt_or_ge r 43 with h43 | h43
    · exact false_of_rank_ge_two h (h712 r h h43) A hA B hB X hX P R hXPR hP hR
    · exact false_of_large_rank (by omega) (h714 r (by omega)) A hA hAint B hB X hX P R hXPR hP hR x hx0 hx6

end QuadFormsKB.Kitaoka.EType
