/-
# Cassels, Chapter 5, §2: simultaneous approximation

**Proves** (Cassels, *Rational Quadratic Forms*, Chapter 5)
* Corollary to Theorem 2.4 (Dirichlet's simultaneous approximation): `simultaneous_approximation`.

**Proof notes.** As Cassels': Minkowski's linear forms theorem (`minkowski_linear_forms_at`) applied to the $n + 1$ forms
$L_j(\vec x) = \theta_j x_n - x_j$ ($0 \le j < n$) and $L_n(\vec x) = x_n$, of determinant $\pm 1$, with
$t_j = M^{-1/n}$ and $t_n = M$ (the non-strict inequality at the index $n$). Indices are $0, \dots, n - 1$ for the
$\theta_j$ (Cassels: $1, \dots, n$), and the variable $x_n$ (Cassels' $x_{n+1}$) carries $m$.
-/
import QuadFormsKB.Literature.Cassels.Ch5.Minkowski

namespace QuadFormsKB.Cassels.Ch5

open Matrix

/-- **Cassels, Ch. 5, Corollary to Theorem 2.4** (simultaneous approximation): *let $n \ge 1$ and $M > 1$ and let
$\theta_0, \dots, \theta_{n-1}$ be real numbers; then there is an integer $m$ with $0 < m \le M$ and integers
$l_0, \dots, l_{n-1}$ with $\lvert\theta_j m - l_j\rvert < M^{-1/n}$ for all $j$.* Cassels takes $M$ an integer;
here $M$ is any real number $> 1$ (a generalization; the proof is the same). This is a variant: the page image
(p. 71) shows Cassels' (2.8)–(2.9) as $0 < m < M$ and $\lvert m\theta_j - l_j\rvert \le M^{-1/n}$ (the strict
inequality on $m$, the non-strict ones on the approximations), stated as printed in
`simultaneous_approximation_printed` (`Ch5/Supplement.lean`); here the non-strict inequality of Theorem 2.4 is put on
$m$ instead. -/
@[kb "cassels1978" "Ch. 5, Cor. to Thm. 2.4, pp. 71–72 (variant: m ≤ M and strict approximations)"]
theorem simultaneous_approximation {n : ℕ} (hn : 1 ≤ n) (θ : Fin n → ℝ) {M : ℝ} (hM : 1 < M) :
    ∃ m : ℤ, 0 < m ∧ (m : ℝ) ≤ M ∧ ∃ l : Fin n → ℤ, ∀ j, |θ j * m - l j| < M ^ (-(1 / n : ℝ)) := by
  classical
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hM0 : 0 < M := by linarith
  set D : ℝ := M ^ (-(1 / n : ℝ)) with hD
  have hDpos : 0 < D := Real.rpow_pos_of_pos hM0 _
  have hD1 : D < 1 := Real.rpow_lt_one_of_one_lt_of_neg hM (by
    have : 0 < (1 / n : ℝ) := by positivity
    linarith)
  set θ' : Fin (n + 1) → ℝ := fun i => if h : i.val < n then θ ⟨i.val, h⟩ else 0 with hθ'
  have hθ'last : θ' (Fin.last n) = 0 := by simp [hθ']
  have hθ'cast : ∀ j : Fin n, θ' j.castSucc = θ j := fun j => by simp [hθ']
  set v : Fin (n + 1) → ℝ := Pi.single (Fin.last n) 1 with hv
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    -(1 + Matrix.replicateCol (Fin 1) (fun i => -θ' i) * Matrix.replicateRow (Fin 1) v) with hA
  have hAv : ∀ x : Fin (n + 1) → ℝ, ∀ i, (A *ᵥ x) i = θ' i * x (Fin.last n) - x i := by
    intro x i
    simp only [hA, Matrix.neg_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      Pi.neg_apply, Pi.add_apply]
    have : (Matrix.replicateCol (Fin 1) (fun i => -θ' i) *ᵥ (Matrix.replicateRow (Fin 1) v *ᵥ x)) i
        = -θ' i * x (Fin.last n) := by
      simp [Matrix.mulVec, dotProduct, hv, Pi.single_apply]
    rw [this]; ring
  have hdet : |A.det| = 1 := by
    have h := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) (fun i => -θ' i) v
    rw [hA, Matrix.det_neg]
    erw [h]
    have : v ⬝ᵥ (fun i => -θ' i) = 0 := by simp [hv, hθ'last]
    rw [this]; simp
  have hdet0 : A.det ≠ 0 := fun h => by rw [h, abs_zero] at hdet; norm_num at hdet
  set t : Fin (n + 1) → ℝ := fun j => if j = Fin.last n then M else D with ht
  have htpos : ∀ j, 0 < t j := fun j => by simp only [ht]; split_ifs <;> assumption
  have hprod : |A.det| ≤ ∏ j, t j := by
    rw [hdet, ← Finset.mul_prod_erase _ _ (Finset.mem_univ (Fin.last n))]
    have : ∏ j ∈ Finset.univ.erase (Fin.last n), t j = D ^ n := by
      rw [Finset.prod_congr rfl (fun j hj => by simp [ht, Finset.ne_of_mem_erase hj] :
        ∀ j ∈ Finset.univ.erase (Fin.last n), t j = D)]
      simp
    rw [this]
    simp only [ht, ite_true]
    rw [hD, ← Real.rpow_natCast, ← Real.rpow_mul hM0.le,
      neg_mul, one_div, inv_mul_cancel₀ hnr.ne', Real.rpow_neg_one, mul_inv_cancel₀ hM0.ne']
  obtain ⟨a, ha0, hal, haj⟩ := minkowski_linear_forms_at (Fin.last n) A hdet0 t htpos hprod
  set x : Fin (n + 1) → ℝ := fun i => (a i : ℝ) with hx
  have hlast : |(a (Fin.last n) : ℝ)| ≤ M := by
    have := hal; rw [hAv] at this; simpa [ht, hθ'last] using this
  have hj : ∀ j : Fin n, |θ j * (a (Fin.last n) : ℝ) - a j.castSucc| < D := by
    intro j
    have := haj j.castSucc (Fin.castSucc_ne_last j)
    rw [hAv, hθ'cast] at this
    simpa [ht, Fin.castSucc_ne_last j] using this
  have hm0 : a (Fin.last n) ≠ 0 := by
    intro h0
    apply ha0
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using h0
    · have := hj j
      rw [h0] at this
      simp only [Int.cast_zero, mul_zero, zero_sub, abs_neg] at this
      have h1 : |(a j.castSucc : ℝ)| < 1 := this.trans hD1
      have : |a j.castSucc| < 1 := by exact_mod_cast h1
      simpa using abs_lt.1 this |>.1 |> fun h => by
        have := abs_lt.1 ‹|a j.castSucc| < 1›
        omega
  rcases lt_or_gt_of_ne hm0 with hneg | hpos
  · have hnegr : (a (Fin.last n) : ℝ) < 0 := by exact_mod_cast hneg
    refine ⟨-a (Fin.last n), by omega, ?_, fun j => -a j.castSucc, fun j => ?_⟩
    · have := abs_of_neg hnegr
      push_cast
      rw [← this]; exact hlast
    · have := hj j
      push_cast
      rw [← abs_neg]; convert this using 2; ring
  · refine ⟨a (Fin.last n), hpos, ?_, fun j => a j.castSucc, hj⟩
    exact (le_abs_self _).trans hlast
