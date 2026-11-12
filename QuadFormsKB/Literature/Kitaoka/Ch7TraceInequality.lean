/-
# Kitaoka 1993, Section 7.1: proof of Lemma 7.1.3 (the trace inequality)

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §7.1, Lemma 7.1.3, p. 193.

**Proves** `lemma713 : Lemma713`: for positive definite real symmetric $n \times n$ matrices $A$, $B$,
$$\operatorname{tr}(AB) \ge n\,(\det A \det B)^{1/n}.$$

**Proof.** By the spectral theorem $A = U\,\mathrm{diag}(\lambda)\,{}^tU$ with $U$ orthogonal and every eigenvalue
$\lambda_i > 0$. Put $C = \mathrm{diag}(\sqrt{\lambda})\,{}^tU$, so that $A = {}^tC\,C$ and $C$ is invertible. Then
$\operatorname{tr}(AB) = \operatorname{tr}({}^tC\,C B) = \operatorname{tr}(C B\,{}^tC)$, the matrix $M = C B\,{}^tC$
is positive definite, and $\det M = \det({}^tC\,C)\det B = \det A \det B$. If $\mu_1, \dots, \mu_n > 0$ are the
eigenvalues of $M$, then $\operatorname{tr} M = \sum_i \mu_i$ and $\det M = \prod_i \mu_i$, and the inequality is the
arithmetic-geometric mean inequality $\frac1n \sum_i \mu_i \ge (\prod_i \mu_i)^{1/n}$ (Mathlib
`Real.geom_mean_le_arith_mean_weighted`). For $n = 0$ both sides are $0$.

**Also proves** `lemma712_of_le_eight`: Lemma 7.1.2 ($\mu_r < \sqrt r$) in the range $2 \le r \le 8$, from Hermite's
bound $\mu_r \le (4/3)^{(r-1)/2}$ (`Reduction.hermiteConst_le`, Theorem 2.1.1), since $(4/3)^{r-1} < r$ for
$2 \le r \le 8$ (at $r = 9$ it fails: $(4/3)^8 \approx 9.99$). Kitaoka's proof of the full range $r < 43$ uses
Blichfeldt's bound (§2.2), not formalized here.
-/
import QuadFormsKB.Literature.Kitaoka.Ch7EType
import QuadFormsKB.Literature.Kitaoka.Ch2Theorem211
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities

open Matrix

noncomputable section

namespace QuadFormsKB.Kitaoka.EType

/-- **Kitaoka 1993, Lemma 7.1.3** (p. 193), *proved*: for positive definite real symmetric $n \times n$ matrices $A$,
$B$, $\operatorname{tr}(AB) \ge n\,(\det A \det B)^{1/n}$. See the module docstring for the proof (spectral theorem
for $A$, then the arithmetic-geometric mean inequality for the eigenvalues of $C B\,{}^tC$, where $A = {}^tC\,C$). -/
@[kb "kitaoka1993" "§7.1, Lemma 7.1.3, p. 193"]
theorem lemma713 : Lemma713 := by
  intro n A B hA hB
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Matrix.trace]
  set U : Matrix (Fin n) (Fin n) ℝ := (hA.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hUdef
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  set lam := hA.1.eigenvalues with hlamdef
  have hlam : ∀ i, 0 < lam i := hA.eigenvalues_pos
  have hAeq : A = U * diagonal lam * star U := by
    conv_lhs => rw [hA.1.spectral_theorem]
    simp [hUdef, hlamdef]
  set C : Matrix (Fin n) (Fin n) ℝ := diagonal (fun i => Real.sqrt (lam i)) * star U with hCdef
  have hstarU : (star U)ᴴ = U := by simp [Matrix.star_eq_conjTranspose]
  have hCA : Cᴴ * C = A := by
    rw [hAeq, hCdef, conjTranspose_mul, hstarU, diagonal_conjTranspose]
    have hd : star (fun i => Real.sqrt (lam i)) = fun i => Real.sqrt (lam i) := by
      ext i; simp
    rw [hd]
    have hsq : diagonal (fun i => Real.sqrt (lam i)) * diagonal (fun i => Real.sqrt (lam i)) = diagonal lam := by
      rw [diagonal_mul_diagonal]
      congr 1; ext i
      exact Real.mul_self_sqrt (hlam i).le
    calc U * diagonal (fun i => Real.sqrt (lam i)) * (diagonal (fun i => Real.sqrt (lam i)) * star U)
        = U * (diagonal (fun i => Real.sqrt (lam i)) * diagonal (fun i => Real.sqrt (lam i))) * star U := by
          simp only [Matrix.mul_assoc]
      _ = U * diagonal lam * star U := by rw [hsq]
  have hCdet : C.det ≠ 0 := by
    intro h0
    have h1 : A.det = 0 := by rw [← hCA, det_mul, h0, mul_zero]
    exact (hA.det_pos).ne' h1
  have hCinj : Function.Injective C.vecMul :=
    Matrix.vecMul_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det C).mpr (Ne.isUnit hCdet))
  have hM : (C * B * Cᴴ).PosDef := hB.mul_mul_conjTranspose_same hCinj
  have htr : (A * B).trace = (C * B * Cᴴ).trace := by
    rw [← hCA, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have hdet : (C * B * Cᴴ).det = A.det * B.det := by
    have h := congrArg Matrix.det hCA
    rw [det_mul] at h
    rw [det_mul, det_mul, ← h]; ring
  rw [htr, ← hdet, hM.1.trace_eq_sum_eigenvalues, hM.1.det_eq_prod_eigenvalues]
  set μ := hM.1.eigenvalues
  have hμ : ∀ i, 0 < μ i := hM.eigenvalues_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hamgm := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin n)) (fun _ => (1 : ℝ) / n) μ
    (fun _ _ => by positivity) (by simp [Finset.card_univ]; field_simp) (fun i _ => (hμ i).le)
  rw [Real.finsetProd_rpow _ _ (fun i _ => (hμ i).le)] at hamgm
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  calc (n : ℝ) * (∏ i, μ i) ^ ((1 : ℝ) / n) ≤ n * ∑ i, (1 : ℝ) / n * μ i := by gcongr
    _ = ∑ i, μ i := by rw [← Finset.mul_sum, ← mul_assoc, mul_one_div_cancel hn'.ne', one_mul]

/-- **Kitaoka 1993, Lemma 7.1.2 for $2 \le r \le 8$** (p. 192), *proved*: Hermite's constant satisfies
$\mu_r < \sqrt r$. Proof: $\mu_r \le (4/3)^{(r-1)/2}$ (Theorem 2.1.1, `Reduction.hermiteConst_le`) and
$(4/3)^{r-1} < r$ for these $r$. The book's range $2 \le r < 43$ (`Lemma712`) needs Blichfeldt's bound. -/
@[kb "kitaoka1993" "§7.1, Lemma 7.1.2, p. 192 (range 2 ≤ r ≤ 8)"]
theorem lemma712_of_le_eight (r : ℕ) (h2 : 2 ≤ r) (h8 : r ≤ 8) : Reduction.hermiteConst r < Real.sqrt r := by
  refine (Reduction.hermiteConst_le h2).trans_lt ?_
  have hpos : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ (((r : ℝ) - 1) / 2) := by positivity
  rw [Real.lt_sqrt hpos, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have he : ((r : ℝ) - 1) / 2 * ((2 : ℕ) : ℝ) = ((r - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [he, Real.rpow_natCast]
  interval_cases r <;> norm_num

end QuadFormsKB.Kitaoka.EType
