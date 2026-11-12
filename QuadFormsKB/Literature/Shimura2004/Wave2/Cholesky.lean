/-
# Shimura 2004, Lemma 16.5: the Cholesky and polar-type decompositions

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Lemma 16.5, printed p. 156:
"Let $Q_n$ be the subgroup of $GL_n(\mathbb R)$ consisting of all upper triangular matrices whose diagonal entries
are all positive, and let $O_n = O(1_n)$. Then the map $a \mapsto {}^t a\, a$ gives a bijection of $Q_n$ onto the set
of positive definite real symmetric $n \times n$ matrices. Moreover, the map $(p, u) \mapsto pu$ of
$Q_n \times O_n$ to $GL_n(\mathbb R)$ is a bijection."

**Dictionary.**
* $Q_n$ = `posUpperTriangular n`, the set of real $n \times n$ matrices $a$ (indices `Fin n`, 0-based) with
  $a_{ij} = 0$ for $j < i$ and $a_{ii} > 0$ for all $i$ (such matrices have positive determinant, so lie in
  $GL_n(\mathbb R)$; the set is closed under products and inverses, `posUpperTriangular_mul_mem`,
  `posUpperTriangular_inv_mem`).
* ${}^t a$ = `aᵀ` (`Matrix.transpose`); positive definite = Mathlib's `Matrix.PosDef` (for real matrices this
  includes symmetry).
* $O_n$ = `Matrix.orthogonalGroup (Fin n) ℝ` (matrices with ${}^t u\, u = 1$).
* $GL_n(\mathbb R)$ = real matrices with unit determinant, `{g | IsUnit g.det}`.

**Proves** (all unconditional; standard axioms only)
* `lemma_16_5_cholesky`: $a \mapsto {}^t a\, a$ is a bijection from $Q_n$ onto the positive definite
  matrices (existence from Mathlib's LDL decomposition, uniqueness by a triangularity argument).
* `lemma_16_5_polar`: $(p, u) \mapsto pu$ is a bijection from $Q_n \times O_n$ onto
  $GL_n(\mathbb R)$ (existence: apply the first part to ${}^t(g^{-1})\, g^{-1} = {}^t q\, q$ and put
  $p = q^{-1}$, $u = q g$).
-/
import Mathlib.Analysis.Matrix.LDL
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.Order.Star.Real
import QuadFormsKB.Citation

namespace QuadFormsKB.Shimura2004

open Matrix

variable {n : ℕ}

/-- Shimura's $Q_n$ (Lemma 16.5, p. 156): the real $n \times n$ upper triangular matrices with all diagonal entries
positive, i.e. $a_{ij} = 0$ whenever $j < i$ and $a_{ii} > 0$ for every $i$ (0-based indices). -/
def posUpperTriangular (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {a | (∀ i j : Fin n, j < i → a i j = 0) ∧ ∀ i, 0 < a i i}

namespace Cholesky

private lemma upper {a : Matrix (Fin n) (Fin n) ℝ} (ha : a ∈ posUpperTriangular n) :
    a.IsUpperTriangular := fun i j h => ha.1 i j h

lemma det_pos {a : Matrix (Fin n) (Fin n) ℝ} (ha : a ∈ posUpperTriangular n) : 0 < a.det := by
  rw [det_of_isUpperTriangular (upper ha)]
  exact Finset.prod_pos fun i _ => ha.2 i

lemma isUnit_det {a : Matrix (Fin n) (Fin n) ℝ} (ha : a ∈ posUpperTriangular n) : IsUnit a.det :=
  isUnit_iff_ne_zero.2 (det_pos ha).ne'

lemma mul_mem {a b : Matrix (Fin n) (Fin n) ℝ} (ha : a ∈ posUpperTriangular n)
    (hb : b ∈ posUpperTriangular n) : a * b ∈ posUpperTriangular n := by
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k < i
    · rw [ha.1 i k hk, zero_mul]
    · rw [hb.1 k j (lt_of_lt_of_le hji (not_lt.1 hk)), mul_zero]
  · rw [mul_apply, Finset.sum_eq_single i]
    · exact mul_pos (ha.2 i) (hb.2 i)
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with h | h
      · rw [ha.1 i k h, zero_mul]
      · rw [hb.1 k i h, mul_zero]
    · simp

lemma inv_mem {a : Matrix (Fin n) (Fin n) ℝ} (ha : a ∈ posUpperTriangular n) :
    a⁻¹ ∈ posUpperTriangular n := by
  have := invertibleOfIsUnitDet a (isUnit_det ha)
  have hup : a⁻¹.IsUpperTriangular := blockTriangular_inv_of_blockTriangular (upper ha)
  refine ⟨fun i j h => hup h, fun i => ?_⟩
  have h1 : (a⁻¹ * a) i i = 1 := by rw [nonsing_inv_mul _ (isUnit_det ha)]; simp
  rw [mul_apply, Finset.sum_eq_single i] at h1
  · by_contra hn
    push Not at hn
    have := mul_nonpos_of_nonpos_of_nonneg hn (ha.2 i).le
    linarith
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with h | h
    · rw [hup (show id k < id i from h), zero_mul]
    · rw [ha.1 k i h, mul_zero]
  · simp

lemma eq_one_of_transpose_mul_self {c : Matrix (Fin n) (Fin n) ℝ} (hc : c ∈ posUpperTriangular n)
    (h : cᵀ * c = 1) : c = 1 := by
  have hinv : c⁻¹ = cᵀ := inv_eq_left_inv h
  have hlow : ∀ i j : Fin n, j < i → cᵀ i j = 0 := by
    rw [← hinv]; exact (inv_mem hc).1
  have off : ∀ i j : Fin n, i ≠ j → c i j = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h' | h'
    · have := hlow j i h'
      simpa using this
    · exact hc.1 i j h'
  have hd : ∀ i, c i i = 1 := fun i => by
    have h1 : (cᵀ * c) i i = 1 := by rw [h]; simp
    rw [mul_apply, Finset.sum_eq_single i] at h1
    · simp only [transpose_apply] at h1
      have h2 : (c i i - 1) * (c i i + 1) = 0 := by linear_combination h1
      rcases mul_eq_zero.1 h2 with h3 | h3
      · linarith
      · linarith [hc.2 i]
    · intro k _ hki
      rw [transpose_apply, off k i hki, zero_mul]
    · simp
  ext i j
  by_cases hij : i = j
  · subst hij; simp [hd]
  · simp [off i j hij, one_apply_ne hij]

lemma gram_injOn {a b : Matrix (Fin n) (Fin n) ℝ} (ha : a ∈ posUpperTriangular n)
    (hb : b ∈ posUpperTriangular n) (h : aᵀ * a = bᵀ * b) : a = b := by
  have hu := isUnit_det hb
  have hc : a * b⁻¹ ∈ posUpperTriangular n := mul_mem ha (inv_mem hb)
  have e : (b⁻¹)ᵀ * bᵀ = 1 := by
    rw [← transpose_mul, mul_nonsing_inv _ hu, transpose_one]
  have h1 : (a * b⁻¹)ᵀ * (a * b⁻¹) = 1 := by
    calc (a * b⁻¹)ᵀ * (a * b⁻¹) = (b⁻¹)ᵀ * (aᵀ * a) * b⁻¹ := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = (b⁻¹)ᵀ * (bᵀ * b) * b⁻¹ := by rw [h]
      _ = ((b⁻¹)ᵀ * bᵀ) * (b * b⁻¹) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e, mul_nonsing_inv _ hu, Matrix.mul_one]
  have h2 := eq_one_of_transpose_mul_self hc h1
  calc a = a * b⁻¹ * b := by rw [Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]
    _ = b := by rw [h2, Matrix.one_mul]

lemma posDef_transpose_mul_self {a : Matrix (Fin n) (Fin n) ℝ} (h : IsUnit a.det) :
    (aᵀ * a).PosDef := by
  have := PosDef.conjTranspose_mul_self a
    (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det a).2 h))
  simpa [conjTranspose_eq_transpose_of_trivial] using this

lemma exists_cholesky {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) :
    ∃ a ∈ posUpperTriangular n, aᵀ * a = S := by
  classical
  have hLDL : LDL.lower hS * LDL.diag hS * (LDL.lower hS)ᴴ = S := LDL.lower_conj_diag hS
  have hLtri : (LDL.lower hS).IsLowerTriangular := LDL.isLowerTriangular_lower hS
  have hLL : LDL.lower hS * LDL.lowerInv hS = 1 :=
    nonsing_inv_mul _ (isUnit_det_of_invertible _)
  have hD : (LDL.diag hS).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    refine hS.mul_mul_conjTranspose_same ?_
    exact vecMul_injective_iff_isUnit.2 (isUnit_of_invertible _)
  have hpos : ∀ i, 0 < LDL.diagEntries hS i := fun i => by
    have := hD.diag_pos (i := i)
    simpa [LDL.diag] using this
  have hdD : LDL.diag hS = diagonal (LDL.diagEntries hS) := rfl
  generalize LDL.lower hS = L at hLDL hLtri hLL
  have hdet : L.det ≠ 0 := by
    have := congrArg det hLL
    rw [det_mul, det_one] at this
    exact left_ne_zero_of_mul_eq_one this
  have hLii : ∀ i, L i i ≠ 0 := by
    rw [det_of_isLowerTriangular L hLtri] at hdet
    intro i h0
    exact hdet (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  let s : Fin n → ℝ := fun i => if L i i < 0 then -1 else 1
  let d : Fin n → ℝ := fun i => Real.sqrt (LDL.diagEntries hS i) * s i
  have hdd : ∀ i, d i * d i = LDL.diagEntries hS i := fun i => by
    have := Real.mul_self_sqrt (hpos i).le
    simp only [d, s]
    split_ifs <;> linear_combination this
  refine ⟨diagonal d * Lᵀ, ⟨fun i j hji => ?_, fun i => ?_⟩, ?_⟩
  · rw [diagonal_mul, transpose_apply, hLtri hji, mul_zero]
  · rw [diagonal_mul, transpose_apply]
    have hs := Real.sqrt_pos.2 (hpos i)
    by_cases hneg : L i i < 0
    · have := mul_pos hs (neg_pos.2 hneg)
      simp only [d, s, hneg, ite_true]
      linarith
    · have hp : 0 < L i i := lt_of_le_of_ne (not_lt.1 hneg) (hLii i).symm
      have := mul_pos hs hp
      simp only [d, s, hneg, ite_false]
      linarith
  · rw [transpose_mul, transpose_transpose, diagonal_transpose]
    calc L * diagonal d * (diagonal d * Lᵀ) = L * (diagonal d * diagonal d) * Lᵀ := by
          simp only [Matrix.mul_assoc]
      _ = L * LDL.diag hS * Lᴴ := by
          rw [diagonal_mul_diagonal, conjTranspose_eq_transpose_of_trivial, hdD]
          congr 3
          funext i
          exact hdd i
      _ = S := hLDL

lemma eq_of_mul_transpose {p p' : Matrix (Fin n) (Fin n) ℝ} (hp : p ∈ posUpperTriangular n)
    (hp' : p' ∈ posUpperTriangular n) (h : p * pᵀ = p' * p'ᵀ) : p = p' := by
  have hu' := isUnit_det hp'
  have hc : p'⁻¹ * p ∈ posUpperTriangular n := mul_mem (inv_mem hp') hp
  have h1 : (p'⁻¹ * p) * (p'⁻¹ * p)ᵀ = 1 := by
    calc (p'⁻¹ * p) * (p'⁻¹ * p)ᵀ = p'⁻¹ * (p * pᵀ) * (p'⁻¹)ᵀ := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = p'⁻¹ * (p' * p'ᵀ) * (p'⁻¹)ᵀ := by rw [h]
      _ = (p'⁻¹ * p') * (p'⁻¹ * p')ᵀ := by simp only [transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [nonsing_inv_mul _ hu', transpose_one, Matrix.mul_one]
  have h2 := eq_one_of_transpose_mul_self hc (mul_eq_one_comm.1 h1)
  calc p = p' * (p'⁻¹ * p) := by rw [← Matrix.mul_assoc, mul_nonsing_inv _ hu', Matrix.one_mul]
    _ = p' := by rw [h2, Matrix.mul_one]

lemma mul_transpose_of_orthogonal (p u : Matrix (Fin n) (Fin n) ℝ) (hu : u * uᵀ = 1) :
    (p * u) * (p * u)ᵀ = p * pᵀ := by
  rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc u, hu, Matrix.one_mul]

end Cholesky

open Cholesky

/-- **Shimura 2004, Lemma 16.5, first part (p. 156).** The map $a \mapsto {}^t a\, a$ is a bijection from $Q_n$
(`posUpperTriangular n`: upper triangular real matrices with positive diagonal) onto the set of positive definite
real symmetric $n \times n$ matrices (`Matrix.PosDef`).  This is the Cholesky decomposition. -/
@[kb "shimura2004" "Lemma 16.5, p. 156 (a ↦ ᵗa a : Q_n → positive definite matrices is a bijection)"]
theorem lemma_16_5_cholesky :
    Set.BijOn (fun a : Matrix (Fin n) (Fin n) ℝ => aᵀ * a) (posUpperTriangular n)
      {S | S.PosDef} := by
  refine ⟨fun a ha => posDef_transpose_mul_self (isUnit_det ha),
    fun a ha b hb h => gram_injOn ha hb h, fun S hS => ?_⟩
  obtain ⟨a, ha, h⟩ := exists_cholesky hS
  exact ⟨a, ha, h⟩

/-- **Shimura 2004, Lemma 16.5, second part (p. 156).** The map $(p, u) \mapsto pu$ is a bijection from
$Q_n \times O_n$ (`posUpperTriangular n` times `Matrix.orthogonalGroup (Fin n) ℝ`) onto $GL_n(\mathbb R)$, the
real $n \times n$ matrices with unit determinant. -/
@[kb "shimura2004" "Lemma 16.5, p. 156 ((p, u) ↦ pu : Q_n × O_n → GL_n(ℝ) is a bijection)"]
theorem lemma_16_5_polar :
    Set.BijOn (fun x : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ => x.1 * x.2)
      (posUpperTriangular n ×ˢ {u | u ∈ Matrix.orthogonalGroup (Fin n) ℝ})
      {g | IsUnit g.det} := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨p, u⟩ ⟨hp, hu⟩
    have hu' := (mem_orthogonalGroup_iff' (Fin n) ℝ).1 hu
    show IsUnit (p * u).det
    rw [det_mul]
    exact (isUnit_det hp).mul (isUnit_det_of_left_inverse hu')
  · rintro ⟨p, u⟩ ⟨hp, hu⟩ ⟨p', u'⟩ ⟨hp', hu'⟩ h
    have h : p * u = p' * u' := h
    have hu2 := (mem_orthogonalGroup_iff (Fin n) ℝ).1 hu
    have hu2' := (mem_orthogonalGroup_iff (Fin n) ℝ).1 hu'
    have hpp : p * pᵀ = p' * p'ᵀ := by
      rw [← mul_transpose_of_orthogonal p u hu2, ← mul_transpose_of_orthogonal p' u' hu2', h]
    have hpe := eq_of_mul_transpose hp hp' hpp
    subst hpe
    have hue : u = u' := by
      calc u = p⁻¹ * (p * u) := by
            rw [← Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_det hp), Matrix.one_mul]
        _ = u' := by rw [h, ← Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_det hp), Matrix.one_mul]
    rw [hue]
  · intro g hg
    have hg : IsUnit g.det := hg
    have hh : IsUnit g⁻¹.det := isUnit_nonsing_inv_det_iff.2 hg
    obtain ⟨q, hq, hqS⟩ := exists_cholesky (posDef_transpose_mul_self hh)
    refine ⟨(q⁻¹, q * g), ⟨inv_mem hq, ?_⟩, ?_⟩
    · show q * g ∈ Matrix.orthogonalGroup (Fin n) ℝ
      rw [mem_orthogonalGroup_iff' (Fin n) ℝ]
      calc (q * g)ᵀ * (q * g) = gᵀ * (qᵀ * q) * g := by
            simp only [transpose_mul, Matrix.mul_assoc]
        _ = gᵀ * ((g⁻¹)ᵀ * g⁻¹) * g := by rw [hqS]
        _ = (g⁻¹ * g)ᵀ * (g⁻¹ * g) := by simp only [transpose_mul, Matrix.mul_assoc]
        _ = 1 := by rw [nonsing_inv_mul _ hg]; simp
    · show q⁻¹ * (q * g) = g
      rw [← Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_det hq), Matrix.one_mul]

end QuadFormsKB.Shimura2004
