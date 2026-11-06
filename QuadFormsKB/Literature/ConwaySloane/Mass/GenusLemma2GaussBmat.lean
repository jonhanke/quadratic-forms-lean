/-
# Conway–Sloane, LDL IV, §11, Lemma 2 at $p = 2$: the Gauss sum of a block decomposition

For a 2-adic Jordan decomposition `D` (a list of `Cassels.DyBlock`s with exponents $\ge 0$) with matrix
`bmat D` on the index type `BIdx D`:
* `shape_bmat`: $F\mathbb Z_2 = \Delta\mathbb Z_2$ with $\Delta = \operatorname{diag}(2^{e_x})$, $e_x$ the exponent of the
  block of the variable $x$;
* `gaussSum_bmat`: the Gauss sum $\sum_r \mathrm{ch}(2^m r^{\mathsf T}F^{-1}r)$ over the discriminant group is the
  product of the block Gauss sums `blockGauss`;
* `qv_bmat_half`: $2^m y^{\mathsf T}Fy \in 2\mathbb Z_2$ for $y \in \mathbb Z_2^\iota$ if $m \ge 1$ or no block
  $u x^2$ has exponent $0$.

Indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemma2GaussCore

set_option linter.unusedSectionVars false

open Matrix QuadFormsKB QuadFormsKB.Cassels Finset QuadFormsKB.ConwaySloane.TwoAdic

namespace QuadFormsKB.ConwaySloane.Mass.Gauss2

variable (D : List DyBlock)

/-- The exponent of the block of a variable. -/
def bx (x : BIdx D) : ℕ := bexp D x.1

theorem isIntM_map_coe {m : ℕ} (M : Matrix (Fin m) (Fin m) ℤ_[2]) : IsIntM (M.map (algebraMap ℤ_[2] ℚ_[2])) :=
  fun i j => by simp only [Matrix.map_apply]; exact (M i j).2

theorem isIntM_blockDiagonal' (M : (j : Fin D.length) → Matrix (Fin (D.get j).dim) (Fin (D.get j).dim) ℚ_[2])
    (hM : ∀ j, IsIntM (M j)) : IsIntM (blockDiagonal' M) := by
  intro x y
  rw [blockDiagonal'_apply]
  split_ifs with h
  · exact hM _ _ _
  · simp

theorem det_bmat_ne (hD : ∀ b ∈ D, b.Valid) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b) : (bmat D).det ≠ 0 := by
  rw [bmat, det_blockDiagonal']
  refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
  rw [det_mat _ (hD0 _ (List.get_mem _ _))]
  refine mul_ne_zero (pow_ne_zero _ two_ne_zero) ?_
  have h1 : bUnit (D.get j) ≠ 0 := fun h0 => by
    have := bUnit_odd (D.get j) (hD _ (List.get_mem _ _)); rw [h0] at this; exact absurd this (by decide)
  exact_mod_cast h1

theorem mat_det_ne {b : DyBlock} (hv : b.Valid) (he : 0 ≤ blockExp b) : b.mat.det ≠ 0 := by
  rw [det_mat _ he]
  refine mul_ne_zero (pow_ne_zero _ two_ne_zero) ?_
  have h1 : bUnit b ≠ 0 := fun h0 => by
    have := bUnit_odd b hv; rw [h0] at this; exact absurd this (by decide)
  exact_mod_cast h1

/-- **The shape of a block decomposition**: $F\mathbb Z_2 = \operatorname{diag}(2^{e_x})\mathbb Z_2$. -/
theorem shape_bmat (hD : ∀ b ∈ D, b.Valid) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b) : Shape (bmat D) (bx D) := by
  refine ⟨bmat_transpose D, det_bmat_ne D hD hD0, ?_⟩
  set U : Matrix (BIdx D) (BIdx D) ℚ_[2] :=
    blockDiagonal' fun j => (bU (D.get j)).map (algebraMap ℤ_[2] ℚ_[2]) with hU
  set V : Matrix (BIdx D) (BIdx D) ℚ_[2] :=
    blockDiagonal' fun j => ((bU (D.get j))⁻¹).map (algebraMap ℤ_[2] ℚ_[2]) with hV
  have hFU : bmat D = dlt (bx D) * U := by
    ext x y
    rw [dlt, diagonal_mul, hU, bmat, blockDiagonal'_apply, blockDiagonal'_apply]
    split_ifs with h
    · obtain ⟨j, s⟩ := x
      obtain ⟨j', t⟩ := y
      simp only at h
      subst h
      simp only [cast_eq]
      rw [mat_eq_smul _ (hD0 _ (List.get_mem _ _)), Matrix.smul_apply, smul_eq_mul]
      rfl
    · rw [mul_zero]
  have hUV : U * V = 1 := by
    rw [hU, hV, ← blockDiagonal'_mul, ← blockDiagonal'_one]
    congr 1
    funext j
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_det_bU _ (hD _ (List.get_mem _ _)))]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨U, V, isIntM_blockDiagonal' D _ fun j => isIntM_map_coe _,
    isIntM_blockDiagonal' D _ fun j => isIntM_map_coe _, hFU, ?_⟩
  rw [hFU, Matrix.mul_assoc, hUV, Matrix.mul_one]

/-- The inverse of the block matrix is the block matrix of the inverses. -/
theorem bmat_inv (hD : ∀ b ∈ D, b.Valid) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b) :
    (bmat D)⁻¹ = blockDiagonal' fun j => (D.get j).mat⁻¹ := by
  apply inv_eq_right_inv
  rw [bmat, ← blockDiagonal'_mul, ← blockDiagonal'_one]
  congr 1
  funext j
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2
    (mat_det_ne (hD _ (List.get_mem _ _)) (hD0 _ (List.get_mem _ _))))

/-- The quadratic value of a block diagonal matrix is the sum over the blocks. -/
theorem qv_blockDiagonal' (M : (j : Fin D.length) → Matrix (Fin (D.get j).dim) (Fin (D.get j).dim) ℚ_[2])
    (v : BIdx D → ℚ_[2]) : qv (blockDiagonal' M) v = ∑ j, qv (M j) (fun s => v ⟨j, s⟩) := by
  unfold qv
  simp only [dotProduct, mulVec, blockDiagonal'_apply]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => ?_
  congr 1
  rw [Fintype.sum_sigma, Finset.sum_eq_single j]
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp
  · intro j' _ hj
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [dif_neg (Ne.symm hj), zero_mul]
  · intro h; exact absurd (mem_univ j) h

/-- **The Gauss sum of a block decomposition is the product of the block Gauss sums.** -/
theorem gaussSum_bmat (hD : ∀ b ∈ D, b.Valid) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b) (m : ℕ) :
    ∑ r : (x : BIdx D) → Fin (2 ^ bx D x), ch ((2 : ℚ_[2]) ^ m * qv (bmat D)⁻¹ (natVec r)) =
      ∏ j, blockGauss (D.get j) m := by
  rw [bmat_inv D hD hD0]
  simp_rw [qv_blockDiagonal', Finset.mul_sum, ch_sum]
  unfold blockGauss
  rw [Fintype.prod_sum]
  refine Fintype.sum_equiv (Equiv.piCurry fun (j : Fin D.length) (_ : Fin (D.get j).dim) => Fin (2 ^ bexp D j))
    _ _ fun r => ?_
  rfl

/-- The quadratic form of a block, halved, is integral unless the block is $u x^2$ with exponent $0$. -/
theorem qv_mat_int (b : DyBlock) (he : 0 ≤ blockExp b) (y : Fin b.dim → ℚ_[2]) (hy : IsIntV y) :
    ‖qv b.mat y‖ ≤ 1 := by
  rw [mat_eq_smul b he]
  exact hy.dot (IsIntM.mulVec (fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]
    exact norm_mul_le_one' (norm_two_pow_le _) ((bU b) i j).2) hy)

end QuadFormsKB.ConwaySloane.Mass.Gauss2
