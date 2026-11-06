/-
# Conway–Sloane, Ch. 15, Theorem 10: the blocks of a 2-adic Jordan decomposition

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §7.3–7.5, pp. 380–381
(`conwaysloane1999`). Matrix facts about a list $D$ of Cassels blocks (`Cassels.DyBlock`: $2^eux^2$, $2^e\cdot 2xy$,
$2^e(2x^2+2xy+2y^2)$), used in `TwoAdicClassificationLattice.lean`:
* the block diagonal matrix `bmat D` on the index type $\Sigma_j \{0, \dots, \dim b_j - 1\}$ and its identification
  with `Cassels.dyMat D` (`dyMat_apply`);
* the determinant of a block diagonal matrix (`det_blockDiagonal'`);
* for each block: its matrix is $2^e$ times a unimodular matrix (`mat_eq_smul`), its determinant $2^{e\dim}\cdot u_b$
  with $u_b \in \{u, -1, 3\}$ (`det_mat`), and an explicit diagonalization over $\mathbb Q_2$ with integer weights
  $\langle 2^eu\rangle$, $\langle 2^{e+1}, -2^{e+1}\rangle$, $\langle 2^{e+1}, 3\cdot 2^{e+1}\rangle$ (`bP_mul`);
* the link with the 2-adic symbol (`blockSymbol`): the product of the units $u_b$ of the blocks of exponent $k$ is
  `cu` of the constituent of scale $2^k$, and the oddity of the weights is `oddW` (`prod_unit_fiber`,
  `sum_oddB_fiber`).
-/
import QuadFormsKB.Literature.ConwaySloane.TwoAdicClassificationCore
import QuadFormsKB.Literature.ConwaySloane.LocalExistence
import QuadFormsKB.Literature.ConwaySloane.Rational

namespace QuadFormsKB.ConwaySloane.TwoAdic

open Cassels Matrix Finset

/-! ### The determinant of a block diagonal matrix with blocks of varying size -/

theorem det_blockDiagonal' {R : Type*} [CommRing R] {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    {d : o → Type*} [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)] (A : ∀ i, Matrix (d i) (d i) R) :
    (blockDiagonal' A).det = ∏ i, (A i).det := by
  have hB : (blockDiagonal' A).BlockTriangular Sigma.fst := fun x y h =>
    blockDiagonal'_apply_ne A x.2 y.2 (ne_of_gt h)
  rw [hB.det]
  have hblk : ∀ k, ((blockDiagonal' A).toSquareBlock Sigma.fst k).det = (A k).det := by
    intro k
    have : (blockDiagonal' A).toSquareBlock Sigma.fst k = (A k).submatrix (Equiv.sigmaSubtype k)
        (Equiv.sigmaSubtype k) := by
      ext ⟨⟨k₁, x⟩, h₁⟩ ⟨⟨k₂, y⟩, h₂⟩
      simp only at h₁ h₂
      subst h₁; subst h₂
      simp [toSquareBlock_def, Equiv.sigmaSubtype]
    rw [this, det_submatrix_equiv_self]
  simp_rw [hblk]
  refine Finset.prod_subset (Finset.subset_univ _) fun k _ hk => ?_
  have : IsEmpty (d k) := ⟨fun x => hk (Finset.mem_image.2 ⟨⟨k, x⟩, Finset.mem_univ _, rfl⟩)⟩
  exact det_isEmpty

/-! ### The block index type and the block diagonal matrix -/

/-- The variables of a block decomposition: pairs (block $j$, variable of the block). -/
abbrev BIdx (D : List DyBlock) : Type := Σ j : Fin D.length, Fin (D.get j).dim

/-- The matrix of the orthogonal sum of the blocks of `D`, on the index type `BIdx D`. -/
noncomputable def bmat (D : List DyBlock) : Matrix (BIdx D) (BIdx D) ℚ_[2] :=
  blockDiagonal' fun j => (D.get j).mat

/-- Splitting off the first block. -/
def consEquiv (b : DyBlock) (D : List DyBlock) : BIdx (b :: D) ≃ Fin b.dim ⊕ BIdx D where
  toFun x := Fin.cases (motive := fun j : Fin (D.length + 1) => Fin ((b :: D).get j).dim → Fin b.dim ⊕ BIdx D)
    (fun y => Sum.inl y) (fun j y => Sum.inr ⟨j, y⟩) x.1 x.2
  invFun := Sum.elim (fun y => ⟨0, y⟩) (fun y => ⟨y.1.succ, y.2⟩)
  left_inv := by
    rintro ⟨j, y⟩
    induction j using Fin.cases <;> rfl
  right_inv := by rintro (y | ⟨j, y⟩) <;> rfl

/-- The identification of the variables of `dyMat D` (in order) with `BIdx D`. -/
def bEquiv : (D : List DyBlock) → Fin (dyDim D) ≃ BIdx D
  | [] => @Equiv.equivOfIsEmpty _ _ ⟨fun i => Fin.elim0 i⟩ ⟨fun x => Fin.elim0 x.1⟩
  | b :: D => finSumFinEquiv.symm.trans ((Equiv.sumCongr (Equiv.refl _) (bEquiv D)).trans (consEquiv b D).symm)

theorem bEquiv_inl (b : DyBlock) (D : List DyBlock) (s : Fin b.dim) :
    bEquiv (b :: D) (finSumFinEquiv (Sum.inl s)) = ⟨0, s⟩ := by
  change (consEquiv b D).symm (Equiv.sumCongr (Equiv.refl _) (bEquiv D)
    (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl s)))) = _
  rw [Equiv.symm_apply_apply]; rfl

theorem bEquiv_inr (b : DyBlock) (D : List DyBlock) (t : Fin (dyDim D)) :
    bEquiv (b :: D) (finSumFinEquiv (Sum.inr t)) = ⟨(bEquiv D t).1.succ, (bEquiv D t).2⟩ := by
  change (consEquiv b D).symm (Equiv.sumCongr (Equiv.refl _) (bEquiv D)
    (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr t)))) = _
  rw [Equiv.symm_apply_apply]; rfl

theorem dyMat_cons_apply (b : DyBlock) (D : List DyBlock) (x y : Fin b.dim ⊕ Fin (dyDim D)) :
    dyMat (b :: D) (finSumFinEquiv x) (finSumFinEquiv y) = fromBlocks b.mat 0 0 (dyMat D) x y := by
  simp [dyMat, orthSumMat]

theorem dyMat_apply : ∀ (D : List DyBlock) (i j : Fin (dyDim D)), dyMat D i j = bmat D (bEquiv D i) (bEquiv D j)
  | [], i, _ => Fin.elim0 i
  | b :: D, i, j => by
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨t, rfl⟩ := finSumFinEquiv.surjective j
    have ih := dyMat_apply D
    rw [dyMat_cons_apply]
    rcases s with s | s <;> rcases t with t | t
    · rw [bEquiv_inl, bEquiv_inl, fromBlocks_apply₁₁]
      exact (blockDiagonal'_apply_eq (fun j => ((b :: D).get j).mat) (0 : Fin (D.length + 1)) s t).symm
    · rw [bEquiv_inl, bEquiv_inr, fromBlocks_apply₁₂, Matrix.zero_apply]
      exact (blockDiagonal'_apply_ne (fun j => ((b :: D).get j).mat) (k := 0) s _
        (Fin.succ_ne_zero _).symm).symm
    · rw [bEquiv_inr, bEquiv_inl, fromBlocks_apply₂₁, Matrix.zero_apply]
      exact (blockDiagonal'_apply_ne (fun j => ((b :: D).get j).mat) (k' := 0) _ t
        (Fin.succ_ne_zero _)).symm
    · rw [bEquiv_inr, bEquiv_inr, fromBlocks_apply₂₂, ih]
      obtain ⟨j₁, y₁⟩ := bEquiv D s
      obtain ⟨j₂, y₂⟩ := bEquiv D t
      by_cases h : j₁ = j₂
      · subst h; rw [bmat, bmat, blockDiagonal'_apply', blockDiagonal'_apply']; simp
      · rw [bmat, bmat, blockDiagonal'_apply', blockDiagonal'_apply', dite_eq_right h,
          dite_eq_right (fun h' => h (Fin.succ_injective _ h'))]

/-! ### Single blocks -/

/-- The unit part of the determinant of a block: $u$ for $2^eux^2$, $-1$ for $2^e\cdot 2xy$, $3$ for
$2^e(2x^2+2xy+2y^2)$. -/
def bUnit : DyBlock → ℤ
  | .sq _ u => u
  | .hyp _ => -1
  | .ell _ => 3

/-- The integer weights of a diagonalization of a block over $\mathbb Q_2$ (for exponent $e \ge 0$):
$\langle 2^eu\rangle$, $\langle 2^{e+1}, -2^{e+1}\rangle$, $\langle 2^{e+1}, 3\cdot 2^{e+1}\rangle$. -/
def bW : (b : DyBlock) → Fin b.dim → ℤ
  | .sq e u => ![2 ^ e.toNat * u]
  | .hyp e => ![2 ^ (e.toNat + 1) * 1, 2 ^ (e.toNat + 1) * (-1)]
  | .ell e => ![2 ^ (e.toNat + 1) * 1, 2 ^ (e.toNat + 1) * 3]

/-- The change of variables diagonalizing a block. -/
noncomputable def bP : (b : DyBlock) → Matrix (Fin b.dim) (Fin b.dim) ℚ_[2]
  | .sq _ _ => 1
  | .hyp _ => !![1, 1; 1, -1]
  | .ell _ => !![1, 0; 1, -2]

/-- The oddity of the weights of a block. -/
def bOdd (b : DyBlock) : ZMod 8 := ∑ r, oddityEntry (bW b r)

theorem zpow_eq_pow_toNat {e : ℤ} (he : 0 ≤ e) : (2 : ℚ_[2]) ^ e = (2 : ℚ_[2]) ^ e.toNat := by
  rw [← zpow_natCast, Int.toNat_of_nonneg he]

theorem bP_mul (b : DyBlock) (he : 0 ≤ blockExp b) :
    bP b * b.mat * (bP b)ᵀ = diagonal fun r => ((bW b r : ℤ) : ℚ_[2]) := by
  cases b with
  | sq e u =>
    simp only [blockExp] at he
    show (1 : Matrix (Fin 1) (Fin 1) ℚ_[2]) * !![(2 : ℚ_[2]) ^ e * u] * (1 : Matrix (Fin 1) (Fin 1) ℚ_[2])ᵀ =
      diagonal fun r => ((![2 ^ e.toNat * u] r : ℤ) : ℚ_[2])
    rw [zpow_eq_pow_toNat he]
    ext i j; fin_cases i; fin_cases j; simp
  | hyp e =>
    simp only [blockExp] at he
    show (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℚ_[2]) * ((2 : ℚ_[2]) ^ e • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2])) *
      (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℚ_[2])ᵀ =
      diagonal fun r => ((![2 ^ (e.toNat + 1) * 1, 2 ^ (e.toNat + 1) * (-1)] r : ℤ) : ℚ_[2])
    rw [zpow_eq_pow_toNat he]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ] <;> ring
  | ell e =>
    simp only [blockExp] at he
    show (!![1, 0; 1, -2] : Matrix (Fin 2) (Fin 2) ℚ_[2]) * ((2 : ℚ_[2]) ^ e • (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ_[2])) *
      (!![1, 0; 1, -2] : Matrix (Fin 2) (Fin 2) ℚ_[2])ᵀ =
      diagonal fun r => ((![2 ^ (e.toNat + 1) * 1, 2 ^ (e.toNat + 1) * 3] r : ℤ) : ℚ_[2])
    rw [zpow_eq_pow_toNat he]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ] <;> ring

theorem bP_det_ne (b : DyBlock) : (bP b).det ≠ 0 := by
  cases b with
  | sq e u => show (1 : Matrix (Fin 1) (Fin 1) ℚ_[2]).det ≠ 0; simp
  | hyp e =>
    show (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℚ_[2]).det ≠ 0
    rw [Matrix.det_fin_two_of]; norm_num
  | ell e =>
    show (!![1, 0; 1, -2] : Matrix (Fin 2) (Fin 2) ℚ_[2]).det ≠ 0
    rw [Matrix.det_fin_two_of]; norm_num

theorem det_mat (b : DyBlock) (he : 0 ≤ blockExp b) :
    b.mat.det = (2 : ℚ_[2]) ^ ((blockExp b).toNat * b.dim) * (bUnit b : ℚ_[2]) := by
  cases b with
  | sq e u =>
    simp only [blockExp] at he
    show (!![(2 : ℚ_[2]) ^ e * u] : Matrix (Fin 1) (Fin 1) ℚ_[2]).det = (2 : ℚ_[2]) ^ (e.toNat * 1) * (u : ℚ_[2])
    rw [Matrix.det_fin_one_of, zpow_eq_pow_toNat he, mul_one]
  | hyp e =>
    simp only [blockExp] at he
    show ((2 : ℚ_[2]) ^ e • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2])).det =
      (2 : ℚ_[2]) ^ (e.toNat * 2) * ((-1 : ℤ) : ℚ_[2])
    rw [Matrix.det_smul, Matrix.det_fin_two_of, zpow_eq_pow_toNat he]
    simp [pow_mul]
  | ell e =>
    simp only [blockExp] at he
    show ((2 : ℚ_[2]) ^ e • (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ_[2])).det =
      (2 : ℚ_[2]) ^ (e.toNat * 2) * ((3 : ℤ) : ℚ_[2])
    rw [Matrix.det_smul, Matrix.det_fin_two_of, zpow_eq_pow_toNat he]
    simp [pow_mul]; norm_num

/-- The unimodular matrix $U_b$ with $b = 2^e U_b$. -/
noncomputable def bU : (b : DyBlock) → Matrix (Fin b.dim) (Fin b.dim) ℤ_[2]
  | .sq _ u => !![(u : ℤ_[2])]
  | .hyp _ => !![0, 1; 1, 0]
  | .ell _ => !![2, 1; 1, 2]

theorem mat_eq_smul (b : DyBlock) (he : 0 ≤ blockExp b) :
    b.mat = (2 : ℚ_[2]) ^ (blockExp b).toNat • (bU b).map (algebraMap ℤ_[2] ℚ_[2]) := by
  cases b with
  | sq e u =>
    simp only [blockExp] at he ⊢
    show (!![(2 : ℚ_[2]) ^ e * u] : Matrix (Fin 1) (Fin 1) ℚ_[2]) =
      (2 : ℚ_[2]) ^ e.toNat • (!![(u : ℤ_[2])] : Matrix (Fin 1) (Fin 1) ℤ_[2]).map (algebraMap ℤ_[2] ℚ_[2])
    ext i j; fin_cases i; fin_cases j; simp [zpow_eq_pow_toNat he]
  | hyp e =>
    simp only [blockExp] at he ⊢
    show (2 : ℚ_[2]) ^ e • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2]) =
      (2 : ℚ_[2]) ^ e.toNat • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ_[2]).map (algebraMap ℤ_[2] ℚ_[2])
    ext i j; fin_cases i <;> fin_cases j <;> simp [zpow_eq_pow_toNat he]
  | ell e =>
    simp only [blockExp] at he ⊢
    show (2 : ℚ_[2]) ^ e • (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ_[2]) =
      (2 : ℚ_[2]) ^ e.toNat • (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ_[2]).map (algebraMap ℤ_[2] ℚ_[2])
    ext i j; fin_cases i <;> fin_cases j <;> simp [zpow_eq_pow_toNat he] <;> norm_cast

theorem isUnit_det_bU (b : DyBlock) (hv : b.Valid) : IsUnit (bU b).det := by
  cases b with
  | sq e u =>
    show IsUnit (!![(u : ℤ_[2])] : Matrix (Fin 1) (Fin 1) ℤ_[2]).det
    rw [Matrix.det_fin_one_of]
    apply dyadic_isUnit_int_cast_of_odd
    simp only [DyBlock.Valid] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> decide
  | hyp e =>
    show IsUnit (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ_[2]).det
    rw [Matrix.det_fin_two_of]; simp
  | ell e =>
    show IsUnit (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ_[2]).det
    rw [Matrix.det_fin_two_of]; norm_num
    exact dyadic_isUnit_three

/-- A block $2^eux^2$ has the entry $2^eu$. -/
theorem mat_sq (e u : ℤ) (he : 0 ≤ e) (r s : Fin (DyBlock.sq e u).dim) :
    (DyBlock.sq e u).mat r s = (2 : ℚ_[2]) ^ e.toNat * (u : ℚ_[2]) := by
  revert r s
  show ∀ r s : Fin 1, (!![(2 : ℚ_[2]) ^ e * u] : Matrix (Fin 1) (Fin 1) ℚ_[2]) r s = _
  intro r s
  fin_cases r; fin_cases s
  simp [zpow_eq_pow_toNat he]

/-- The diagonal entries of a binary block are in $2^{e+1}\mathbb Z_2$. -/
theorem mat_diag_binary (b : DyBlock) (he : 0 ≤ blockExp b) (hb : ¬ IsSqBlock b) (r : Fin b.dim) :
    ∃ z : ℤ_[2], b.mat r r = (2 : ℚ_[2]) ^ ((blockExp b).toNat + 1) * (z : ℚ_[2]) := by
  cases b with
  | sq e u => exact absurd trivial hb
  | hyp e =>
    refine ⟨0, ?_⟩
    revert r
    show ∀ r : Fin 2, ((2 : ℚ_[2]) ^ e • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2])) r r = _
    intro r
    fin_cases r <;> simp
  | ell e =>
    simp only [blockExp] at he ⊢
    refine ⟨1, ?_⟩
    revert r
    show ∀ r : Fin 2, ((2 : ℚ_[2]) ^ e • (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ_[2])) r r = _
    intro r
    fin_cases r <;> simp [zpow_eq_pow_toNat he, pow_succ]

theorem bUnit_odd (b : DyBlock) (hv : b.Valid) : Odd (bUnit b) := by
  cases b with
  | sq e u =>
    simp only [DyBlock.Valid] at hv
    simp only [bUnit]
    rcases hv with rfl | rfl | rfl | rfl <;> decide
  | hyp e => exact ⟨-1, by simp [bUnit]⟩
  | ell e => exact ⟨1, by simp [bUnit]⟩

theorem bUnit_cast (b : DyBlock) (hv : b.Valid) :
    ((bUnit b : ℤ) : ZMod 8) = unitOf (blockOddity b - b.dim) (signInd (blockSign b)) := by
  cases b with
  | sq e u =>
    simp only [DyBlock.Valid] at hv
    simp only [bUnit, blockOddity, blockSign, DyBlock.dim]
    rcases hv with rfl | rfl | rfl | rfl <;> decide
  | hyp e => simp only [bUnit, blockOddity, blockSign, DyBlock.dim]; decide
  | ell e => simp only [bUnit, blockOddity, blockSign, DyBlock.dim]; decide

theorem blockOddity_sub_dim (b : DyBlock) (hv : b.Valid) : ∃ c : ZMod 8, blockOddity b - b.dim = 2 * c := by
  cases b with
  | sq e u =>
    simp only [DyBlock.Valid] at hv
    simp only [blockOddity, DyBlock.dim]
    rcases hv with rfl | rfl | rfl | rfl
    · exact ⟨0, by decide⟩
    · exact ⟨1, by decide⟩
    · exact ⟨2, by decide⟩
    · exact ⟨3, by decide⟩
  | hyp e => exact ⟨-1, by simp only [blockOddity, DyBlock.dim]; decide⟩
  | ell e => exact ⟨-1, by simp only [blockOddity, DyBlock.dim]; decide⟩

theorem oddityEntry_two_pow (e : ℕ) : oddityEntry (2 ^ e * 1) = 1 := by
  rw [Rational.oddityEntry_two_pow_mul e 1 (by decide)]
  have h : ¬ (Odd e ∧ (((1 : ℤ) : ZMod 8) = 3 ∨ ((1 : ℤ) : ZMod 8) = 5)) := fun h => absurd h.2 (by decide)
  rw [if_neg h]; simp

theorem oddityEntry_two_pow_neg (e : ℕ) : oddityEntry (2 ^ e * (-1)) = -1 := by
  rw [Rational.oddityEntry_two_pow_mul e (-1) (by decide)]
  have h : ¬ (Odd e ∧ (((-1 : ℤ) : ZMod 8) = 3 ∨ ((-1 : ℤ) : ZMod 8) = 5)) := fun h => absurd h.2 (by decide)
  rw [if_neg h]; simp

theorem bOdd_eq (b : DyBlock) (hv : b.Valid) :
    bOdd b = blockOddity b + 4 * ((blockExp b).toNat : ZMod 8) * signInd (blockSign b) := by
  rw [four_mul_natCast_mod_two]
  cases b with
  | sq e u =>
    simp only [DyBlock.Valid] at hv
    show (∑ r : Fin 1, oddityEntry (![2 ^ e.toNat * u] r)) = (u : ZMod 8) +
      4 * (if e.toNat % 2 = 1 then 1 else 0) * signInd (jacobiTwo u)
    rw [Fin.sum_univ_one, Matrix.cons_val_zero,
      Rational.oddityEntry_two_pow_mul _ _ (by rcases hv with rfl | rfl | rfl | rfl <;> decide)]
    have ho : Odd e.toNat ↔ e.toNat % 2 = 1 := Nat.odd_iff
    simp only [ho]
    rcases Nat.mod_two_eq_zero_or_one e.toNat with h | h <;> simp only [h] <;>
      rcases hv with rfl | rfl | rfl | rfl <;> decide
  | hyp e =>
    show (∑ r : Fin 2, oddityEntry (![2 ^ (e.toNat + 1) * 1, 2 ^ (e.toNat + 1) * (-1)] r)) =
      0 + 4 * (if e.toNat % 2 = 1 then 1 else 0) * signInd Sign.plus
    rw [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero, oddityEntry_two_pow,
      oddityEntry_two_pow_neg]
    simp [signInd]
  | ell e =>
    show (∑ r : Fin 2, oddityEntry (![2 ^ (e.toNat + 1) * 1, 2 ^ (e.toNat + 1) * 3] r)) =
      0 + 4 * (if e.toNat % 2 = 1 then 1 else 0) * signInd Sign.minus
    rw [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero, oddityEntry_two_pow,
      Rational.oddityEntry_two_pow_mul _ 3 (by decide)]
    have ho : Odd (e.toNat + 1) ↔ (e.toNat + 1) % 2 = 1 := Nat.odd_iff
    simp only [ho]
    rcases Nat.mod_two_eq_zero_or_one e.toNat with h | h
    · simp only [show (e.toNat + 1) % 2 = 1 by omega, h]; decide
    · simp only [show (e.toNat + 1) % 2 = 0 by omega, h]; decide

/-! ### Sums over the blocks of one exponent -/

theorem get_cons_zero' {α : Type*} (a : α) (l : List α) : (a :: l).get (0 : Fin (l.length + 1)) = a := rfl

theorem get_cons_succ' {α : Type*} (a : α) (l : List α) (j : Fin l.length) : (a :: l).get j.succ = l.get j := rfl

theorem sum_fiber {α M : Type*} [AddCommMonoid M] (l : List α) (p : α → Prop) [DecidablePred p] (f : α → M) :
    ∑ j ∈ univ.filter (fun j : Fin l.length => p (l.get j)), f (l.get j) = ((l.filter fun a => p a).map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [Finset.sum_filter] at ih ⊢
    rw [show ∀ g : Fin (a :: l).length → M, (∑ j, g j) = g 0 + ∑ j : Fin l.length, g j.succ from fun g => Fin.sum_univ_succ (n := l.length) g]
    simp only [get_cons_zero', get_cons_succ']
    rw [ih]
    by_cases h : p a <;> simp [List.filter_cons, h]

theorem prod_fiber {α M : Type*} [CommMonoid M] (l : List α) (p : α → Prop) [DecidablePred p] (f : α → M) :
    ∏ j ∈ univ.filter (fun j : Fin l.length => p (l.get j)), f (l.get j) =
      ((l.filter fun a => p a).map f).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [Finset.prod_filter] at ih ⊢
    rw [show ∀ g : Fin (a :: l).length → M, (∏ j, g j) = g 0 * ∏ j : Fin l.length, g j.succ from fun g => Fin.prod_univ_succ (n := l.length) g]
    simp only [get_cons_zero', get_cons_succ']
    rw [ih]
    by_cases h : p a <;> simp [List.filter_cons, h]

theorem unitOf_congr_right {a b b' : ZMod 8} (h : 4 * b = 4 * b') : unitOf a b = unitOf a b' := by
  unfold unitOf; rw [h]

theorem unitOf_signInd_mul (a : ZMod 8) (x y : Sign) :
    unitOf a (signInd (x.mul y)) = unitOf a (signInd x + signInd y) := by
  apply unitOf_congr_right
  cases x <;> cases y <;> decide

theorem four_mul_signInd_mul (k : ZMod 8) (x y : Sign) :
    4 * k * signInd (x.mul y) = 4 * k * signInd x + 4 * k * signInd y := by
  have h8 : (8 : ZMod 8) = 0 := by decide
  cases x <;> cases y <;> simp [Sign.mul, Sign.flip, signInd] <;> linear_combination (-k) * h8

theorem prod_unit_list (B : List DyBlock) (hB : ∀ b ∈ B, b.Valid) :
    (B.map fun b => ((bUnit b : ℤ) : ZMod 8)).prod =
      unitOf ((B.map blockOddity).sum - (((B.map DyBlock.dim).sum : ℕ) : ZMod 8))
        (signInd (Sign.prodList (B.map blockSign))) := by
  induction B with
  | nil => simp only [List.map_nil, List.prod_nil, List.sum_nil, Sign.prodList]; decide
  | cons b B ih =>
    have hb := hB b List.mem_cons_self
    have hB' : ∀ x ∈ B, x.Valid := fun x hx => hB x (List.mem_cons_of_mem _ hx)
    simp only [List.map_cons, List.prod_cons, List.sum_cons, Sign.prodList]
    rw [ih hB', bUnit_cast b hb]
    obtain ⟨c, hc⟩ := blockOddity_sub_dim b hb
    obtain ⟨C, hC⟩ := exists_sub_eq_two_mul (oddity_parity B hB')
    rw [hc, hC, unitOf_mul, unitOf_signInd_mul]
    congr 1
    rw [Nat.cast_add]
    linear_combination -hc - hC

theorem sum_oddB_list (B : List DyBlock) (hB : ∀ b ∈ B, b.Valid) (k : ℕ)
    (hk : ∀ b ∈ B, (blockExp b).toNat = k) :
    (B.map bOdd).sum = (B.map blockOddity).sum + 4 * (k : ZMod 8) * signInd (Sign.prodList (B.map blockSign)) := by
  induction B with
  | nil => simp [Sign.prodList, signInd]
  | cons b B ih =>
    have hb := hB b List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, Sign.prodList]
    rw [ih (fun x hx => hB x (List.mem_cons_of_mem _ hx)) (fun x hx => hk x (List.mem_cons_of_mem _ hx)),
      bOdd_eq b hb, hk b List.mem_cons_self, four_mul_signInd_mul]
    ring

section Symbol

variable (D : List DyBlock) (hD : ∀ b ∈ D, b.Valid) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b)

/-- The exponent of the block $j$, as a natural number. -/
def bexp (j : Fin D.length) : ℕ := (blockExp (D.get j)).toNat

include hD0 in
theorem filter_exp_eq (k : ℕ) :
    (D.filter fun b => decide (blockExp b = (k : ℤ))) = D.filter fun b => decide ((blockExp b).toNat = k) := by
  refine List.filter_congr fun b hb => ?_
  have := hD0 b hb
  by_cases h : blockExp b = k <;> simp [h] <;> omega

theorem blockSymbol_oddity (k : ℕ) :
    (blockSymbol D k).oddity = ((D.filter fun b => decide (blockExp b = (k : ℤ))).map blockOddity).sum := rfl

theorem blockSymbol_dim (k : ℕ) :
    (blockSymbol D k).dim = ((D.filter fun b => decide (blockExp b = (k : ℤ))).map DyBlock.dim).sum := rfl

theorem blockSymbol_sign (k : ℕ) :
    (blockSymbol D k).sign = Sign.prodList ((D.filter fun b => decide (blockExp b = (k : ℤ))).map blockSign) := rfl

include hD hD0 in
theorem cu_blockSymbol (k : ℕ) :
    cu (blockSymbol D k) = ∏ j ∈ univ.filter (fun j => bexp D j = k), ((bUnit (D.get j) : ℤ) : ZMod 8) := by
  rw [show (∏ j ∈ univ.filter (fun j => bexp D j = k), ((bUnit (D.get j) : ℤ) : ZMod 8)) =
      ((D.filter fun b => decide ((blockExp b).toNat = k)).map fun b => ((bUnit b : ℤ) : ZMod 8)).prod from
    prod_fiber D (fun b => (blockExp b).toNat = k) (fun b => ((bUnit b : ℤ) : ZMod 8)), ← filter_exp_eq D hD0,
    prod_unit_list _ (fun b hb => hD b (List.mem_of_mem_filter hb))]
  unfold cu
  rw [blockSymbol_oddity, blockSymbol_dim, blockSymbol_sign]

include hD hD0 in
theorem oddW_blockSymbol (k : ℕ) :
    oddW k (blockSymbol D k) = ∑ j ∈ univ.filter (fun j => bexp D j = k), bOdd (D.get j) := by
  rw [show (∑ j ∈ univ.filter (fun j => bexp D j = k), bOdd (D.get j)) =
      ((D.filter fun b => decide ((blockExp b).toNat = k)).map bOdd).sum from
    sum_fiber D (fun b => (blockExp b).toNat = k) bOdd, sum_oddB_list _ (fun b hb => hD b (List.mem_of_mem_filter hb)) k
      (fun b hb => by simpa using List.of_mem_filter hb), ← filter_exp_eq D hD0]
  unfold oddW
  rw [blockSymbol_oddity, blockSymbol_sign]

include hD0 in
theorem dim_blockSymbol (k : ℕ) :
    (blockSymbol D k).dim = ∑ j ∈ univ.filter (fun j => bexp D j = k), (D.get j).dim := by
  rw [show (∑ j ∈ univ.filter (fun j => bexp D j = k), (D.get j).dim) =
      ((D.filter fun b => decide ((blockExp b).toNat = k)).map DyBlock.dim).sum from
    sum_fiber D (fun b => (blockExp b).toNat = k) DyBlock.dim, ← filter_exp_eq D hD0, blockSymbol_dim]

include hD0 in
theorem isTypeI_blockSymbol (k : ℕ) :
    IsTypeI (blockSymbol D) k ↔ ∃ j, bexp D j = k ∧ IsSqBlock (D.get j) := by
  unfold IsTypeI
  simp only [blockSymbol]
  rw [filter_exp_eq D hD0]
  constructor
  · intro h
    split_ifs at h with h'
    · obtain ⟨b, hb, hsq⟩ := List.any_eq_true.1 h'
      obtain ⟨hbD, hbk⟩ := List.mem_filter.1 hb
      obtain ⟨j, rfl⟩ := List.get_of_mem hbD
      exact ⟨j, by simpa [bexp] using hbk, by simpa using hsq⟩
  · rintro ⟨j, hj, hsq⟩
    rw [if_pos]
    exact List.any_eq_true.2 ⟨D.get j, List.mem_filter.2 ⟨List.get_mem _ _, by simpa [bexp] using hj⟩,
      by simpa using hsq⟩

include hD hD0 in
theorem unitPre_blockSymbol : ∀ m : ℕ,
    unitPre (blockSymbol D) m = ∏ j ∈ univ.filter (fun j => bexp D j < m), ((bUnit (D.get j) : ℤ) : ZMod 8)
  | 0 => by simp [unitPre]
  | m + 1 => by
    rw [unitPre, unitPre_blockSymbol m, cu_blockSymbol D hD hD0, ← Finset.prod_union]
    · congr 1; ext j; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    · exact Finset.disjoint_filter.2 fun j _ h1 h2 => by omega

include hD hD0 in
theorem oddPre_blockSymbol : ∀ m : ℕ,
    oddPre (blockSymbol D) m = ∑ j ∈ univ.filter (fun j => bexp D j < m), bOdd (D.get j)
  | 0 => by simp [oddPre]
  | m + 1 => by
    rw [oddPre, oddPre_blockSymbol m, oddW_blockSymbol D hD hD0, ← Finset.sum_union]
    · congr 1; ext j; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    · exact Finset.disjoint_filter.2 fun j _ h1 h2 => by omega

end Symbol

end QuadFormsKB.ConwaySloane.TwoAdic
