/-
# Cassels, Chapter 9, Lemma 4.3: matrix algebra for the local proof

**Layer:** symmetric matrices over a commutative ring $R$, indexed by a finite type; congruence $A \sim B$
(`MEq`: $T^{\mathsf T} A T = B$ with $\det T$ a unit) and entrywise divisibility (`MDvd`).

**Proves** the block manipulations used for Cassels' Lemma 4.3 (`Ch9Sec4Congr.lean`): transport along reindexing,
orthogonal sums of congruences (`MEq.fromBlocks`), the pivot $\begin{pmatrix} tK_0 & tC_0 \\ tC_0^{\mathsf T} & N
\end{pmatrix} \sim \begin{pmatrix} tK_0 & 0 \\ 0 & N - tC_0^{\mathsf T}K_0^{-1}C_0\end{pmatrix}$ for $\det K_0$ a unit
(`meq_pivot`), the congruence of the complements of congruent matrices (`mdvd_compl`) and a unipotent twist
(`twist_eq`). Indices are 0-based.
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination

open Matrix

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Siegel.CongrLocal

variable {R : Type*} [CommRing R]

section Basic

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **Congruence of matrices:** $T^{\mathsf T} A T = B$ for some $T$ with $\det T$ a unit. -/
def MEq (A B : Matrix ι ι R) : Prop := ∃ T : Matrix ι ι R, IsUnit T.det ∧ Tᵀ * A * T = B

/-- **Entrywise divisibility:** $m \mid M_{ij}$ for all $i, j$. -/
def MDvd {α β : Type*} (m : R) (M : Matrix α β R) : Prop := ∀ i j, m ∣ M i j

/-- `MEq` is reflexive. -/
theorem MEq.refl (A : Matrix ι ι R) : MEq A A := ⟨1, by simp, by simp⟩

/-- `MEq` is transitive. -/
theorem MEq.trans {A B C : Matrix ι ι R} (h : MEq A B) (h' : MEq B C) : MEq A C := by
  obtain ⟨T, hT, rfl⟩ := h
  obtain ⟨T', hT', rfl⟩ := h'
  refine ⟨T * T', by rw [det_mul]; exact hT.mul hT', ?_⟩
  rw [transpose_mul]; simp only [Matrix.mul_assoc]

/-- `MEq` is symmetric. -/
theorem MEq.symm {A B : Matrix ι ι R} (h : MEq A B) : MEq B A := by
  obtain ⟨T, hT, rfl⟩ := h
  refine ⟨T⁻¹, isUnit_nonsing_inv_det T hT, ?_⟩
  rw [transpose_nonsing_inv]
  have h1 : (Tᵀ)⁻¹ * Tᵀ = 1 := nonsing_inv_mul _ (by rw [det_transpose]; exact hT)
  have h2 : T * T⁻¹ = 1 := mul_nonsing_inv _ hT
  calc (Tᵀ)⁻¹ * (Tᵀ * A * T) * T⁻¹ = ((Tᵀ)⁻¹ * Tᵀ) * A * (T * T⁻¹) := by simp only [Matrix.mul_assoc]
    _ = A := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

/-- A matrix is congruent to each of its conjugates $T^{\mathsf T}AT$, $\det T$ a unit. -/
theorem MEq.conj (A T : Matrix ι ι R) (hT : IsUnit T.det) : MEq A (Tᵀ * A * T) := ⟨T, hT, rfl⟩

/-- Congruent matrices have determinants differing by a unit square. -/
theorem MEq.det {A B : Matrix ι ι R} (h : MEq A B) : ∃ r : R, IsUnit r ∧ B.det = r ^ 2 * A.det := by
  obtain ⟨T, hT, rfl⟩ := h
  exact ⟨T.det, hT, by rw [det_mul, det_mul, det_transpose]; ring⟩

/-- Congruence is preserved by scaling both matrices. -/
theorem MEq.smul {A B : Matrix ι ι R} (h : MEq A B) (t : R) : MEq (t • A) (t • B) := by
  obtain ⟨T, hT, rfl⟩ := h
  exact ⟨T, hT, by rw [Matrix.mul_smul, Matrix.smul_mul]⟩

/-- Congruence is preserved by symmetric conjugation of both sides. -/
theorem MEq.conj_both {A B : Matrix ι ι R} (P : Matrix ι ι R) (hP : IsUnit P.det)
    (h : MEq (Pᵀ * A * P) (Pᵀ * B * P)) : MEq A B :=
  ((MEq.conj A P hP).trans h).trans (MEq.conj B P hP).symm

/-- Transport of a congruence along a reindexing $e : \kappa \simeq \iota$. -/
theorem MEq.of_submatrix {A B : Matrix ι ι R} (e : κ ≃ ι) (h : MEq (A.submatrix e e) (B.submatrix e e)) :
    MEq A B := by
  obtain ⟨T, hT, hTB⟩ := h
  have hX : ∀ X : Matrix ι ι R, (X.submatrix e e).submatrix e.symm e.symm = X := fun X => by
    ext i j; simp
  refine ⟨T.submatrix e.symm e.symm, by rw [det_submatrix_equiv_self]; exact hT, ?_⟩
  rw [transpose_submatrix, ← hX A, submatrix_mul_equiv _ _ _ e.symm, submatrix_mul_equiv _ _ _ e.symm,
    hTB, hX]

/-- Transport of a congruence to a reindexing. -/
theorem MEq.submatrix {A B : Matrix ι ι R} (e : κ ≃ ι) (h : MEq A B) : MEq (A.submatrix e e) (B.submatrix e e) := by
  obtain ⟨T, hT, rfl⟩ := h
  refine ⟨T.submatrix e e, by rw [det_submatrix_equiv_self]; exact hT, ?_⟩
  rw [transpose_submatrix, submatrix_mul_equiv _ _ _ e, submatrix_mul_equiv _ _ _ e]

/-- Orthogonal sums of congruences are congruences. -/
theorem MEq.fromBlocks {K K' : Matrix κ κ R} {N N' : Matrix ι ι R} (hK : MEq K K') (hN : MEq N N') :
    MEq (Matrix.fromBlocks K 0 0 N) (Matrix.fromBlocks K' 0 0 N') := by
  obtain ⟨T, hT, rfl⟩ := hK
  obtain ⟨S, hS, rfl⟩ := hN
  refine ⟨Matrix.fromBlocks T 0 0 S, by rw [det_fromBlocks_zero₂₁]; exact hT.mul hS, ?_⟩
  simp [fromBlocks_transpose, fromBlocks_multiply]

/-! ### Entrywise divisibility -/

section MDvd

variable {α β γ : Type*} [Fintype β]

theorem MDvd.add {m : R} {M M' : Matrix α γ R} (h : MDvd m M) (h' : MDvd m M') : MDvd m (M + M') :=
  fun i j => dvd_add (h i j) (h' i j)

theorem MDvd.sub {m : R} {M M' : Matrix α γ R} (h : MDvd m M) (h' : MDvd m M') : MDvd m (M - M') :=
  fun i j => dvd_sub (h i j) (h' i j)

theorem MDvd.neg {m : R} {M : Matrix α γ R} (h : MDvd m M) : MDvd m (-M) :=
  fun i j => by simpa using h i j

theorem MDvd.zero (m : R) : MDvd m (0 : Matrix α γ R) := fun _ _ => dvd_zero m

theorem MDvd.mul_left {m : R} {M : Matrix β γ R} (h : MDvd m M) (X : Matrix α β R) : MDvd m (X * M) :=
  fun i j => by rw [mul_apply]; exact Finset.dvd_sum fun k _ => dvd_mul_of_dvd_right (h k j) _

theorem MDvd.mul_right {m : R} {M : Matrix α β R} (h : MDvd m M) (X : Matrix β γ R) : MDvd m (M * X) :=
  fun i j => by rw [mul_apply]; exact Finset.dvd_sum fun k _ => dvd_mul_of_dvd_left (h i k) _

theorem MDvd.mul {m m' : R} {X : Matrix α β R} {Y : Matrix β γ R} (h : MDvd m X) (h' : MDvd m' Y) :
    MDvd (m * m') (X * Y) :=
  fun i j => by rw [mul_apply]; exact Finset.dvd_sum fun k _ => mul_dvd_mul (h i k) (h' k j)

theorem MDvd.transpose {m : R} {M : Matrix α γ R} (h : MDvd m M) : MDvd m Mᵀ := fun i j => h j i

theorem MDvd.smul {m : R} {M : Matrix α γ R} (h : MDvd m M) (c : R) : MDvd m (c • M) :=
  fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact dvd_mul_of_dvd_right (h i j) c

theorem MDvd.smul_mul {m : R} {M : Matrix α γ R} (h : MDvd m M) (c : R) : MDvd (c * m) (c • M) :=
  fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_dvd_mul_left c (h i j)

theorem MDvd.of_dvd {m m' : R} {M : Matrix α γ R} (h : MDvd m M) (hm : m' ∣ m) : MDvd m' M :=
  fun i j => hm.trans (h i j)

theorem MDvd.submatrix {m : R} {M : Matrix α γ R} (h : MDvd m M) {α' γ' : Type*} (f : α' → α) (g : γ' → γ) :
    MDvd m (M.submatrix f g) := fun i j => h (f i) (g j)

theorem mdvd_smul (m : R) (M : Matrix α γ R) : MDvd m (m • M) :=
  fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact dvd_mul_right m _

end MDvd

end Basic

/-! ### The pivot -/

section Pivot

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The inverse of a symmetric matrix is symmetric. -/
theorem inv_transpose_of_symm {K : Matrix κ κ R} (hK : Kᵀ = K) : (K⁻¹)ᵀ = K⁻¹ := by
  rw [transpose_nonsing_inv, hK]

/-- **The pivot:** for $K_0$ symmetric with $\det K_0$ a unit,
$\begin{pmatrix} tK_0 & tC_0 \\ tC_0^{\mathsf T} & N\end{pmatrix} \sim
\begin{pmatrix} tK_0 & 0 \\ 0 & N - tC_0^{\mathsf T}K_0^{-1}C_0\end{pmatrix}$. -/
theorem meq_pivot (t : R) {K₀ : Matrix κ κ R} (hK₀ : K₀ᵀ = K₀) (hu : IsUnit K₀.det) (C₀ : Matrix κ ι R)
    (N : Matrix ι ι R) :
    MEq (Matrix.fromBlocks (t • K₀) (t • C₀) (t • C₀ᵀ) N)
      (Matrix.fromBlocks (t • K₀) 0 0 (N - t • (C₀ᵀ * K₀⁻¹ * C₀))) := by
  refine ⟨Matrix.fromBlocks 1 (-(K₀⁻¹ * C₀)) 0 1, by simp [det_fromBlocks_zero₂₁], ?_⟩
  have hi := inv_transpose_of_symm hK₀
  have h1 : K₀ * (K₀⁻¹ * C₀) = C₀ := mul_nonsing_inv_cancel_left K₀ C₀ hu
  have h2 : C₀ᵀ * K₀⁻¹ * K₀ = C₀ᵀ := by rw [Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [transpose_one, transpose_zero, transpose_neg, transpose_mul, hi, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul, Matrix.smul_mul,
    Matrix.mul_smul, h1, neg_add_cancel, smul_neg, smul_zero, Matrix.mul_assoc, nonsing_inv_mul _ hu, neg_zero]
  congr 1
  abel

/-- **Complements of congruent matrices are congruent:** with $\Gamma = K_0^{-1}C_0$, if $tK_0' \equiv tK_0$,
$tC_0' \equiv tC_0$ and $N' \equiv N \pmod m$ then
$N' - tC_0'^{\mathsf T}K_0'^{-1}C_0' \equiv N - tC_0^{\mathsf T}K_0^{-1}C_0 \pmod m$. -/
theorem mdvd_compl {m t : R} {K₀ K₀' : Matrix κ κ R} (hu : IsUnit K₀.det) (hu' : IsUnit K₀'.det)
    {C₀ C₀' : Matrix κ ι R} {N N' : Matrix ι ι R} (hK : MDvd m (t • K₀' - t • K₀))
    (hC : MDvd m (t • C₀' - t • C₀)) (hN : MDvd m (N' - N)) :
    MDvd m ((N' - t • (C₀'ᵀ * K₀'⁻¹ * C₀')) - (N - t • (C₀ᵀ * K₀⁻¹ * C₀))) := by
  have key : t • (C₀'ᵀ * K₀'⁻¹ * C₀') - t • (C₀ᵀ * K₀⁻¹ * C₀) =
      (t • C₀' - t • C₀)ᵀ * (K₀'⁻¹ * C₀') +
        C₀ᵀ * (K₀'⁻¹ * ((t • C₀' - t • C₀) - (t • K₀' - t • K₀) * (K₀⁻¹ * C₀))) := by
    have e1 : K₀'⁻¹ * (K₀' * (K₀⁻¹ * C₀)) = K₀⁻¹ * C₀ := nonsing_inv_mul_cancel_left K₀' _ hu'
    have e2 : K₀ * (K₀⁻¹ * C₀) = C₀ := mul_nonsing_inv_cancel_left K₀ C₀ hu
    simp only [transpose_sub, transpose_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
      Matrix.mul_smul, e1, e2, Matrix.mul_assoc]
    abel
  have hD : MDvd m ((t • C₀' - t • C₀) - (t • K₀' - t • K₀) * (K₀⁻¹ * C₀)) :=
    hC.sub (hK.mul_right _)
  have : (N' - t • (C₀'ᵀ * K₀'⁻¹ * C₀')) - (N - t • (C₀ᵀ * K₀⁻¹ * C₀)) =
      (N' - N) - (t • (C₀'ᵀ * K₀'⁻¹ * C₀') - t • (C₀ᵀ * K₀⁻¹ * C₀)) := by abel
  rw [this, key]
  exact hN.sub ((hC.transpose.mul_right _).add ((hD.mul_left _).mul_left _))

/-- **A unipotent twist:** $\begin{pmatrix} 1 & 0 \\ Y & 1\end{pmatrix}^{\mathsf T}
\begin{pmatrix} K & 0 \\ 0 & N\end{pmatrix}\begin{pmatrix} 1 & 0 \\ Y & 1\end{pmatrix} =
\begin{pmatrix} K + Y^{\mathsf T}NY & Y^{\mathsf T}N \\ NY & N\end{pmatrix}$. -/
theorem twist_eq (K : Matrix κ κ R) (N : Matrix ι ι R) (Y : Matrix ι κ R) :
    (Matrix.fromBlocks 1 0 Y 1)ᵀ * Matrix.fromBlocks K 0 0 N * Matrix.fromBlocks 1 0 Y 1 =
      Matrix.fromBlocks (K + Yᵀ * N * Y) (Yᵀ * N) (N * Y) N := by
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp [Matrix.mul_assoc]

/-- The twist has determinant $1$. -/
theorem det_twist (Y : Matrix ι κ R) : (Matrix.fromBlocks (1 : Matrix κ κ R) 0 Y 1).det = 1 := by
  rw [det_fromBlocks_zero₁₂]; simp

end Pivot

/-! ### Reduction by a pivot block -/

section Reduce

variable [IsDomain R] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- $K \sim r^2 K$ for a unit $r$. -/
theorem MEq.smul_sq (K : Matrix κ κ R) {r : R} (hr : IsUnit r) : MEq K (r ^ 2 • K) :=
  ⟨r • 1, by rw [det_smul, det_one, mul_one]; exact hr.pow _, by
    simp [pow_two, smul_smul]⟩

/-- **Reduction by a pivot block** on the coordinates $P$: if $A_{PP} = tK_0$ ($K_0$ symmetric, $\det K_0$ a
unit), $t$ divides the rows of $A$ in $P$, $t \mid m$, $B \equiv A \pmod m$ and $A_{PP} \sim B_{PP}$, then $A \sim B$
provided the complements are congruent whenever they satisfy the hypotheses of the induction. -/
theorem pivot_reduce (P : ι → Prop) [DecidablePred P] {A B : Matrix ι ι R} (hA : Aᵀ = A) (hB : Bᵀ = B)
    (hA0 : A.det ≠ 0) (hdet : ∃ s, IsUnit s ∧ B.det = s ^ 2 * A.det) {t m : R}
    (K₀ : Matrix {x // P x} {x // P x} R) (hK₀ : K₀ᵀ = K₀) (hu : IsUnit K₀.det)
    (hK : ∀ i j : {x // P x}, A i j = t * K₀ i j)
    (hrow : ∀ (i : {x // P x}) (j : {x // ¬ P x}), t ∣ A i j) (htm : t ∣ m) (hBA : MDvd m (B - A))
    (h11 : MEq (A.submatrix (fun x : {x // P x} => x.1) (fun x => x.1))
      (B.submatrix (fun x : {x // P x} => x.1) (fun x => x.1)))
    (hcompl : ∀ A' B' : Matrix {x // ¬ P x} {x // ¬ P x} R, A'ᵀ = A' → B'ᵀ = B' → A'.det ≠ 0 →
      A'.det ∣ A.det → MDvd m (B' - A') → (∃ s, IsUnit s ∧ B'.det = s ^ 2 * A'.det) → MEq A' B') :
    MEq A B := by
  apply MEq.of_submatrix (Equiv.sumCompl P)
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : Matrix {x // P x} {x // ¬ P x} R, ∀ (i : {x // P x}) (j : {x // ¬ P x}), A i j = t * C₀ i j :=
    ⟨Matrix.of fun i j => (hrow i j).choose, fun i j => (hrow i j).choose_spec⟩
  have hA11 : (A.submatrix (fun x : {x // P x} => x.1) (fun x => x.1)) = t • K₀ := by
    ext i j; simp [hK]
  obtain ⟨T, hT, hTB⟩ := h11
  set K₀' := Tᵀ * K₀ * T with hK₀'def
  have hB11 : (B.submatrix (fun x : {x // P x} => x.1) (fun x => x.1)) = t • K₀' := by
    rw [← hTB, hA11, Matrix.mul_smul, Matrix.smul_mul]
  have hBK : ∀ i j : {x // P x}, B i j = t * K₀' i j := fun i j => by
    have := congrFun (congrFun hB11 i) j
    simpa using this
  have hu' : IsUnit K₀'.det := by
    rw [hK₀'def, det_mul, det_mul, det_transpose]; exact (hT.mul hu).mul hT
  have hK₀' : K₀'ᵀ = K₀' := by
    rw [hK₀'def, transpose_mul, transpose_mul, transpose_transpose, hK₀, Matrix.mul_assoc]
  have hrowB : ∀ (i : {x // P x}) (j : {x // ¬ P x}), t ∣ B i j := fun i j => by
    have h1 := htm.trans (hBA i j)
    rw [Matrix.sub_apply] at h1
    have h2 : t ∣ A i j := ⟨C₀ i j, hC₀ i j⟩
    simpa using dvd_add h1 h2
  obtain ⟨C₀', hC₀'⟩ : ∃ C₀ : Matrix {x // P x} {x // ¬ P x} R, ∀ (i : {x // P x}) (j : {x // ¬ P x}), B i j = t * C₀ i j :=
    ⟨Matrix.of fun i j => (hrowB i j).choose, fun i j => (hrowB i j).choose_spec⟩
  set N := A.submatrix (fun x : {x // ¬ P x} => x.1) (fun x : {x // ¬ P x} => x.1) with hNdef
  set N' := B.submatrix (fun x : {x // ¬ P x} => x.1) (fun x : {x // ¬ P x} => x.1) with hN'def
  have hsym : ∀ {M : Matrix ι ι R}, Mᵀ = M → ∀ i j, M i j = M j i := fun {M} h i j => by
    rw [← transpose_apply M i j, h]
  have hAe : A.submatrix (Equiv.sumCompl P) (Equiv.sumCompl P) =
      Matrix.fromBlocks (t • K₀) (t • C₀) (t • C₀ᵀ) N := by
    ext (i | i) (j | j)
    · exact hK i j
    · exact hC₀ i j
    · show A i.1 j.1 = t * C₀ j i
      rw [hsym hA, hC₀]
    · rfl
  have hBe : B.submatrix (Equiv.sumCompl P) (Equiv.sumCompl P) =
      Matrix.fromBlocks (t • K₀') (t • C₀') (t • C₀'ᵀ) N' := by
    ext (i | i) (j | j)
    · exact hBK i j
    · exact hC₀' i j
    · show B i.1 j.1 = t * C₀' j i
      rw [hsym hB, hC₀']
    · rfl
  have p1 : MEq (A.submatrix (Equiv.sumCompl P) (Equiv.sumCompl P))
      (Matrix.fromBlocks (t • K₀) 0 0 (N - t • (C₀ᵀ * K₀⁻¹ * C₀))) := by
    rw [hAe]; exact meq_pivot t hK₀ hu C₀ N
  have p2 : MEq (B.submatrix (Equiv.sumCompl P) (Equiv.sumCompl P))
      (Matrix.fromBlocks (t • K₀') 0 0 (N' - t • (C₀'ᵀ * K₀'⁻¹ * C₀'))) := by
    rw [hBe]; exact meq_pivot t hK₀' hu' C₀' N'
  set A' := N - t • (C₀ᵀ * K₀⁻¹ * C₀) with hA'def
  set B' := N' - t • (C₀'ᵀ * K₀'⁻¹ * C₀') with hB'def
  have hNs : Nᵀ = N := by ext i j; simp [hNdef, hsym hA i.1 j.1]
  have hN's : N'ᵀ = N' := by ext i j; simp [hN'def, hsym hB i.1 j.1]
  have hA's : A'ᵀ = A' := by
    rw [hA'def, transpose_sub, transpose_smul, transpose_mul, transpose_mul, transpose_transpose,
      inv_transpose_of_symm hK₀, hNs, Matrix.mul_assoc]
  have hB's : B'ᵀ = B' := by
    rw [hB'def, transpose_sub, transpose_smul, transpose_mul, transpose_mul, transpose_transpose,
      inv_transpose_of_symm hK₀', hN's, Matrix.mul_assoc]
  obtain ⟨r₁, hr₁, e1⟩ := p1.det
  obtain ⟨r₂, hr₂, e2⟩ := p2.det
  obtain ⟨s, hs, hsd⟩ := hdet
  have h11' : MEq (t • K₀) (t • K₀') := (MEq.conj K₀ T hT).smul t
  obtain ⟨r₃, hr₃, e3⟩ := h11'.det
  rw [det_fromBlocks_zero₂₁, det_submatrix_equiv_self] at e1 e2
  set D₁ := (t • K₀).det
  have hne : D₁ * A'.det ≠ 0 := by rw [e1]; exact mul_ne_zero (hr₁.pow 2).ne_zero hA0
  have hD₁ : D₁ ≠ 0 := left_ne_zero_of_mul hne
  have hA'0 : A'.det ≠ 0 := right_ne_zero_of_mul hne
  obtain ⟨u₁, hu₁⟩ := hr₁.exists_right_inv
  obtain ⟨u₃, hu₃⟩ := hr₃.exists_right_inv
  have hmid : MEq (Matrix.fromBlocks (t • K₀) 0 0 A') (Matrix.fromBlocks (t • K₀') 0 0 B') := by
    refine MEq.fromBlocks h11' (hcompl A' B' hA's hB's hA'0 ?_ ?_ ?_)
    · exact ⟨u₁ ^ 2 * D₁, by linear_combination (-(u₁ ^ 2)) * e1 - (A.det * (r₁ * u₁ + 1)) * hu₁⟩
    · refine mdvd_compl hu hu' ?_ ?_ ?_
      · intro i j
        have := hBA i j
        rw [Matrix.sub_apply, hBK, hK] at this
        simpa [Matrix.smul_apply] using this
      · intro i j
        have := hBA i j
        rw [Matrix.sub_apply, hC₀', hC₀] at this
        simpa [Matrix.smul_apply] using this
      · intro i j
        simpa [hNdef, hN'def] using hBA i j
    · have hr₂u : IsUnit (r₂ * s * u₁ * u₃) := by
        refine ((hr₂.mul hs).mul ?_).mul ?_
        · exact ⟨⟨u₁, r₁, by rw [mul_comm]; exact hu₁, hu₁⟩, rfl⟩
        · exact ⟨⟨u₃, r₃, by rw [mul_comm]; exact hu₃, hu₃⟩, rfl⟩
      refine ⟨r₂ * s * u₁ * u₃, hr₂u, mul_left_cancel₀ hD₁ ?_⟩
      rw [e3] at e2
      linear_combination u₃ ^ 2 * e2 + (u₃ ^ 2 * r₂ ^ 2) * hsd - (u₃ ^ 2 * r₂ ^ 2 * s ^ 2 * u₁ ^ 2) * e1 -
        (D₁ * B'.det * (r₃ * u₃ + 1)) * hu₃ - (u₃ ^ 2 * r₂ ^ 2 * s ^ 2 * A.det * (r₁ * u₁ + 1)) * hu₁
  exact p1.trans (hmid.trans p2.symm)

/-- **The pivot in the original coordinates:** with $A_{PP} = tK_0$ and $A_{P,P^c} = tC_0$,
$A \sim \begin{pmatrix} tK_0 & 0 \\ 0 & A_{P^cP^c} - tC_0^{\mathsf T}K_0^{-1}C_0\end{pmatrix}$ (reindexed by `Equiv.sumCompl`). -/
theorem pivot_split (P : ι → Prop) [DecidablePred P] {A : Matrix ι ι R} (hA : Aᵀ = A) (t : R)
    {K₀ : Matrix {x // P x} {x // P x} R} (hK₀ : K₀ᵀ = K₀) (hu : IsUnit K₀.det)
    (C₀ : Matrix {x // P x} {x // ¬ P x} R)
    (hK : ∀ i j : {x // P x}, A i j = t * K₀ i j)
    (hC : ∀ (i : {x // P x}) (j : {x // ¬ P x}), A i j = t * C₀ i j) :
    MEq (A.submatrix (Equiv.sumCompl P) (Equiv.sumCompl P))
      (Matrix.fromBlocks (t • K₀) 0 0
        (A.submatrix (fun x : {x // ¬ P x} => x.1) (fun x : {x // ¬ P x} => x.1) - t • (C₀ᵀ * K₀⁻¹ * C₀))) := by
  have hsym : ∀ i j, A i j = A j i := fun i j => by rw [← transpose_apply A i j, hA]
  have hAe : A.submatrix (Equiv.sumCompl P) (Equiv.sumCompl P) =
      Matrix.fromBlocks (t • K₀) (t • C₀) (t • C₀ᵀ)
        (A.submatrix (fun x : {x // ¬ P x} => x.1) (fun x : {x // ¬ P x} => x.1)) := by
    ext (i | i) (j | j)
    · exact hK i j
    · exact hC i j
    · show A i.1 j.1 = t * C₀ j i
      rw [hsym, hC]
    · rfl
  rw [hAe]; exact meq_pivot t hK₀ hu C₀ _

/-- The complement $N - tC_0^{\mathsf T}K_0^{-1}C_0$ of symmetric matrices is symmetric. -/
theorem compl_symm {N : Matrix ι ι R} (hN : Nᵀ = N) {K₀ : Matrix κ κ R} (hK₀ : K₀ᵀ = K₀) (t : R)
    (C₀ : Matrix κ ι R) : (N - t • (C₀ᵀ * K₀⁻¹ * C₀))ᵀ = N - t • (C₀ᵀ * K₀⁻¹ * C₀) := by
  rw [transpose_sub, transpose_smul, transpose_mul, transpose_mul, transpose_transpose,
    inv_transpose_of_symm hK₀, hN, Matrix.mul_assoc]

/-- A principal submatrix of a symmetric matrix is symmetric. -/
theorem submatrix_symm {A : Matrix ι ι R} (hA : Aᵀ = A) {α : Type*} (f : α → ι) :
    (A.submatrix f f)ᵀ = A.submatrix f f := by
  rw [transpose_submatrix, hA]

/-- **Determinants up to unit squares:** $\det Y = r^2 \det X$ for a unit $r$. -/
def DetRel (X Y : Matrix ι ι R) : Prop := ∃ r : R, IsUnit r ∧ Y.det = r ^ 2 * X.det

/-- Congruent matrices are `DetRel`. -/
theorem MEq.detRel {X Y : Matrix ι ι R} (h : MEq X Y) : DetRel X Y := h.det

/-- `DetRel` is transitive. -/
theorem DetRel.trans {X Y Z : Matrix ι ι R} (h : DetRel X Y) (h' : DetRel Y Z) : DetRel X Z := by
  obtain ⟨r, hr, e⟩ := h
  obtain ⟨r', hr', e'⟩ := h'
  exact ⟨r' * r, hr'.mul hr, by rw [e', e]; ring⟩

/-- `DetRel` is symmetric. -/
theorem DetRel.symm {X Y : Matrix ι ι R} (h : DetRel X Y) : DetRel Y X := by
  obtain ⟨r, hr, e⟩ := h
  obtain ⟨u, hu⟩ := hr.exists_right_inv
  refine ⟨u, ⟨⟨u, r, by rw [mul_comm]; exact hu, hu⟩, rfl⟩, ?_⟩
  rw [e]; linear_combination (-(X.det * (r * u + 1))) * hu

/-- Cancel a unit-square factor: if $a_2b_2 = r^2a_1b_1$, $a_2 = q^2a_1$ and $a_1 \ne 0$ then $b_2 = r'^2 b_1$. -/
theorem unit_sq_cancel {a₁ a₂ b₁ b₂ r q : R} (hr : IsUnit r) (hq : IsUnit q) (h : a₂ * b₂ = r ^ 2 * (a₁ * b₁))
    (h' : a₂ = q ^ 2 * a₁) (ha : a₁ ≠ 0) : ∃ r' : R, IsUnit r' ∧ b₂ = r' ^ 2 * b₁ := by
  obtain ⟨u, hu⟩ := hq.exists_right_inv
  refine ⟨r * u, hr.mul ⟨⟨u, q, by rw [mul_comm]; exact hu, hu⟩, rfl⟩, mul_left_cancel₀ ha ?_⟩
  rw [h'] at h
  linear_combination u ^ 2 * h - (a₁ * b₂ * (q * u + 1)) * hu

/-- `DetRel` of orthogonal sums and of the first blocks gives `DetRel` of the second blocks. -/
theorem DetRel.compl {K₁ K₂ : Matrix κ κ R} {N₁ N₂ : Matrix ι ι R}
    (h : DetRel (Matrix.fromBlocks K₁ 0 0 N₁) (Matrix.fromBlocks K₂ 0 0 N₂)) (hK : DetRel K₁ K₂)
    (h0 : K₁.det ≠ 0) : DetRel N₁ N₂ := by
  obtain ⟨r, hr, e⟩ := h
  obtain ⟨q, hq, e'⟩ := hK
  rw [det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁] at e
  exact unit_sq_cancel hr hq e e' h0

/-- `DetRel` of orthogonal sums and of the second blocks gives `DetRel` of the first blocks. -/
theorem DetRel.first {K₁ K₂ : Matrix κ κ R} {N₁ N₂ : Matrix ι ι R}
    (h : DetRel (Matrix.fromBlocks K₁ 0 0 N₁) (Matrix.fromBlocks K₂ 0 0 N₂)) (hN : DetRel N₁ N₂)
    (h0 : N₁.det ≠ 0) : DetRel K₁ K₂ := by
  obtain ⟨r, hr, e⟩ := h
  obtain ⟨q, hq, e'⟩ := hN
  rw [det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁, mul_comm K₂.det, mul_comm K₁.det] at e
  exact unit_sq_cancel hr hq e e' h0

/-- `DetRel` is preserved by reindexing. -/
theorem DetRel.submatrix {X Y : Matrix ι ι R} (h : DetRel X Y) (e : κ ≃ ι) :
    DetRel (X.submatrix e e) (Y.submatrix e e) := by
  simpa [DetRel, det_submatrix_equiv_self] using h

end Reduce

end QuadFormsKB.Siegel.CongrLocal
