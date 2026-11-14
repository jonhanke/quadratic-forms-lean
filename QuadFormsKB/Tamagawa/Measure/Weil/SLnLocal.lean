import QuadFormsKB.Tamagawa.Measure.Weil.SLnAdele

/-!
# A local section of $g\mapsto ge_0$ on $\mathrm{SL}_n(K)$

$K$ a field, $n = k + 2\ge2$, $B\subseteq K$ a "unit ball" (the valuation ring $\mathcal O_v$ at a finite place, the closed
unit ball at an archimedean place). Indices are 0-based: $e_0$ is the first basis vector.

For $z\in K^n$ a **pivot** is an index $i$ with $z_i\ne0$ and $z_j/z_i\in B$ for all $j$ (`PivP`); `piv B z` is the
first pivot (and $0$ if there is none). With the signed swap $Q_i\in\mathrm{SL}_n(\mathbb Z)$ ($Q_iz$ has $z_i$ in
position $0$ and $-z_0$ in position $i$; `qMat`, a product of three transvections) and the lower triangular
$$L(w) = \begin{pmatrix} w_0 & & & \\ w_1 & w_0^{-1} & & \\ w_2 & 0 & 1 & \\ \vdots & & & \ddots\end{pmatrix},$$
the local section is
$$ s_B(z) = Q_i^{-1}\,L(Q_iz),\qquad i = \texttt{piv}\,B\,z\qquad(\texttt{secM}).$$
* `secM_col`: the first column of $s_B(z)$ is $z$ (always);
* `det_secM`: $\det s_B(z) = 1$ when $z$ has a pivot;
* `secM_mem`: if $B = \mathcal O$ is a subring, $z\in\mathcal O^n$ and $z_i^{-1}\in\mathcal O$ at the pivot, then
  $s_B(z)\in M_n(\mathcal O)$; for $\mathcal O$ a valuation ring and $z$ **primitive** (`IsPrimN`: integral with a unit
  coordinate) this holds (`inv_piv_mem`), and every nonzero $z$ has a pivot (`exists_pivP_valuationSubring`,
  `exists_pivP_norm`);
* `isPrimN_col`: the first column of a matrix in $M_n(\mathcal O)$ of determinant $1$ is primitive.
-/

open Matrix
open scoped Classical

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil.SLn

noncomputable section

/-! ### Transvections -/

section Ring

variable {R : Type*} [CommRing R] {k : ℕ}

theorem transvection_mulVec_apply (a b : Fin (k + 2)) (c : R) (z : Fin (k + 2) → R) (r : Fin (k + 2)) :
    (transvection a b c *ᵥ z) r = z r + if r = a then c * z b else 0 := by
  simp only [transvection, add_mulVec, one_mulVec, Pi.add_apply]
  congr 1
  simp only [mulVec, dotProduct, single_apply]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single b]
    · simp
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  · simp [Ne.symm h]

/-- The signed swap $Q_i$: $Q_iz$ has $z_i$ in position $0$ and $-z_0$ in position $i$ (for $i\ne0$; $Q_0 = 1$). -/
def qMat (i : Fin (k + 2)) : Matrix (Fin (k + 2)) (Fin (k + 2)) R :=
  if i = 0 then 1 else transvection 0 i 1 * transvection i 0 (-1) * transvection 0 i 1

/-- The inverse of $Q_i$. -/
def qInv (i : Fin (k + 2)) : Matrix (Fin (k + 2)) (Fin (k + 2)) R :=
  if i = 0 then 1 else transvection 0 i (-1) * transvection i 0 1 * transvection 0 i (-1)

theorem qInv_mul_qMat (i : Fin (k + 2)) : qInv (R := R) i * qMat i = 1 := by
  unfold qInv qMat
  split_ifs with h
  · exact mul_one 1
  · have h1 : (0 : Fin (k + 2)) ≠ i := Ne.symm h
    have e : ∀ (A B C D E G : Matrix (Fin (k + 2)) (Fin (k + 2)) R), A * B * C * (D * E * G) =
        A * B * (C * D) * E * G := by intro A B C D E G; simp only [Matrix.mul_assoc]
    rw [e, transvection_mul_transvection_same _ _ h1, neg_add_cancel, transvection_zero, Matrix.mul_one,
      Matrix.mul_assoc (transvection 0 i (-1)), transvection_mul_transvection_same _ _ h, add_neg_cancel,
      transvection_zero, Matrix.mul_one, transvection_mul_transvection_same _ _ h1, neg_add_cancel,
      transvection_zero]

theorem det_qMat (i : Fin (k + 2)) : (qMat (R := R) i).det = 1 := by
  unfold qMat
  split_ifs with h
  · exact det_one
  · rw [det_mul, det_mul, det_transvection_of_ne _ _ (Ne.symm h), det_transvection_of_ne _ _ h, mul_one, mul_one]

theorem det_qInv (i : Fin (k + 2)) : (qInv (R := R) i).det = 1 := by
  have := congrArg det (qInv_mul_qMat (R := R) i)
  rwa [det_mul, det_qMat, mul_one, det_one] at this

theorem qMat_mulVec_zero (i : Fin (k + 2)) (z : Fin (k + 2) → R) : (qMat i *ᵥ z) 0 = z i := by
  unfold qMat
  split_ifs with h
  · subst h; simp
  · rw [← mulVec_mulVec, ← mulVec_mulVec]
    simp only [transvection_mulVec_apply, if_pos rfl, if_neg (Ne.symm h), if_neg h, add_zero, if_pos]
    ring

/-! ### Integral matrices -/

/-- All entries of `A` lie in the subring `S`. -/
def IsIntMat (S : Subring R) (A : Matrix (Fin (k + 2)) (Fin (k + 2)) R) : Prop := ∀ r c, A r c ∈ S

theorem IsIntMat.mul {S : Subring R} {A B : Matrix (Fin (k + 2)) (Fin (k + 2)) R} (hA : IsIntMat S A)
    (hB : IsIntMat S B) : IsIntMat S (A * B) := fun r c => by
  rw [mul_apply]; exact Subring.sum_mem _ fun s _ => mul_mem (hA r s) (hB s c)

theorem isIntMat_one (S : Subring R) : IsIntMat S (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) R) := fun r c => by
  rw [one_apply]; split_ifs
  · exact one_mem S
  · exact zero_mem S

theorem isIntMat_transvection (S : Subring R) (a b : Fin (k + 2)) {c : R} (hc : c ∈ S) :
    IsIntMat S (transvection a b c) := fun r s => by
  simp only [transvection, Matrix.add_apply]
  refine add_mem (isIntMat_one S r s) ?_
  rw [Matrix.single_apply]
  split_ifs
  · exact hc
  · exact zero_mem S

theorem isIntMat_qMat (S : Subring R) (i : Fin (k + 2)) : IsIntMat S (qMat i) := by
  unfold qMat; split_ifs
  · exact isIntMat_one S
  · exact ((isIntMat_transvection S _ _ (one_mem S)).mul (isIntMat_transvection S _ _ (neg_mem (one_mem S)))).mul
      (isIntMat_transvection S _ _ (one_mem S))

theorem isIntMat_qInv (S : Subring R) (i : Fin (k + 2)) : IsIntMat S (qInv i) := by
  unfold qInv; split_ifs
  · exact isIntMat_one S
  · exact ((isIntMat_transvection S _ _ (neg_mem (one_mem S))).mul (isIntMat_transvection S _ _ (one_mem S))).mul
      (isIntMat_transvection S _ _ (neg_mem (one_mem S)))

theorem qMat_mulVec_mem {S : Subring R} (i : Fin (k + 2)) {z : Fin (k + 2) → R} (hz : ∀ j, z j ∈ S) (r) :
    (qMat i *ᵥ z) r ∈ S := by
  show (∑ s, qMat i r s * z s) ∈ S
  exact Subring.sum_mem _ fun s _ => mul_mem (isIntMat_qMat S i r s) (hz s)

end Ring

/-! ### Pivots and the local section -/

section Field

variable {K : Type*} [Field K] {k : ℕ}

/-- `i` is a pivot of `z` relative to the unit ball `B`: $z_i\ne0$ and $z_j/z_i\in B$ for all $j$. -/
def PivP (B : Set K) (z : Fin (k + 2) → K) (i : Fin (k + 2)) : Prop := z i ≠ 0 ∧ ∀ j, z j * (z i)⁻¹ ∈ B

/-- The first pivot of `z` (`0` if there is none). -/
def piv (B : Set K) (z : Fin (k + 2) → K) : Fin (k + 2) :=
  if h : ∃ i, PivP B z i then Fin.find (PivP B z) h else 0

theorem pivP_piv {B : Set K} {z : Fin (k + 2) → K} (h : ∃ i, PivP B z i) : PivP B z (piv B z) := by
  rw [piv, dite_eq_left h]; exact Fin.find_spec h

theorem piv_eq_iff (B : Set K) (z : Fin (k + 2) → K) (i : Fin (k + 2)) :
    piv B z = i ↔ ((∃ i, PivP B z i) ∧ PivP B z i ∧ ∀ j < i, ¬ PivP B z j) ∨ ((¬ ∃ i, PivP B z i) ∧ i = 0) := by
  unfold piv
  by_cases h : ∃ i, PivP B z i
  · rw [dite_eq_left h, Fin.find_eq_iff]
    simp [h]
  · rw [dite_eq_right h]
    simp [h, eq_comm]

/-- The lower triangular matrix $L(w)$: first column $w$, then $w_0^{-1}$ at $(1,1)$, and $1$ further down the diagonal. -/
def lowM (w : Fin (k + 2) → K) : Matrix (Fin (k + 2)) (Fin (k + 2)) K :=
  Matrix.of fun r c => if c = 0 then w r else if r = c then (if c = 1 then (w 0)⁻¹ else 1) else 0

theorem det_lowM {w : Fin (k + 2) → K} (hw : w 0 ≠ 0) : (lowM w).det = 1 := by
  have hlow : (lowM w).BlockTriangular OrderDual.toDual := by
    intro r c hrc
    have hrc' : r < c := hrc
    have hc0 : c ≠ 0 := Fin.pos_iff_ne_zero.mp (lt_of_le_of_lt (Fin.zero_le r) hrc')
    simp [lowM, hc0, hrc'.ne]
  rw [det_of_lowerTriangular _ hlow, Fin.prod_univ_succ, Fin.prod_univ_succ]
  have hrest : ∀ j : Fin k, lowM w j.succ.succ j.succ.succ = 1 := by
    intro j
    simp only [lowM, of_apply, if_neg (Fin.succ_ne_zero _), if_true]
    rw [if_neg]
    intro h
    have := congrArg Fin.val h
    simp at this
  simp only [hrest, Finset.prod_const_one, mul_one]
  simp [lowM, mul_inv_cancel₀ hw]

/-- **The local section** $s_B(z) = Q_i^{-1}L(Q_iz)$, $i$ the first pivot. -/
def secM (B : Set K) (z : Fin (k + 2) → K) : Matrix (Fin (k + 2)) (Fin (k + 2)) K :=
  qInv (piv B z) * lowM (qMat (piv B z) *ᵥ z)

/-- The first column of $s_B(z)$ is $z$. -/
theorem secM_col (B : Set K) (z : Fin (k + 2) → K) (r : Fin (k + 2)) : secM B z r 0 = z r := by
  have : (fun s => lowM (qMat (piv B z) *ᵥ z) s 0) = qMat (piv B z) *ᵥ z := by
    funext s; simp [lowM]
  calc secM B z r 0 = (qInv (piv B z) *ᵥ (fun s => lowM (qMat (piv B z) *ᵥ z) s 0)) r := by
        simp [secM, mul_apply, mulVec, dotProduct]
    _ = z r := by rw [this, mulVec_mulVec, qInv_mul_qMat, one_mulVec]

theorem det_secM {B : Set K} {z : Fin (k + 2) → K} (h : ∃ i, PivP B z i) : (secM B z).det = 1 := by
  rw [secM, det_mul, det_qInv, one_mul]
  refine det_lowM ?_
  rw [qMat_mulVec_zero]
  exact (pivP_piv h).1

/-- Integrality of the section. -/
theorem secM_mem {O : Subring K} {z : Fin (k + 2) → K} (hz : ∀ j, z j ∈ O) (hinv : (z (piv O z))⁻¹ ∈ O) :
    IsIntMat O (secM (O : Set K) z) := by
  refine (isIntMat_qInv O _).mul fun r c => ?_
  simp only [lowM, of_apply]
  split_ifs
  · exact qMat_mulVec_mem _ hz r
  · rw [qMat_mulVec_zero]; exact hinv
  · exact one_mem O
  · exact zero_mem O

/-- **Primitive** vectors of $\mathcal O^n$: integral, with a coordinate whose inverse is integral. -/
def IsPrimN (O : Subring K) (z : Fin (k + 2) → K) : Prop := (∀ j, z j ∈ O) ∧ ∃ j, z j ≠ 0 ∧ (z j)⁻¹ ∈ O

theorem inv_mem_of_pivP {O : Subring K} {z : Fin (k + 2) → K} (hz : IsPrimN O z) {i : Fin (k + 2)}
    (hi : PivP (O : Set K) z i) : (z i)⁻¹ ∈ O := by
  obtain ⟨-, j, hj0, hj⟩ := hz
  have : (z i)⁻¹ = z j * (z i)⁻¹ * (z j)⁻¹ := by field_simp
  rw [this]
  exact mul_mem (hi.2 j) hj

/-- A pivot exists for every nonzero vector, relative to a valuation subring. -/
theorem exists_pivP_valuationSubring (O : ValuationSubring K) {z : Fin (k + 2) → K} (hz : z ≠ 0) :
    ∃ i, PivP (O.toSubring : Set K) z i := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => O.valuation (z j)) Finset.univ_nonempty
  have hi0 : z i ≠ 0 := by
    intro h0
    apply hz
    funext j
    have := hi j (Finset.mem_univ j)
    rw [h0, map_zero] at this
    simpa using (le_zero_iff.mp this)
  refine ⟨i, hi0, fun j => ?_⟩
  show z j * (z i)⁻¹ ∈ O
  rw [← O.valuation_le_one_iff, map_mul, map_inv₀]
  have hpos : O.valuation (z i) ≠ 0 := by simpa using hi0
  rw [mul_inv_le_iff₀ (zero_lt_iff.mpr hpos), one_mul]
  exact hi j (Finset.mem_univ j)

/-- A pivot exists for every nonzero vector, relative to the closed unit ball of a normed field. -/
theorem exists_pivP_norm {L : Type*} [NormedField L] {z : Fin (k + 2) → L} (hz : z ≠ 0) :
    ∃ i, PivP (Metric.closedBall (0 : L) 1) z i := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖z j‖) Finset.univ_nonempty
  have hi0 : z i ≠ 0 := by
    intro h0
    apply hz
    funext j
    have := hi j (Finset.mem_univ j)
    rw [h0, norm_zero] at this
    simpa using (norm_le_zero_iff.mp this)
  refine ⟨i, hi0, fun j => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right, norm_mul, norm_inv]
  rw [mul_inv_le_iff₀ (norm_pos_iff.mpr hi0), one_mul]
  exact hi j (Finset.mem_univ j)

theorem inv_piv_mem (O : ValuationSubring K) {z : Fin (k + 2) → K} (hz : IsPrimN O.toSubring z) :
    (z (piv (O.toSubring : Set K) z))⁻¹ ∈ O.toSubring := by
  have hne : z ≠ 0 := by
    obtain ⟨-, j, hj, -⟩ := hz
    intro h; exact hj (by rw [h]; rfl)
  exact inv_mem_of_pivP hz (pivP_piv (exists_pivP_valuationSubring O hne))

/-- A matrix whose entries lie in a subring has its determinant in that subring. -/
theorem det_mem_of_isIntMat' {n : Type*} [Fintype n] [DecidableEq n] (S : Subring K) (A : Matrix n n K)
    (hA : ∀ r c, A r c ∈ S) : A.det ∈ S := by
  set A' : Matrix n n S := Matrix.of fun r c => ⟨A r c, hA r c⟩
  have : A = A'.map S.subtype := by ext r c; rfl
  rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (A'.det).2

/-- **The first column of an integral matrix of determinant $1$ is primitive** (valuation ring). -/
theorem isPrimN_col (O : ValuationSubring K) {g : Matrix (Fin (k + 2)) (Fin (k + 2)) K}
    (hg : ∀ r c, g r c ∈ O) (hdet : g.det = 1) : IsPrimN O.toSubring (fun r => g r 0) := by
  refine ⟨fun j => hg j 0, ?_⟩
  by_contra hno
  push Not at hno
  -- every entry of the first column has valuation `< 1`
  have hlt : ∀ r, O.valuation (g r 0) < 1 := by
    intro r
    have hle : O.valuation (g r 0) ≤ 1 := (O.valuation_le_one_iff _).mpr (hg r 0)
    rcases eq_or_ne (g r 0) 0 with h0 | h0
    · rw [h0, map_zero]; exact zero_lt_one
    · refine lt_of_le_of_ne hle fun h1 => hno r h0 ?_
      show (g r 0)⁻¹ ∈ O
      rw [← O.valuation_le_one_iff, map_inv₀, h1, inv_one]
  have hterm : ∀ r : Fin (k + 2), O.valuation ((-1) ^ (r : ℕ) * g r 0 *
      (g.submatrix r.succAbove Fin.succ).det) < 1 := by
    intro r
    have hd : O.valuation (g.submatrix r.succAbove Fin.succ).det ≤ 1 :=
      (O.valuation_le_one_iff _).mpr
        (det_mem_of_isIntMat' O.toSubring _ fun a b => hg (r.succAbove a) (Fin.succ b))
    rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, Valuation.map_neg, Valuation.map_one, one_pow,
      one_mul]
    calc O.valuation (g r 0) * O.valuation (g.submatrix r.succAbove Fin.succ).det
        ≤ O.valuation (g r 0) * 1 := by gcongr
      _ = O.valuation (g r 0) := mul_one _
      _ < 1 := hlt r
  have hsum := Valuation.map_sum_lt O.valuation (s := Finset.univ) one_ne_zero fun r _ => hterm r
  rw [← det_succ_column_zero, hdet, map_one] at hsum
  exact lt_irrefl _ hsum

end Field

end

end QuadFormsKB.Tamagawa.Measure.Weil.SLn
