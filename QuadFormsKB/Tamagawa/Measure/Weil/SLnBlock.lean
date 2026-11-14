import QuadFormsKB.Tamagawa.Measure.Weil.SLnLocal

/-!
# The stabilizer of $e_0$ in $\mathrm{SL}_n$: block matrices

$R$ a commutative ring, $n = k + 2$. For $h\in M_{n-1}(R)$ and a row $c\in R^{n-1}$,
$$\operatorname{blk}(h, c) = \begin{pmatrix}1 & c\\ 0 & h\end{pmatrix}\qquad(\texttt{blkM}),$$
with $\det\operatorname{blk}(h,c) = \det h$ (`det_blkM`) and
$\operatorname{blk}(h,c)\operatorname{blk}(h',c') = \operatorname{blk}(hh',\ c' + ch')$ (`blkM_mul`). A matrix $g$ with
$ge_0 = e_0$ is $\operatorname{blk}(\text{lower block},\ \text{top row})$ (`eq_blkM`): the stabilizer of $e_0$ in
$\mathrm{SL}_n$ is $\mathbb G_a^{n-1}\rtimes\mathrm{SL}_{n-1}$. Also the full formula for the signed swap $Q_i$
(`qMat_mulVec`), so that $Q_i^{-1}e_0 = e_i$.
-/

open Matrix
open scoped Classical

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil.SLn

noncomputable section

variable {R : Type*} [CommRing R] {k : ℕ}

/-- The block matrix $\begin{pmatrix}1 & c\\ 0 & h\end{pmatrix}$. -/
def blkM (h : Matrix (Fin (k + 1)) (Fin (k + 1)) R) (c : Fin (k + 1) → R) : Matrix (Fin (k + 2)) (Fin (k + 2)) R :=
  Fin.cons (Fin.cons 1 c) (fun r => Fin.cons 0 (h r))

@[simp] theorem blkM_zero_zero (h : Matrix (Fin (k + 1)) (Fin (k + 1)) R) (c : Fin (k + 1) → R) :
    blkM h c 0 0 = 1 := rfl
@[simp] theorem blkM_zero_succ (h : Matrix (Fin (k + 1)) (Fin (k + 1)) R) (c : Fin (k + 1) → R) (s : Fin (k + 1)) :
    blkM h c 0 s.succ = c s := rfl
@[simp] theorem blkM_succ_zero (h : Matrix (Fin (k + 1)) (Fin (k + 1)) R) (c : Fin (k + 1) → R) (r : Fin (k + 1)) :
    blkM h c r.succ 0 = 0 := rfl
@[simp] theorem blkM_succ_succ (h : Matrix (Fin (k + 1)) (Fin (k + 1)) R) (c : Fin (k + 1) → R)
    (r s : Fin (k + 1)) : blkM h c r.succ s.succ = h r s := rfl

theorem det_blkM (h : Matrix (Fin (k + 1)) (Fin (k + 1)) R) (c : Fin (k + 1) → R) : (blkM h c).det = h.det := by
  rw [det_succ_column_zero, Fin.sum_univ_succ]
  simp only [blkM_zero_zero, blkM_succ_zero, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
    Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
  rfl

theorem blkM_mul (h h' : Matrix (Fin (k + 1)) (Fin (k + 1)) R) (c c' : Fin (k + 1) → R) :
    blkM h c * blkM h' c' = blkM (h * h') (c' + vecMul c h') := by
  ext r s
  refine Fin.cases ?_ (fun r => ?_) r <;> refine Fin.cases ?_ (fun s => ?_) s <;>
    simp [mul_apply, Fin.sum_univ_succ, vecMul, dotProduct, add_comm]

theorem blkM_mulVec_single (h : Matrix (Fin (k + 1)) (Fin (k + 1)) R) (c : Fin (k + 1) → R) :
    blkM h c *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  ext r
  rw [mulVec_single_one]
  refine Fin.cases ?_ (fun r => ?_) r <;> simp

/-- The lower block of a matrix. -/
def lowBlk (g : Matrix (Fin (k + 2)) (Fin (k + 2)) R) : Matrix (Fin (k + 1)) (Fin (k + 1)) R :=
  fun r s => g r.succ s.succ

/-- The top row (without the corner) of a matrix. -/
def topRow (g : Matrix (Fin (k + 2)) (Fin (k + 2)) R) : Fin (k + 1) → R := fun s => g 0 s.succ

theorem eq_blkM {g : Matrix (Fin (k + 2)) (Fin (k + 2)) R} (hg : g *ᵥ Pi.single 0 1 = Pi.single 0 1) :
    g = blkM (lowBlk g) (topRow g) := by
  have hcol : ∀ r, g r 0 = (Pi.single 0 1 : Fin (k + 2) → R) r := fun r => by
    rw [← hg, mulVec_single_one]; rfl
  ext r s
  refine Fin.cases ?_ (fun r => ?_) r <;> refine Fin.cases ?_ (fun s => ?_) s
  · simpa using hcol 0
  · rfl
  · simpa using hcol r.succ
  · rfl

theorem det_lowBlk {g : Matrix (Fin (k + 2)) (Fin (k + 2)) R} (hg : g *ᵥ Pi.single 0 1 = Pi.single 0 1) :
    (lowBlk g).det = g.det := by
  conv_rhs => rw [eq_blkM hg]
  rw [det_blkM]

theorem blkM_map {S : Type*} [CommRing S] (f : R →+* S) (h : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
    (c : Fin (k + 1) → R) : (blkM h c).map f = blkM (h.map f) (f ∘ c) := by
  ext r s
  refine Fin.cases ?_ (fun r => ?_) r <;> refine Fin.cases ?_ (fun s => ?_) s <;> simp

/-- The block matrix as an element of $\mathrm{SL}_n(R)$. -/
def blk (h : SpecialLinearGroup (Fin (k + 1)) R) (c : Fin (k + 1) → R) : SpecialLinearGroup (Fin (k + 2)) R :=
  ⟨blkM h c, by rw [det_blkM, h.2]⟩

theorem blk_mul (h h' : SpecialLinearGroup (Fin (k + 1)) R) (c c' : Fin (k + 1) → R) :
    blk h c * blk h' c' = blk (h * h') (c' + vecMul c h') :=
  Subtype.ext (blkM_mul _ _ _ _)

/-- The lower block of an element of $\mathrm{SL}_n(R)$ fixing $e_0$. -/
def lowBlkSL (g : SpecialLinearGroup (Fin (k + 2)) R)
    (hg : (g : Matrix (Fin (k + 2)) (Fin (k + 2)) R) *ᵥ Pi.single 0 1 = Pi.single 0 1) :
    SpecialLinearGroup (Fin (k + 1)) R :=
  ⟨lowBlk g, by rw [det_lowBlk hg, g.2]⟩

theorem eq_blk (g : SpecialLinearGroup (Fin (k + 2)) R)
    (hg : (g : Matrix (Fin (k + 2)) (Fin (k + 2)) R) *ᵥ Pi.single 0 1 = Pi.single 0 1) :
    g = blk (lowBlkSL g hg) (topRow g) :=
  Subtype.ext (eq_blkM hg)

/-! ### The signed swap, fully -/

theorem qMat_mulVec (i : Fin (k + 2)) (hi : i ≠ 0) (z : Fin (k + 2) → R) (r : Fin (k + 2)) :
    (qMat i *ᵥ z) r = if r = 0 then z i else if r = i then -z 0 else z r := by
  unfold qMat
  rw [if_neg hi, ← mulVec_mulVec, ← mulVec_mulVec]
  simp only [transvection_mulVec_apply]
  by_cases h0 : r = 0
  · subst h0; simp [Ne.symm hi, hi]
  · by_cases hri : r = i
    · subst hri; simp [hi]
    · simp [h0, hri]

/-- $Q_ie_i = e_0$. -/
theorem qMat_mulVec_single (i : Fin (k + 2)) :
    qMat (R := R) i *ᵥ Pi.single i 1 = Pi.single 0 1 := by
  by_cases hi : i = 0
  · subst hi; rw [qMat, if_pos rfl, one_mulVec]
  ext r
  rw [qMat_mulVec i hi]
  by_cases h0 : r = 0
  · subst h0; simp
  · by_cases hri : r = i
    · subst hri; simp [hi]
    · simp [h0, hri]

/-- $Q_i^{-1}e_0 = e_i$. -/
theorem qInv_mulVec_single (i : Fin (k + 2)) :
    qInv (R := R) i *ᵥ Pi.single 0 1 = Pi.single i 1 := by
  rw [← qMat_mulVec_single i, mulVec_mulVec, qInv_mul_qMat, one_mulVec]

/-- The signed swap as an element of $\mathrm{SL}_n(R)$. -/
def qSL (i : Fin (k + 2)) : SpecialLinearGroup (Fin (k + 2)) R := ⟨qMat i, det_qMat i⟩

/-- $Q_i^{-1}$ as an element of $\mathrm{SL}_n(R)$. -/
def qInvSL (i : Fin (k + 2)) : SpecialLinearGroup (Fin (k + 2)) R := ⟨qInv i, det_qInv i⟩

theorem qSL_mul_qInvSL (i : Fin (k + 2)) : qSL (R := R) i * qInvSL i = 1 := by
  have h : qInvSL (R := R) i * qSL i = 1 := Subtype.ext (qInv_mul_qMat i)
  exact mul_eq_one_iff_eq_inv.mpr (inv_eq_of_mul_eq_one_right h).symm

end

end QuadFormsKB.Tamagawa.Measure.Weil.SLn
