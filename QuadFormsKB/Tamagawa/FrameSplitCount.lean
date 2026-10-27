/-
# The orbit of the standard frame mod $\pi^k$

**Layer:** a complete DVR $R$ with uniformizer $\pi$ and finite residue field of size $q$ (every residue characteristic, dyadic
included).

For $Q = T\perp Q'$ (`blockForm`, ranks $r$ and $n'$) and the standard frame $E$, Weil's fibration $O(V) \to \{\text{frames of } T\}$,
$g \mapsto gE$, has fibre $O(Q')$ up to the Jacobian $|\det H_T|^{-n'}$. In finite form:
$$N_{k,s}(KE)\cdot q^{d n'}\cdot|O(Q'\bmod\pi^k)| = |O(Q\bmod\pi^k)|\qquad(\pi^d\,\Vert\,\det H_T,\ k \gg s \gg 0),$$
$K$ the integral isometries of $Q$ (`frameNear_stdFrame`). This is the frame version of `repCountForm_splitForm_orbit`
and
`card_orbitSet_eq_nearCount`.

*Proof.* (1) The near set of $KE$ is the orbit $O(Q\bmod\pi^k)\,\bar E$: an isometry mod $\pi^k$ is $\equiv$ an exact integral isometry
mod $\pi^{k - d_Q}$ (`exists_compMat_eq_of_dvd`); conversely a frame $z$ near $KE$ is, after Hensel (`exists_formF_eq_of_dvd`) and
openness (`exists_frame_openMat`), $M(E + \pi^{k-d}w)$ with $M$ an integral isometry, and
$g = \begin{pmatrix}1 + \pi^{k-d}A & B\\ \pi^{k-d}C & 1\end{pmatrix}$, $B = -\pi^{k-d}H_T^{-1}C^{\mathsf T}H_{Q'}$ (integral for $k \ge 2d$), is an
isometry mod $\pi^k$ for $k \ge 4d$ with $gE = E + \pi^{k-d}w$. (2) The stabilizer of $\bar E$ in $O(Q\bmod\pi^k)$ is
$\{\begin{pmatrix}1 & S\\ 0 & Y\end{pmatrix} : H_TS \equiv 0,\ Y \in O(Q'\bmod\pi^k)\}$ (for $k \ge 2d$ the term $T\circ S$ vanishes mod
$\pi^k$), of order $|\ker(H_T\bmod\pi^k)|^{n'}\,|O(Q'\bmod\pi^k)| = q^{dn'}|O(Q'\bmod\pi^k)|$. (3) Orbit–stabilizer.

Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.FrameOpen
import QuadFormsKB.Tamagawa.BlockForm

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Frames

open QuadForm LocalDensity LocalDensity.DVR QuadFormsKB.Tamagawa

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n r n' : ℕ}

/-! ### The group of integral isometries -/

/-- **The integral isometries** $\{g \in \mathrm{GL}_n(R) : Q\circ g = Q\}$. -/
def isomGL (Q : QuadForm R n) : Subgroup (GL (Fin n) R) where
  carrier := {g | Q.compMat g.val = Q}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Units.val_mul] at *
    rw [← compMat_mul, ha, hb]
  one_mem' := by simp [compMat_one]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [compMat_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, compMat_one]

/-- The integral isometries acting on frames by left multiplication. -/
def frameRep (Q : QuadForm R n) (r : ℕ) : isomGL Q →* Matrix (Fin n × Fin r) (Fin n × Fin r) R :=
  (frameHom r R).comp ((Units.coeHom (Matrix (Fin n) (Fin n) R)).comp (isomGL Q).subtype)

theorem frameRep_apply (Q : QuadForm R n) (κ : isomGL Q) : frameRep Q r κ = frameMat r (κ : GL (Fin n) R).val := rfl

theorem compMat_frameRep (Q : QuadForm R n) (κ : isomGL Q) : Q.compMat (κ : GL (Fin n) R).val = Q := κ.2

/-- An integral matrix $X$ with $Q\circ X = Q$, $Q$ nondegenerate, is invertible (its determinant squares to $1$). -/
theorem isUnit_det_of_compMat_eq_self {Q : QuadForm R n} (hQ : Q.Nondegenerate) {X : Matrix (Fin n) (Fin n) R}
    (hX : Q.compMat X = Q) : IsUnit X.det := by
  have h1 := congrArg QuadForm.hessian hX
  rw [hessian_compMat] at h1
  have h2 := congrArg Matrix.det h1
  rw [det_mul, det_mul, det_transpose] at h2
  have h3 : (X.det * X.det - 1) * Q.hessian.det = 0 := by linear_combination h2
  rcases mul_eq_zero.mp h3 with h | h
  · exact IsUnit.of_mul_eq_one X.det (by linear_combination h)
  · exact absurd h hQ

/-- An integral isometry as an element of `isomGL`. -/
def isomOf {Q : QuadForm R n} (hQ : Q.Nondegenerate) (X : Matrix (Fin n) (Fin n) R) (hX : Q.compMat X = Q) : isomGL Q :=
  ⟨Matrix.GeneralLinearGroup.mk'' X (isUnit_det_of_compMat_eq_self hQ hX), hX⟩

theorem isomOf_val {Q : QuadForm R n} (hQ : Q.Nondegenerate) (X : Matrix (Fin n) (Fin n) R) (hX : Q.compMat X = Q) :
    ((isomOf hQ X hX : isomGL Q) : GL (Fin n) R).val = X := rfl

/-! ### Block matrices over a commutative ring: the isometries of $T \perp Q'$ near $1$ -/

section BlockAlg

variable {A : Type*} [CommRing A]

theorem blockMat_mulVec_castAdd (P : Matrix (Fin r) (Fin r) A) (B : Matrix (Fin r) (Fin n') A)
    (C : Matrix (Fin n') (Fin r) A) (D : Matrix (Fin n') (Fin n') A) (x : Fin (r + n') → A) (i : Fin r) :
    (blockMat P B C D *ᵥ x) (Fin.castAdd n' i) =
      (P *ᵥ fun j => x (Fin.castAdd n' j)) i + (B *ᵥ fun j => x (Fin.natAdd r j)) i := by
  simp [mulVec, dotProduct, Fin.sum_univ_add]

theorem blockMat_mulVec_natAdd (P : Matrix (Fin r) (Fin r) A) (B : Matrix (Fin r) (Fin n') A)
    (C : Matrix (Fin n') (Fin r) A) (D : Matrix (Fin n') (Fin n') A) (x : Fin (r + n') → A) (i : Fin n') :
    (blockMat P B C D *ᵥ x) (Fin.natAdd r i) =
      (C *ᵥ fun j => x (Fin.castAdd n' j)) i + (D *ᵥ fun j => x (Fin.natAdd r j)) i := by
  simp [mulVec, dotProduct, Fin.sum_univ_add]

/-- **The isometries near $1$ of $T \perp Q'$** (abstract form of the explicit element of $O(Q \bmod \pi^k)$ moving $E$ to $E + aw$):
$g = \begin{pmatrix}1 + aA & B\\ aC & 1\end{pmatrix}$ is an isometry of $T\perp Q'$ if
$T(x + aAx) + Q'(aCx) = T(x)$, $H_TB + aC^{\mathsf T}H_{Q'} = 0$, $a^2 = 0$, $T(Bx) = 0$ for all $x$. -/
theorem compMat_blockMat_near_one (T : QuadForm A r) (Q' : QuadForm A n') (a : A)
    (A' : Matrix (Fin r) (Fin r) A) (B : Matrix (Fin r) (Fin n') A) (C : Matrix (Fin n') (Fin r) A)
    (h1 : ∀ x : Fin r → A, T.eval (x + a • (A' *ᵥ x)) + Q'.eval (a • (C *ᵥ x)) = T.eval x)
    (h2 : T.hessian * B + a • (Cᵀ * Q'.hessian) = 0) (h3 : a * a = 0)
    (h5 : ∀ x : Fin n' → A, T.eval (B *ᵥ x) = 0) :
    (blockForm T Q').compMat (blockMat (1 + a • A') B (a • C) 1) = blockForm T Q' := by
  refine eq_of_eval_eq fun x => ?_
  rw [eval_compMat]
  set x₁ : Fin r → A := fun j => x (Fin.castAdd n' j) with hx₁
  set x₂ : Fin n' → A := fun j => x (Fin.natAdd r j) with hx₂
  have e1 : (fun j => (blockMat (1 + a • A') B (a • C) 1 *ᵥ x) (Fin.castAdd n' j)) =
      (x₁ + a • (A' *ᵥ x₁)) + B *ᵥ x₂ := by
    funext i
    rw [blockMat_mulVec_castAdd, add_mulVec, one_mulVec, smul_mulVec]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_assoc]
    rfl
  have e2 : (fun j => (blockMat (1 + a • A') B (a • C) 1 *ᵥ x) (Fin.natAdd r j)) =
      a • (C *ᵥ x₁) + x₂ := by
    funext i
    rw [blockMat_mulVec_natAdd, one_mulVec, smul_mulVec]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  have hev : ∀ y : Fin (r + n') → A, (blockForm T Q').eval y =
      T.eval (fun j => y (Fin.castAdd n' j)) + Q'.eval (fun j => y (Fin.natAdd r j)) :=
    fun y => evalIn_blockForm A T Q' y
  rw [hev, hev, e1, e2]
  -- the algebra
  have hB : ∀ y : Fin r → A, y ⬝ᵥ (T.hessian *ᵥ (B *ᵥ x₂)) = -(a * ((C *ᵥ y) ⬝ᵥ (Q'.hessian *ᵥ x₂))) := by
    intro y
    have h2' := congrArg (fun M => M *ᵥ x₂) h2
    simp only [add_mulVec, smul_mulVec, zero_mulVec, ← mulVec_mulVec] at h2'
    have h2'' : T.hessian *ᵥ (B *ᵥ x₂) = -(a • (Cᵀ *ᵥ (Q'.hessian *ᵥ x₂))) :=
      eq_neg_of_add_eq_zero_left h2'
    rw [h2'', dotProduct_neg, dotProduct_smul, Matrix.dotProduct_mulVec, vecMul_transpose, smul_eq_mul]
  have hu := eval_polar T (x₁ + a • (A' *ᵥ x₁)) (B *ᵥ x₂)
  have hv := eval_polar Q' (a • (C *ᵥ x₁)) x₂
  have hw : (a • (A' *ᵥ x₁)) ⬝ᵥ (T.hessian *ᵥ (B *ᵥ x₂)) = 0 := by
    rw [smul_dotProduct, hB, smul_eq_mul]
    linear_combination (-( (C *ᵥ (A' *ᵥ x₁)) ⬝ᵥ (Q'.hessian *ᵥ x₂))) * h3
  rw [add_dotProduct, hB, hw, h5] at hu
  rw [smul_dotProduct, smul_eq_mul] at hv
  have := h1 x₁
  linear_combination hu + hv + this

/-- The standard frame matrix over `A` (explicit type, for elaboration). -/
abbrev Efr (A : Type*) [CommRing A] (r n' : ℕ) : Matrix (Fin (r + n')) (Fin r) A := stdFrameMat

theorem mul_Efr_apply (X : Matrix (Fin (r + n')) (Fin (r + n')) A) (i : Fin (r + n')) (j : Fin r) :
    (X * Efr A r n') i j = X i (Fin.castAdd n' j) := by
  simp [Matrix.mul_apply, Efr, stdFrameMat]

theorem Efr_castAdd (i j : Fin r) : Efr A r n' (Fin.castAdd n' i) j = (1 : Matrix (Fin r) (Fin r) A) i j := by
  simp [Efr, stdFrameMat, Matrix.one_apply, Fin.castAdd_inj]

theorem Efr_natAdd (i : Fin n') (j : Fin r) : Efr A r n' (Fin.natAdd r i) j = 0 := by
  simp only [Efr, stdFrameMat, Matrix.of_apply, ite_eq_right_iff]
  intro h
  have h1 := congrArg Fin.val h
  have h2 := j.isLt
  simp at h1
  omega

theorem blockMat_mul_Efr_castAdd (P : Matrix (Fin r) (Fin r) A) (B : Matrix (Fin r) (Fin n') A)
    (C : Matrix (Fin n') (Fin r) A) (D : Matrix (Fin n') (Fin n') A) (i j : Fin r) :
    (blockMat P B C D * Efr A r n') (Fin.castAdd n' i) j = P i j := by
  rw [mul_Efr_apply, blockMat_castAdd_castAdd]

theorem blockMat_mul_Efr_natAdd (P : Matrix (Fin r) (Fin r) A) (B : Matrix (Fin r) (Fin n') A)
    (C : Matrix (Fin n') (Fin r) A) (D : Matrix (Fin n') (Fin n') A) (i : Fin n') (j : Fin r) :
    (blockMat P B C D * Efr A r n') (Fin.natAdd r i) j = C i j := by
  rw [mul_Efr_apply, blockMat_natAdd_castAdd]

/-- A matrix fixing the standard frame is $\begin{pmatrix}1 & S\\ 0 & Y\end{pmatrix}$. -/
theorem eq_blockMat_of_mul_Efr {X : Matrix (Fin (r + n')) (Fin (r + n')) A}
    (hX : X * Efr A r n' = Efr A r n') :
    X = blockMat 1 (Matrix.of fun i j => X (Fin.castAdd n' i) (Fin.natAdd r j)) 0
      (Matrix.of fun i j => X (Fin.natAdd r i) (Fin.natAdd r j)) := by
  have hcol : ∀ i j, X i (Fin.castAdd n' j) = Efr A r n' i j := by
    intro i j
    have := mul_Efr_apply X i j
    rw [hX] at this
    exact this.symm
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [hcol, Efr_castAdd]; simp
  · simp
  · rw [hcol, Efr_natAdd]; simp
  · simp

/-- The upper right block. -/
def blkS (X : Matrix (Fin (r + n')) (Fin (r + n')) A) : Matrix (Fin r) (Fin n') A :=
  Matrix.of fun i j => X (Fin.castAdd n' i) (Fin.natAdd r j)

/-- The lower right block. -/
def blkY (X : Matrix (Fin (r + n')) (Fin (r + n')) A) : Matrix (Fin n') (Fin n') A :=
  Matrix.of fun i j => X (Fin.natAdd r i) (Fin.natAdd r j)

theorem eq_blockMat_of_mul_Efr' {X : Matrix (Fin (r + n')) (Fin (r + n')) A}
    (hX : X * Efr A r n' = Efr A r n') : X = blockMat 1 (blkS X) 0 (blkY X) :=
  eq_blockMat_of_mul_Efr hX

@[simp] theorem blkS_blockMat (P : Matrix (Fin r) (Fin r) A) (S : Matrix (Fin r) (Fin n') A)
    (C : Matrix (Fin n') (Fin r) A) (Y : Matrix (Fin n') (Fin n') A) : blkS (blockMat P S C Y) = S := by
  ext i j; simp [blkS]

@[simp] theorem blkY_blockMat (P : Matrix (Fin r) (Fin r) A) (S : Matrix (Fin r) (Fin n') A)
    (C : Matrix (Fin n') (Fin r) A) (Y : Matrix (Fin n') (Fin n') A) : blkY (blockMat P S C Y) = Y := by
  ext i j; simp [blkY]

theorem blockMat_one_mul_Efr (S : Matrix (Fin r) (Fin n') A) (Y : Matrix (Fin n') (Fin n') A) :
    blockMat 1 S 0 Y * Efr A r n' = Efr A r n' := by
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [blockMat_mul_Efr_castAdd, Efr_castAdd]
  · rw [blockMat_mul_Efr_natAdd, Efr_natAdd]; simp

/-- $T \perp Q'$ composed with $\begin{pmatrix}1 & S\\ 0 & Y\end{pmatrix}$ when $H_TS = 0$ and $T\circ S = 0$. -/
theorem compMat_blockMat_stab (T : QuadForm A r) (Q' : QuadForm A n') (S : Matrix (Fin r) (Fin n') A)
    (Y : Matrix (Fin n') (Fin n') A) (h1 : T.hessian * S = 0) (h2 : ∀ x : Fin n' → A, T.eval (S *ᵥ x) = 0) :
    (blockForm T Q').compMat (blockMat 1 S 0 Y) = blockForm T (Q'.compMat Y) := by
  refine eq_of_eval_eq fun x => ?_
  rw [eval_compMat]
  have hev : ∀ (T : QuadForm A r) (Q' : QuadForm A n') (y : Fin (r + n') → A), (blockForm T Q').eval y =
      T.eval (fun j => y (Fin.castAdd n' j)) + Q'.eval (fun j => y (Fin.natAdd r j)) :=
    fun T Q' y => evalIn_blockForm A T Q' y
  set x₁ : Fin r → A := fun j => x (Fin.castAdd n' j) with hx₁
  set x₂ : Fin n' → A := fun j => x (Fin.natAdd r j) with hx₂
  have e1 : (fun j => (blockMat 1 S 0 Y *ᵥ x) (Fin.castAdd n' j)) = x₁ + S *ᵥ x₂ := by
    funext i
    rw [blockMat_mulVec_castAdd, one_mulVec]
    rfl
  have e2 : (fun j => (blockMat 1 S 0 Y *ᵥ x) (Fin.natAdd r j)) = Y *ᵥ x₂ := by
    funext i
    rw [blockMat_mulVec_natAdd, zero_mulVec]
    simp only [Pi.zero_apply, zero_add]
    rfl
  rw [hev, hev, e1, e2, eval_compMat]
  have hu := eval_polar T x₁ (S *ᵥ x₂)
  have h0 : x₁ ⬝ᵥ (T.hessian *ᵥ (S *ᵥ x₂)) = 0 := by
    rw [mulVec_mulVec, h1, zero_mulVec, dotProduct_zero]
  rw [h0, h2] at hu
  linear_combination hu

/-- If $T\perp Q'$ composed with $\begin{pmatrix}1 & S\\ 0 & Y\end{pmatrix}$ is $T\perp Q'$, then $H_TS = 0$. -/
theorem hessian_mul_eq_zero_of_compMat (T : QuadForm A r) (Q' : QuadForm A n') (S : Matrix (Fin r) (Fin n') A)
    (Y : Matrix (Fin n') (Fin n') A) (h : (blockForm T Q').compMat (blockMat 1 S 0 Y) = blockForm T Q') :
    T.hessian * S = 0 := by
  have hev : ∀ (T : QuadForm A r) (Q' : QuadForm A n') (y : Fin (r + n') → A), (blockForm T Q').eval y =
      T.eval (fun j => y (Fin.castAdd n' j)) + Q'.eval (fun j => y (Fin.natAdd r j)) :=
    fun T Q' y => evalIn_blockForm A T Q' y
  have key : ∀ (x₁ : Fin r → A) (x₂ : Fin n' → A), x₁ ⬝ᵥ (T.hessian *ᵥ (S *ᵥ x₂)) = 0 := by
    intro x₁ x₂
    have hgen : ∀ z₁ : Fin r → A, T.eval (z₁ + S *ᵥ x₂) + Q'.eval (Y *ᵥ x₂) = T.eval z₁ + Q'.eval x₂ := by
      intro z₁
      have e1 : (fun j => (blockMat 1 S 0 Y *ᵥ (Fin.append z₁ x₂ : Fin (r + n') → A))
          (Fin.castAdd n' j)) = z₁ + S *ᵥ x₂ := by
        funext i
        rw [blockMat_mulVec_castAdd, one_mulVec]
        simp
      have e2 : (fun j => (blockMat 1 S 0 Y *ᵥ (Fin.append z₁ x₂ : Fin (r + n') → A))
          (Fin.natAdd r j)) = Y *ᵥ x₂ := by
        funext i
        rw [blockMat_mulVec_natAdd, zero_mulVec]
        simp
      have := congrArg (fun F : QuadForm A (r + n') => F.eval (Fin.append z₁ x₂)) h
      simp only [eval_compMat, hev, e1, e2] at this
      simpa using this
    have hx' := hgen x₁
    have hx0' := hgen 0
    have hu := eval_polar T x₁ (S *ᵥ x₂)
    rw [zero_add] at hx0'
    have h0 : T.eval (0 : Fin r → A) = 0 := by
      simp [QuadForm.eval, QuadForm.evalIn]
    linear_combination -hu + hx' - hx0' - h0
  ext i j
  have h1 := key (Pi.single i 1) (Pi.single j 1)
  rw [single_one_dotProduct, mulVec_mulVec, mulVec_single_one] at h1
  simpa [Matrix.mul_apply, Matrix.col, mulVec_single_one] using h1

theorem blockForm_injective_right {T : QuadForm A r} {Q₁ Q₂ : QuadForm A n'} (h : blockForm T Q₁ = blockForm T Q₂) :
    Q₁ = Q₂ := by
  ext i j
  have := congrArg (fun F : QuadForm A (r + n') => F.coeff (Fin.natAdd r i) (Fin.natAdd r j)) h
  simpa [blockForm_coeff] using this

end BlockAlg

/-! ### The orbit of the standard frame -/

variable [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Finite (IsLocalRing.ResidueField R)]

section Mod

variable {π : R} {k : ℕ}

/-- **$O(Q \bmod \pi^k)$ acts on frames mod $\pi^k$** by left multiplication. -/
instance modFrameAct (Q : QuadForm R n) (π : R) (k : ℕ) :
    MulAction (orthMod Q π k) (Fin n × Fin r → R ⧸ Ideal.span {π ^ k}) where
  smul g x := frameMat r g.val.val *ᵥ x
  one_smul x := by
    show frameMat r ((1 : orthMod Q π k).val.val) *ᵥ x = x
    rw [show ((1 : orthMod Q π k).val.val) = 1 from rfl, frameMat_one, one_mulVec]
  mul_smul g h x := by
    show frameMat r ((g * h).val.val) *ᵥ x = frameMat r g.val.val *ᵥ (frameMat r h.val.val *ᵥ x)
    rw [show ((g * h).val.val) = g.val.val * h.val.val from rfl, frameMat_mul, mulVec_mulVec]

theorem modFrameAct_smul (Q : QuadForm R n) (π : R) (k : ℕ) (g : orthMod Q π k)
    (x : Fin n × Fin r → R ⧸ Ideal.span {π ^ k}) : g • x = frameMat r g.val.val *ᵥ x := rfl

/-- The standard frame reduced mod $\pi^k$. -/
def Ebar (r n' : ℕ) (π : R) (k : ℕ) : Fin (r + n') × Fin r → R ⧸ Ideal.span {π ^ k} :=
  redI π k (stdFrame (A := R) (r := r) (n' := n'))

theorem toMat_Ebar (π : R) (k : ℕ) :
    toMat (Ebar r n' π k) = (Efr (R ⧸ Ideal.span {π ^ k}) r n') := by
  ext l j
  simp only [toMat, Ebar, redI, stdFrame, Matrix.of_apply, Efr, stdFrameMat]
  split_ifs <;> simp

theorem toMat_injective' {A : Type*} {x y : Fin n × Fin r → A} (h : toMat x = toMat y) : x = y := by
  funext ⟨l, j⟩
  exact congrFun (congrFun h l) j

theorem toMat_redI (π : R) (k : ℕ) (x : Fin n × Fin r → R) :
    toMat (redI π k x) = (toMat x).map (Ideal.Quotient.mk (Ideal.span {π ^ k})) := by
  ext l j
  rfl

theorem mk_pow_eq_zero {m : ℕ} (h : k ≤ m) : Ideal.Quotient.mk (Ideal.span {π ^ k}) (π ^ m) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact pow_dvd_pow π h

theorem exists_eq_mul_of_ann (hπ : Irreducible π) {d : ℕ} (hdk : d ≤ k) (s : R ⧸ Ideal.span {π ^ k})
    (hs : Ideal.Quotient.mk (Ideal.span {π ^ k}) (π ^ d) * s = 0) :
    ∃ s₀, s = Ideal.Quotient.mk (Ideal.span {π ^ k}) (π ^ (k - d)) * s₀ := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hs
  have h' : π ^ d * π ^ (k - d) ∣ π ^ d * x := by
    rw [← pow_add, Nat.add_sub_cancel' hdk]; exact hs
  obtain ⟨y, hy⟩ := (mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero)).mp h'
  exact ⟨Ideal.Quotient.mk _ y, by rw [← map_mul, hy]⟩

/-- $\pi^{d+d'} \,\Vert\, \det H_{T\perp Q'}$. -/
theorem det_blockForm_exact (hπ : Irreducible π) (T : QuadForm R r) (Q' : QuadForm R n') {d d' : ℕ}
    (hd : π ^ d ∣ T.hessian.det) (hd' : ¬ π ^ (d + 1) ∣ T.hessian.det)
    (he : π ^ d' ∣ Q'.hessian.det) (he' : ¬ π ^ (d' + 1) ∣ Q'.hessian.det) :
    π ^ (d + d') ∣ (blockForm T Q').hessian.det ∧ ¬ π ^ (d + d' + 1) ∣ (blockForm T Q').hessian.det := by
  obtain ⟨u, hu, huu⟩ := dvr_exact hπ hd hd'
  obtain ⟨u', hu', huu'⟩ := dvr_exact hπ he he'
  rw [det_hessian_blockForm, hu, hu']
  refine ⟨⟨u * u', by ring⟩, fun h => ?_⟩
  have h2 : π ^ (d + d') * π ∣ π ^ (d + d') * (u * u') := by
    rw [← pow_succ, show π ^ (d + d') * (u * u') = π ^ d * u * (π ^ d' * u') by ring]; exact h
  exact dvr_not_dvd_of_isUnit hπ (huu.mul huu') ((mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero)).mp h2)

theorem det_ne_zero_of_exact {a : R} {d : ℕ} (h : ¬ π ^ (d + 1) ∣ a) : a ≠ 0 :=
  fun h0 => h (h0 ▸ dvd_zero _)

/-- An isometry mod $\pi^k$ as an element of $O(Q\bmod\pi^k)$ (invertible for $k > d$, $\pi^d \,\Vert\, \det H_Q$). -/
def orthOfMat (hπ : Irreducible π) (Q : QuadForm R n) {d : ℕ} (hd : π ^ d ∣ Q.hessian.det)
    (hd' : ¬ π ^ (d + 1) ∣ Q.hessian.det) (hdk : d < k) (X : Matrix (Fin n) (Fin n) (R ⧸ Ideal.span {π ^ k}))
    (hX : (Q.map (Ideal.Quotient.mk _)).compMat X = Q.map (Ideal.Quotient.mk _)) : orthMod Q π k :=
  ⟨Matrix.nonsingInvUnit X (isUnit_det_of_compMat_eq Q π hπ d k hd hd' hdk X hX), hX⟩

theorem orthOfMat_val (hπ : Irreducible π) (Q : QuadForm R n) {d : ℕ} (hd : π ^ d ∣ Q.hessian.det)
    (hd' : ¬ π ^ (d + 1) ∣ Q.hessian.det) (hdk : d < k) (X : Matrix (Fin n) (Fin n) (R ⧸ Ideal.span {π ^ k}))
    (hX : (Q.map (Ideal.Quotient.mk _)).compMat X = Q.map (Ideal.Quotient.mk _)) :
    (orthOfMat hπ Q hd hd' hdk X hX).val.val = X := rfl

/-- **`formF` mod $\pi^k$ is the form $\bar Q \circ \bar X$:** $Q\circ X \equiv T \bmod \pi^k$ coefficientwise iff
$\bar Q\circ\bar X = \bar T$ over $R/\pi^k$. -/
theorem formF_dvd_iff (Q : QuadForm R n) (T : QuadForm R r) (x : Fin n × Fin r → R) :
    (∀ p, π ^ k ∣ formF Q x p - tc T p) ↔
      (Q.map (Ideal.Quotient.mk (Ideal.span {π ^ k}))).compMat (toMat (redI π k x)) =
        T.map (Ideal.Quotient.mk (Ideal.span {π ^ k})) := by
  rw [toMat_redI, map_compMat]
  constructor
  · intro h
    refine ext_upper fun i j hij => ?_
    have := (mk_eq_mk_iff π k _ _).mpr (h ⟨(i, j), hij⟩)
    simpa [formF, tc, QuadForm.map] using this
  · intro h p
    have := congrArg (fun F : QuadForm _ r => F.coeff p.1.1 p.1.2) h
    simp only [QuadForm.map, Matrix.map_apply] at this
    exact (mk_eq_mk_iff π k _ _).mp this

/-- **$H_TS \equiv 0$ forces $T\circ S \equiv 0$** mod $\pi^k$ for $k \ge 2d$ ($\pi^d \,\Vert\, \det H_T$): the entries of $S$ are
divisible by $\pi^{k-d}$ (multiply by the adjugate). -/
theorem eval_zero_of_hessian_mul (hπ : Irreducible π) (T : QuadForm R r) {d : ℕ} (hd : π ^ d ∣ T.hessian.det)
    (hd' : ¬ π ^ (d + 1) ∣ T.hessian.det) (hk : 2 * d ≤ k)
    (S : Matrix (Fin r) (Fin n') (R ⧸ Ideal.span {π ^ k}))
    (hS : (T.map (Ideal.Quotient.mk (Ideal.span {π ^ k}))).hessian * S = 0)
    (x : Fin n' → R ⧸ Ideal.span {π ^ k}) :
    (T.map (Ideal.Quotient.mk (Ideal.span {π ^ k}))).eval (S *ᵥ x) = 0 := by
  set mk := Ideal.Quotient.mk (Ideal.span {π ^ k}) with hmk
  obtain ⟨u, hu, huu⟩ := dvr_exact hπ hd hd'
  obtain ⟨w, hw⟩ := huu.exists_right_inv
  have hdet : (T.map mk).hessian.det = mk (π ^ d) * mk u := by
    rw [hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hu, map_mul]
  have h1 : ((T.map mk).hessian.det) • S = 0 := by
    have h := congrArg (fun M => (T.map mk).hessian.adjugate * M) hS
    simp only [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.mul_zero, Matrix.smul_mul, Matrix.one_mul] at h
    exact h
  have h2 : ∀ i j, mk (π ^ d) * S i j = 0 := by
    intro i j
    have hc := congrFun (congrFun h1 i) j
    simp only [Matrix.smul_apply, smul_eq_mul, hdet, Matrix.zero_apply] at hc
    have hw1 : mk u * mk w = 1 := by rw [← map_mul, hw, map_one]
    linear_combination (mk w) * hc - (mk (π ^ d) * S i j) * hw1
  choose S₀ hS₀ using fun i j => exists_eq_mul_of_ann hπ (show d ≤ k by omega) (S i j) (h2 i j)
  have hSeq : S = (mk (π ^ (k - d))) • (Matrix.of S₀ : Matrix (Fin r) (Fin n') _) := by
    ext i j
    show S i j = mk (π ^ (k - d)) * S₀ i j
    exact hS₀ i j
  rw [hSeq, smul_mulVec, eval_smul_gen]
  have : mk (π ^ (k - d)) ^ 2 = 0 := by
    rw [← map_pow, ← pow_mul]
    exact mk_pow_eq_zero (by omega)
  rw [this, zero_mul]

/-- **The solutions of $H_TS = 0$ mod $\pi^k$:** $q^{dn'}$ matrices $S \in M_{r\times n'}(R/\pi^k)$ ($k \ge d$). -/
theorem card_hessian_ker (hπ : Irreducible π) (T : QuadForm R r) {d : ℕ} (hd : π ^ d ∣ T.hessian.det)
    (hd' : ¬ π ^ (d + 1) ∣ T.hessian.det) (hdk : d ≤ k) :
    Nat.card {S : Matrix (Fin r) (Fin n') (R ⧸ Ideal.span {π ^ k}) //
      (T.map (Ideal.Quotient.mk (Ideal.span {π ^ k}))).hessian * S = 0} = q R ^ (d * n') := by
  obtain ⟨u, hu, huu⟩ := dvr_exact hπ hd hd'
  obtain ⟨w, hw⟩ := huu.exists_right_inv
  have hc : ∀ v : Fin r → R, ∃ y, T.hessian *ᵥ y = π ^ k • v := by
    refine exists_mulVec_eq_smul T.hessian (c := k) ?_
    have hpk : π ^ k = π ^ d * π ^ (k - d) := by rw [← pow_add, Nat.add_sub_cancel' hdk]
    exact ⟨w * π ^ (k - d), by rw [hu, hpk]; linear_combination (-(π ^ d * π ^ (k - d))) * hw⟩
  have hker : Nat.card (redMat π k T.hessian).ker = q R ^ d := by
    rw [card_ker_redMat hπ T.hessian hc, card_quot_range hπ T.hessian (det_ne_zero_of_exact hd'),
      card_quot_span_eq hπ hd hd']
  have hcol : ∀ (M : Matrix (Fin r) (Fin r) (R ⧸ Ideal.span {π ^ k})) (S : Matrix (Fin r) (Fin n') (R ⧸ Ideal.span {π ^ k}))
      (j : Fin n'), (M *ᵥ fun i => S i j) = fun i => (M * S) i j := by
    intro M S j
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  let e : {S : Matrix (Fin r) (Fin n') (R ⧸ Ideal.span {π ^ k}) //
      (T.map (Ideal.Quotient.mk (Ideal.span {π ^ k}))).hessian * S = 0} ≃ (Fin n' → (redMat π k T.hessian).ker) :=
    { toFun := fun S j => ⟨fun i => S.1 i j, by
        rw [AddMonoidHom.mem_ker, redMat_apply, ← hessian_map, hcol, S.2]
        rfl⟩
      invFun := fun f => ⟨Matrix.of fun i j => (f j).1 i, by
        ext i j
        have h := (f j).2
        rw [AddMonoidHom.mem_ker, redMat_apply, ← hessian_map] at h
        have := congrFun h i
        simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this⟩
      left_inv := fun S => rfl
      right_inv := fun f => rfl }
  rw [Nat.card_congr e, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hker, ← pow_mul,
    mul_comm]

/-- **Isometries of the shape $\begin{pmatrix}1 & S\\ 0 & Y\end{pmatrix}$ mod $\pi^k$:** $(T\perp Q')\circ g = T\perp Q'$ iff
$H_TS = 0$ and $Q'\circ Y = Q'$ (for $k \ge 2d$). -/
theorem compMat_blockMat_stab_iff (hπ : Irreducible π) (T : QuadForm R r) (Q' : QuadForm R n') {d : ℕ}
    (hd : π ^ d ∣ T.hessian.det) (hd' : ¬ π ^ (d + 1) ∣ T.hessian.det) (hk : 2 * d ≤ k)
    (S : Matrix (Fin r) (Fin n') (R ⧸ Ideal.span {π ^ k})) (Y : Matrix (Fin n') (Fin n') (R ⧸ Ideal.span {π ^ k})) :
    (blockForm (T.map (Ideal.Quotient.mk (Ideal.span {π ^ k}))) (Q'.map (Ideal.Quotient.mk (Ideal.span {π ^ k})))).compMat
        (blockMat 1 S 0 Y) =
      blockForm (T.map (Ideal.Quotient.mk (Ideal.span {π ^ k}))) (Q'.map (Ideal.Quotient.mk (Ideal.span {π ^ k}))) ↔
    ((T.map (Ideal.Quotient.mk (Ideal.span {π ^ k}))).hessian * S = 0 ∧
      (Q'.map (Ideal.Quotient.mk (Ideal.span {π ^ k}))).compMat Y = Q'.map (Ideal.Quotient.mk (Ideal.span {π ^ k}))) := by
  constructor
  · intro h
    have h1 := hessian_mul_eq_zero_of_compMat _ _ _ _ h
    refine ⟨h1, ?_⟩
    rw [compMat_blockMat_stab _ _ S Y h1 (eval_zero_of_hessian_mul hπ T hd hd' hk S h1)] at h
    exact blockForm_injective_right h
  · rintro ⟨h1, h2⟩
    rw [compMat_blockMat_stab _ _ S Y h1 (eval_zero_of_hessian_mul hπ T hd hd' hk S h1), h2]

/-- **The stabilizer of $\bar E$ in $O((T\perp Q')\bmod\pi^k)$** has $q^{dn'}\,|O(Q'\bmod\pi^k)|$ elements
($k \ge 2d$, $k > d + d'$): it is $\{\begin{pmatrix}1 & S\\ 0 & Y\end{pmatrix} : H_TS \equiv 0,\ Y \in O(Q'\bmod\pi^k)\}$. -/
theorem card_stabilizer_Ebar (hπ : Irreducible π) (T : QuadForm R r) (Q' : QuadForm R n') {d d' : ℕ}
    (hd : π ^ d ∣ T.hessian.det) (hd' : ¬ π ^ (d + 1) ∣ T.hessian.det)
    (he : π ^ d' ∣ Q'.hessian.det) (he' : ¬ π ^ (d' + 1) ∣ Q'.hessian.det) (hdk : 2 * d ≤ k) (hQk : d + d' < k) :
    Nat.card (MulAction.stabilizer (orthMod (blockForm T Q') π k) (Ebar r n' π k)) =
      q R ^ (d * n') * Nat.card (orthMod Q' π k) := by
  obtain ⟨hdQ, hdQ'⟩ := det_blockForm_exact hπ T Q' hd hd' he he'
  set mk := Ideal.Quotient.mk (Ideal.span {π ^ k}) with hmk
  have hbf : (blockForm T Q').map mk = blockForm (T.map mk) (Q'.map mk) := map_blockForm mk T Q'
  let e1 : MulAction.stabilizer (orthMod (blockForm T Q') π k) (Ebar r n' π k) ≃
      {X : Matrix (Fin (r + n')) (Fin (r + n')) (R ⧸ Ideal.span {π ^ k}) //
        ((blockForm T Q').map mk).compMat X = (blockForm T Q').map mk ∧
          X * Efr (R ⧸ Ideal.span {π ^ k}) r n' = Efr (R ⧸ Ideal.span {π ^ k}) r n'} :=
    { toFun := fun g => ⟨g.1.1.val, g.1.2, by
        have h1 : g.1 • Ebar r n' π k = Ebar r n' π k := g.2
        have h2 := congrArg toMat h1
        rw [modFrameAct_smul, toMat_frameMat_mulVec, toMat_Ebar] at h2
        exact h2⟩
      invFun := fun X => ⟨orthOfMat hπ _ hdQ hdQ' (by omega) X.1 X.2.1, by
        show frameMat r X.1 *ᵥ Ebar r n' π k = Ebar r n' π k
        apply toMat_injective'
        rw [toMat_frameMat_mulVec, toMat_Ebar, X.2.2]⟩
      left_inv := fun g => Subtype.ext (Subtype.ext (Units.ext rfl))
      right_inv := fun X => rfl }
  have key : ∀ X : Matrix (Fin (r + n')) (Fin (r + n')) (R ⧸ Ideal.span {π ^ k}),
      ((blockForm T Q').map mk).compMat X = (blockForm T Q').map mk →
      X * Efr (R ⧸ Ideal.span {π ^ k}) r n' = Efr (R ⧸ Ideal.span {π ^ k}) r n' →
      (T.map mk).hessian * blkS X = 0 ∧ (Q'.map mk).compMat (blkY X) = Q'.map mk := by
    intro X h1 h2
    have h3 := eq_blockMat_of_mul_Efr' h2
    rw [hbf] at h1
    refine (compMat_blockMat_stab_iff hπ T Q' hd hd' hdk _ _).mp ?_
    rw [← h3]
    exact h1
  let e2 : {X : Matrix (Fin (r + n')) (Fin (r + n')) (R ⧸ Ideal.span {π ^ k}) //
        ((blockForm T Q').map mk).compMat X = (blockForm T Q').map mk ∧
          X * Efr (R ⧸ Ideal.span {π ^ k}) r n' = Efr (R ⧸ Ideal.span {π ^ k}) r n'} ≃
      {S : Matrix (Fin r) (Fin n') (R ⧸ Ideal.span {π ^ k}) // (T.map mk).hessian * S = 0} ×
        {Y : Matrix (Fin n') (Fin n') (R ⧸ Ideal.span {π ^ k}) // (Q'.map mk).compMat Y = Q'.map mk} :=
    { toFun := fun X => (⟨blkS X.1, (key X.1 X.2.1 X.2.2).1⟩, ⟨blkY X.1, (key X.1 X.2.1 X.2.2).2⟩)
      invFun := fun p => ⟨blockMat 1 p.1.1 0 p.2.1, by
          rw [hbf]
          exact (compMat_blockMat_stab_iff hπ T Q' hd hd' hdk _ _).mpr ⟨p.1.2, p.2.2⟩,
        blockMat_one_mul_Efr _ _⟩
      left_inv := fun X => Subtype.ext (eq_blockMat_of_mul_Efr' X.2.2).symm
      right_inv := fun p => by
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> simp }
  have hO : Nat.card {Y : Matrix (Fin n') (Fin n') (R ⧸ Ideal.span {π ^ k}) // (Q'.map mk).compMat Y = Q'.map mk} =
      Nat.card (orthMod Q' π k) := by
    have := repCountForm_self_eq_card_orthMod Q' π hπ d' k he he' (by omega)
    unfold repCountForm at this
    exact this
  rw [Nat.card_congr (e1.trans e2), Nat.card_prod, hO, card_hessian_ker hπ T hd hd' (by omega)]

theorem toMat_add_smul {A : Type*} [CommRing A] (x y : Fin n × Fin r → A) (c : A) :
    toMat (x + c • y) = toMat x + c • toMat y := by
  ext l j
  rfl

/-- **Frames near $\bar E$ with the right Gram form are in its orbit** (the explicit isometry mod $\pi^k$): if
$\bar Q\circ(\bar E + aW) = \bar T$ with $a = \pi^{k-d}$ ($k \ge 4d$, $k > d + d'$), then $(\bar E + aW) = h\bar E$ for some
$h \in O((T\perp Q')\bmod\pi^k)$. Explicitly
$h = \begin{pmatrix}1 + aA & B\\ aC & 1\end{pmatrix}$, $B = -\pi^{k-2d}u^{-1}\mathrm{adj}(H_T)\,C^{\mathsf T}H_{Q'}$ ($\det H_T = \pi^du$). -/
theorem exists_smul_Ebar (hπ : Irreducible π) (T : QuadForm R r) (Q' : QuadForm R n') {d d' : ℕ}
    (hd : π ^ d ∣ T.hessian.det) (hd' : ¬ π ^ (d + 1) ∣ T.hessian.det)
    (he : π ^ d' ∣ Q'.hessian.det) (he' : ¬ π ^ (d' + 1) ∣ Q'.hessian.det) (hk4 : 4 * d ≤ k) (hQk : d + d' < k)
    (W : Fin (r + n') × Fin r → R ⧸ Ideal.span {π ^ k})
    (hW : ((blockForm T Q').map (Ideal.Quotient.mk (Ideal.span {π ^ k}))).compMat
      (toMat (Ebar r n' π k + Ideal.Quotient.mk (Ideal.span {π ^ k}) (π ^ (k - d)) • W)) =
        T.map (Ideal.Quotient.mk (Ideal.span {π ^ k}))) :
    ∃ h : orthMod (blockForm T Q') π k,
      h • Ebar r n' π k = Ebar r n' π k + Ideal.Quotient.mk (Ideal.span {π ^ k}) (π ^ (k - d)) • W := by
  obtain ⟨hdQ, hdQ'⟩ := det_blockForm_exact hπ T Q' hd hd' he he'
  set mk := Ideal.Quotient.mk (Ideal.span {π ^ k}) with hmk
  have hbf : (blockForm T Q').map mk = blockForm (T.map mk) (Q'.map mk) := map_blockForm mk T Q'
  set a : R ⧸ Ideal.span {π ^ k} := mk (π ^ (k - d)) with ha
  obtain ⟨u, hu, huu⟩ := dvr_exact hπ hd hd'
  obtain ⟨w, hw⟩ := huu.exists_right_inv
  set A' : Matrix (Fin r) (Fin r) (R ⧸ Ideal.span {π ^ k}) := Matrix.of fun i j => W (Fin.castAdd n' i, j) with hA'
  set C : Matrix (Fin n') (Fin r) (R ⧸ Ideal.span {π ^ k}) := Matrix.of fun i j => W (Fin.natAdd r i, j) with hC
  set c : R ⧸ Ideal.span {π ^ k} := mk (π ^ (k - 2 * d) * w) with hc
  set B₀ : Matrix (Fin r) (Fin n') (R ⧸ Ideal.span {π ^ k}) :=
    -((T.map mk).hessian.adjugate * Cᵀ * (Q'.map mk).hessian) with hB₀
  set B : Matrix (Fin r) (Fin n') (R ⧸ Ideal.span {π ^ k}) := c • B₀ with hB
  have hdet : (T.map mk).hessian.det = mk (π ^ d) * mk u := by
    rw [hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hu, map_mul]
  have hca : c * (T.map mk).hessian.det = a := by
    rw [hdet, hc, ha, ← map_mul, ← map_mul]
    congr 1
    have : π ^ (k - 2 * d) * w * (π ^ d * u) = π ^ (k - 2 * d) * π ^ d * (u * w) := by ring
    rw [this, hw, mul_one, ← pow_add]
    congr 1
    omega
  have h2 : (T.map mk).hessian * B + a • (Cᵀ * (Q'.map mk).hessian) = 0 := by
    rw [hB, hB₀, Matrix.mul_smul, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_adjugate,
      Matrix.smul_mul, Matrix.one_mul, smul_neg, Matrix.smul_mul, smul_smul, hca]
    exact neg_add_cancel _
  have h3 : a * a = 0 := by
    rw [ha, ← map_mul, ← pow_add]
    exact mk_pow_eq_zero (by omega)
  have h5 : ∀ x : Fin n' → R ⧸ Ideal.span {π ^ k}, (T.map mk).eval (B *ᵥ x) = 0 := by
    intro x
    rw [hB, smul_mulVec, eval_smul_gen]
    have : c ^ 2 = 0 := by
      rw [hc, ← map_pow, mul_pow, ← pow_mul, show π ^ ((k - 2 * d) * 2) * w ^ 2 = π ^ ((k - 2 * d) * 2) * w ^ 2 from rfl]
      rw [map_mul, mk_pow_eq_zero (by omega), zero_mul]
    rw [this, zero_mul]
  have hZ : toMat (Ebar r n' π k + a • W) = Efr (R ⧸ Ideal.span {π ^ k}) r n' + a • toMat W := by
    rw [toMat_add_smul, toMat_Ebar]
  have hx1 : ∀ x₁ : Fin r → R ⧸ Ideal.span {π ^ k},
      (fun j => ((Efr (R ⧸ Ideal.span {π ^ k}) r n' + a • toMat W) *ᵥ x₁) (Fin.castAdd n' j)) = x₁ + a • (A' *ᵥ x₁) := by
    intro x₁
    funext i
    rw [add_mulVec, smul_mulVec]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    simp [mulVec, dotProduct, Matrix.one_apply]
  have hx2 : ∀ x₁ : Fin r → R ⧸ Ideal.span {π ^ k},
      (fun j => ((Efr (R ⧸ Ideal.span {π ^ k}) r n' + a • toMat W) *ᵥ x₁) (Fin.natAdd r j)) = a • (C *ᵥ x₁) := by
    intro x₁
    funext i
    rw [add_mulVec, smul_mulVec]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : (Efr (R ⧸ Ideal.span {π ^ k}) r n' *ᵥ x₁) (Fin.natAdd r i) = 0 := by
      simp [mulVec, dotProduct]
    rw [this, zero_add]
    rfl
  have h1 : ∀ x₁ : Fin r → R ⧸ Ideal.span {π ^ k},
      (T.map mk).eval (x₁ + a • (A' *ᵥ x₁)) + (Q'.map mk).eval (a • (C *ᵥ x₁)) = (T.map mk).eval x₁ := by
    intro x₁
    have h := congrArg (fun F : QuadForm _ r => F.eval x₁) hW
    simp only [eval_compMat, hbf] at h
    rw [hZ] at h
    have hev : ∀ y : Fin (r + n') → R ⧸ Ideal.span {π ^ k}, (blockForm (T.map mk) (Q'.map mk)).eval y =
        (T.map mk).eval (fun j => y (Fin.castAdd n' j)) + (Q'.map mk).eval (fun j => y (Fin.natAdd r j)) :=
      fun y => evalIn_blockForm _ _ _ y
    rw [hev, hx1, hx2] at h
    exact h
  have hg := compMat_blockMat_near_one (T.map mk) (Q'.map mk) a A' B C h1 h2 h3 h5
  rw [← hbf] at hg
  refine ⟨orthOfMat hπ _ hdQ hdQ' (by omega) (blockMat (1 + a • A') B (a • C) 1) hg, ?_⟩
  apply toMat_injective'
  rw [modFrameAct_smul, toMat_frameMat_mulVec, hZ, toMat_Ebar]
  show blockMat (1 + a • A') B (a • C) 1 * Efr (R ⧸ Ideal.span {π ^ k}) r n' = _
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [blockMat_mul_Efr_castAdd, Matrix.add_apply, Matrix.smul_apply, Efr_castAdd]
    simp [hA', toMat]
  · simp only [blockMat_mul_Efr_natAdd, Matrix.add_apply, Matrix.smul_apply, Efr_natAdd]
    simp [hC, toMat]

/-- **The orbit is near $KE$** ("$\supseteq$"): $g\bar E$ solves $Q\circ z \equiv T \bmod \pi^k$ and is $\equiv \kappa E \bmod \pi^s$ for an
integral isometry $\kappa \equiv g \bmod \pi^{k - d_Q}$ (`exists_compMat_eq_of_dvd`). -/
theorem near_of_smul_Ebar (hπ : Irreducible π) (T : QuadForm R r) (Q' : QuadForm R n') {d d' : ℕ}
    (hd : π ^ d ∣ T.hessian.det) (hd' : ¬ π ^ (d + 1) ∣ T.hessian.det)
    (he : π ^ d' ∣ Q'.hessian.det) (he' : ¬ π ^ (d' + 1) ∣ Q'.hessian.det) {s : ℕ}
    (hsk : s + (d + d') ≤ k) (hk2 : 2 * (d + d') + 1 ≤ k) (g : orthMod (blockForm T Q') π k) :
    (∀ p, π ^ k ∣ formF (blockForm T Q') (liftI π k (g • Ebar r n' π k)) p - tc T p) ∧
      ∃ a ∈ gOrbit (frameRep (blockForm T Q') r) ⊤ stdFrame,
        ∀ i, π ^ s ∣ liftI π k (g • Ebar r n' π k) i - a i := by
  obtain ⟨hdQ, hdQ'⟩ := det_blockForm_exact hπ T Q' hd hd' he he'
  generalize hQ : blockForm T Q' = Q at g hdQ hdQ' ⊢
  set mk := Ideal.Quotient.mk (Ideal.span {π ^ k}) with hmk
  have hg : (Q.map mk).compMat g.val.val = Q.map mk := g.2
  refine ⟨?_, ?_⟩
  · rw [formF_dvd_iff, redI_liftI, modFrameAct_smul, toMat_frameMat_mulVec, ← compMat_mul, hg]
    show (Q.map mk).compMat (toMat (redI π k stdFrame)) = _
    rw [toMat_redI, toMat_stdFrame, map_compMat, ← hQ, compMat_stdFrameMat]
  · let X : Matrix (Fin (r + n')) (Fin (r + n')) R :=
      Matrix.of fun i j => liftI π k (fun p : Fin (r + n') × Fin (r + n') => g.val.val p.1 p.2) (i, j)
    have hXm : X.map mk = g.val.val := by
      ext i j
      exact congrFun (redI_liftI π k (fun p : Fin (r + n') × Fin (r + n') => g.val.val p.1 p.2)) (i, j)
    have hcoeff : ∀ i j, π ^ k ∣ (Q.compMat X).coeff i j - Q.coeff i j := by
      intro i j
      have h1 : ((Q.map mk).compMat g.val.val).coeff i j = (Q.map mk).coeff i j := by rw [hg]
      rw [← hXm, map_compMat] at h1
      have h2 : mk ((Q.compMat X).coeff i j) = mk (Q.coeff i j) := h1
      exact (mk_eq_mk_iff π k _ _).mp h2
    obtain ⟨Y, hY, hYX⟩ := exists_compMat_eq_of_dvd hπ Q hdQ hdQ' hk2 X hcoeff
    have hnd : Q.Nondegenerate := det_ne_zero_of_exact hdQ'
    refine ⟨frameMat r Y *ᵥ stdFrame, ⟨isomOf hnd Y hY, Subgroup.mem_top _, ?_⟩, fun i => ?_⟩
    · rw [frameRep_apply, isomOf_val]
    · have hgE : g • Ebar r n' π k = redI π k (frameMat r X *ᵥ stdFrame) := by
        rw [modFrameAct_smul, redI_mulVec_gen, frameMat_map, hXm]
        rfl
      have h1 : π ^ k ∣ liftI π k (redI π k (frameMat r X *ᵥ stdFrame)) i - (frameMat r X *ᵥ stdFrame) i :=
        liftI_redI_dvd_gen π k _ i
      have h2 : π ^ (k - (d + d')) ∣ (frameMat r X *ᵥ stdFrame) i - (frameMat r Y *ᵥ stdFrame) i := by
        rw [frameMat_mulVec, frameMat_mulVec, ← Finset.sum_sub_distrib]
        refine Finset.dvd_sum fun l _ => ?_
        rw [← sub_mul]
        refine dvd_mul_of_dvd_left ?_ _
        have := hYX i.1 l
        rw [← dvd_neg, neg_sub] at this
        exact this
      rw [hgE]
      have h3 := (pow_dvd_pow π (show s ≤ k by omega)).trans h1
      have h4 := (pow_dvd_pow π (show s ≤ k - (d + d') by omega)).trans h2
      have := h3.add h4
      rwa [sub_add_sub_cancel] at this

/-- **A frame near $KE$ is in the orbit of $\bar E$** ("$\subseteq$"): translate by $\kappa_0^{-1}$, Hensel (`exists_formF_eq_of_dvd`),
openness (`exists_frame_openMat`) gives an integral isometry $M$ with $y \equiv ME \bmod \pi^{k-d}$, and then
`exists_smul_Ebar` moves $\bar E$ to $M^{-1}\bar y$. -/
theorem smul_Ebar_of_near (hπ : Irreducible π) (T : QuadForm R r) (Q' : QuadForm R n') {d d' : ℕ}
    (hd : π ^ d ∣ T.hessian.det) (hd' : ¬ π ^ (d + 1) ∣ T.hessian.det)
    (he : π ^ d' ∣ Q'.hessian.det) (he' : ¬ π ^ (d' + 1) ∣ Q'.hessian.det)
    {P : Matrix (Fin r) (Fin r) R} (hPdet : P.det ≠ 0) {dg : Fin r → R} (hP : T.compMat P = QuadForm.diag dg)
    (hdg : ∀ i, dg i ≠ 0) {f : ℕ} (hf : ∀ i, ¬ π ^ (f + 1) ∣ 4 * dg i)
    {s : ℕ} (hs : r * f + 1 ≤ s) (hk : s + 4 * (d + d') + 1 ≤ k)
    (z : Fin (r + n') × Fin r → R ⧸ Ideal.span {π ^ k})
    (hz1 : ∀ p, π ^ k ∣ formF (blockForm T Q') (liftI π k z) p - tc T p)
    (hz2 : ∃ a ∈ gOrbit (frameRep (blockForm T Q') r) ⊤ stdFrame, ∀ i, π ^ s ∣ liftI π k z i - a i) :
    ∃ g : orthMod (blockForm T Q') π k, g • Ebar r n' π k = z := by
  obtain ⟨hdQ, hdQ'⟩ := det_blockForm_exact hπ T Q' hd hd' he he'
  set Q := blockForm T Q' with hQ
  set mk := Ideal.Quotient.mk (Ideal.span {π ^ k}) with hmk
  obtain ⟨_, ⟨κ₀, -, rfl⟩, hza⟩ := hz2
  set zt := liftI π k z with hzt
  set ρ := frameRep Q r with hρ
  set y := ρ κ₀⁻¹ *ᵥ zt with hy
  have hy1 : ∀ p, π ^ k ∣ formF Q y p - tc T p := by
    intro p
    have := hz1 p
    rwa [hy, hρ, frameRep_apply, formF_frameMat_of_compMat Q (compMat_frameRep Q κ₀⁻¹)]
  have hy2 : ∀ i, π ^ s ∣ y i - stdFrame i := by
    intro i
    have := dvd_mulVec_sub_gen (ρ κ₀⁻¹) hza i
    rwa [mulVec_inv_mulVec_g ρ] at this
  obtain ⟨ys, hys1, hys2⟩ := exists_formF_eq_of_dvd hπ Q T hd hd' (K := k) (by omega) y hy1
  have hxx : ∀ i, π ^ s ∣ ys i - stdFrame i := by
    intro i
    have h1 := (pow_dvd_pow π (show s ≤ k - d by omega)).trans (hys2 i)
    have := h1.add (hy2 i)
    rwa [sub_add_sub_cancel] at this
  obtain ⟨M, hM, hMx, -⟩ := exists_frame_openMat hπ Q T hPdet hP hdg hf hs (x := stdFrame) (x' := ys)
    (formF_stdFrame T Q') hys1 hxx
  have hyM : ∀ i, π ^ (k - d) ∣ y i - (frameMat r M *ᵥ stdFrame) i := by
    intro i
    rw [hMx, ← dvd_neg, neg_sub]
    exact hys2 i
  choose wv hwv using hyM
  -- the group elements
  have hκ₀ : (Q.map mk).compMat ((κ₀ : GL (Fin (r + n')) R).val.map mk) = Q.map mk := by
    rw [map_compMat, compMat_frameRep]
  have hM' : (Q.map mk).compMat (M.map mk) = Q.map mk := by rw [map_compMat, hM]
  set g₀ : orthMod Q π k := orthOfMat hπ Q hdQ hdQ' (by omega) _ hκ₀ with hg₀
  set g₁ : orthMod Q π k := orthOfMat hπ Q hdQ hdQ' (by omega) _ hM' with hg₁
  have hz : z = g₀ • redI π k y := by
    rw [modFrameAct_smul]
    show z = frameMat r ((κ₀ : GL (Fin (r + n')) R).val.map mk) *ᵥ redI π k y
    rw [← frameMat_map, ← redI_mulVec_gen, ← frameRep_apply, hy, mulVec_mulVec_inv_g ρ, hzt, redI_liftI]
  have hry : redI π k y = g₁ • Ebar r n' π k + mk (π ^ (k - d)) • redI π k wv := by
    funext i
    have h1 : y i = (frameMat r M *ᵥ stdFrame) i + π ^ (k - d) * wv i := by
      linear_combination hwv i
    show mk (y i) = _
    rw [h1, map_add, map_mul]
    rw [modFrameAct_smul]
    show _ = (frameMat r (M.map mk) *ᵥ redI π k stdFrame) i + _
    rw [← frameMat_map, ← redI_mulVec_gen]
    rfl
  set V := g₁⁻¹ • redI π k y with hV
  have hVeq : V = Ebar r n' π k + mk (π ^ (k - d)) • (g₁⁻¹ • redI π k wv) := by
    rw [hV, hry, modFrameAct_smul, modFrameAct_smul, modFrameAct_smul, mulVec_add, mulVec_smul]
    congr 1
    rw [← modFrameAct_smul, ← modFrameAct_smul, inv_smul_smul]
  have hW : ((blockForm T Q').map mk).compMat
      (toMat (Ebar r n' π k + mk (π ^ (k - d)) • (g₁⁻¹ • redI π k wv))) = T.map mk := by
    rw [← hVeq, hV, modFrameAct_smul, toMat_frameMat_mulVec, ← compMat_mul]
    have hg1 : (Q.map mk).compMat (g₁⁻¹).val.val = Q.map mk := (g₁⁻¹).2
    rw [hg1]
    exact (formF_dvd_iff Q T y).mp hy1
  obtain ⟨h, hh⟩ := exists_smul_Ebar hπ T Q' hd hd' he he' (by omega) (by omega) _ hW
  refine ⟨g₀ * g₁ * h, ?_⟩
  rw [mul_smul, mul_smul, hh, ← hVeq, hV, smul_inv_smul, ← hz]

end Mod

/-- **The orbit of the standard frame mod $\pi^k$** (Weil's fibration in finite form). Let $\pi^d\,\Vert\,\det H_T$,
$\pi^{d'}\,\Vert\,\det H_{Q'}$, and let $T\circ P = \langle d_0, \dots, d_{r-1}\rangle$ be a diagonalization ($\det P \ne 0$, $d_i \ne 0$,
$\pi^{f+1}\nmid 4d_i$). For $s \ge rf + 1$ and $k \ge s + 4(d + d') + 1$,
$$N_{k,s}(KE)\cdot q^{dn'}\cdot|O(Q'\bmod\pi^k)| = |O((T\perp Q')\bmod\pi^k)|.$$ -/
@[kb "weil1982" "§3.4 (the fibration O(V) → frames, finite form) [unverified]"]
theorem frameNear_stdFrame {π : R} (hπ : Irreducible π) (T : QuadForm R r) (Q' : QuadForm R n') {d d' : ℕ}
    (hd : π ^ d ∣ T.hessian.det) (hd' : ¬ π ^ (d + 1) ∣ T.hessian.det)
    (he : π ^ d' ∣ Q'.hessian.det) (he' : ¬ π ^ (d' + 1) ∣ Q'.hessian.det)
    {P : Matrix (Fin r) (Fin r) R} (hPdet : P.det ≠ 0) {dg : Fin r → R} (hP : T.compMat P = QuadForm.diag dg)
    (hdg : ∀ i, dg i ≠ 0) {f : ℕ} (hf : ∀ i, ¬ π ^ (f + 1) ∣ 4 * dg i)
    {s k : ℕ} (hs : r * f + 1 ≤ s) (hk : s + 4 * (d + d') + 1 ≤ k) :
    gNear (formF (blockForm T Q')) (tc T) π k s (gOrbit (frameRep (blockForm T Q') r) ⊤ stdFrame) *
        (q R ^ (d * n') * Nat.card (orthMod Q' π k)) = Nat.card (orthMod (blockForm T Q') π k) := by
  have hnear : gNear (formF (blockForm T Q')) (tc T) π k s (gOrbit (frameRep (blockForm T Q') r) ⊤ stdFrame) =
      Nat.card (MulAction.orbit (orthMod (blockForm T Q') π k) (Ebar r n' π k)) := by
    unfold gNear
    refine Nat.card_congr (Equiv.subtypeEquivRight fun z => ?_)
    constructor
    · rintro ⟨hz1, hz2⟩
      obtain ⟨g, hg⟩ := smul_Ebar_of_near hπ T Q' hd hd' he he' hPdet hP hdg hf hs hk z hz1 hz2
      exact ⟨g, hg⟩
    · rintro ⟨g, rfl⟩
      exact near_of_smul_Ebar hπ T Q' hd hd' he he' (s := s) (by omega) (by omega) g
  have horb := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (orthMod (blockForm T Q') π k) (Ebar r n' π k))
  rw [Nat.card_prod, card_stabilizer_Ebar hπ T Q' hd hd' he he' (by omega) (by omega)] at horb
  rw [hnear, horb]

end QuadFormsKB.Tamagawa.Frames
