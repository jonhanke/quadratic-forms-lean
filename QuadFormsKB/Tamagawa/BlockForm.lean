/-
# The orthogonal sum $T \perp Q'$, the standard frame, and its stabilizer

**Layer:** forms over a commutative ring; then $F$ a number field (the rational, local and finite adelic orthogonal groups).

For representations of a form $T$ of rank $r$ the role of the split form $\langle m\rangle\perp Q'$ is played by the
orthogonal sum $T \perp Q'$ on $\mathrm{Fin}(r + n')$ (`blockForm`; the first $r$ coordinates carry $T$, via `Fin.castAdd`, the last
$n'$ carry $Q'$, via `Fin.natAdd`), and the role of $e_0$ by the **standard frame** $E = \binom{1_r}{0}$ (`stdFrameMat`), with
$(T\perp Q')\circ E = T$.

**Defines**
* `blockMat P B C D` $= \begin{pmatrix}P & B\\ C & D\end{pmatrix}$ in the coordinates $\mathrm{Fin}(r + n')$;
* `blockForm T Q'` $= T \perp Q'$; `stdFrameMat`, `stdFrame` $= E$;
* `orthEmbB T Q' R : O(Q')(R) → O(T ⊥ Q')(R)`, $g \mapsto \mathrm{diag}(1_r, g)$, and its adelic version `orthEmbBAf`.

**Proves**
* `exists_orthEmbB_eq` (**the stabilizer of $E$**): over a field $K \supseteq F$ in which $\det H_T \ne 0$, an isometry of $T\perp Q'$ fixing
  $E$ is $\mathrm{diag}(1_r, g)$ with $g \in O(Q')(K)$ (the rows: $E^{\mathsf T}H\gamma = E^{\mathsf T}H$ and $E^{\mathsf T}H = (H_T\ 0)$);
* `exists_orthGroup_mul_stdFrameMat` (**Witt transitivity on frames**): for $T \perp Q'$ and $T$ nondegenerate, every $X \in F^{n\times r}$
  with $(T\perp Q')\circ X = T$ is $\gamma E$ for some $\gamma \in O(T\perp Q')(F)$ (`QuadraticForm.Witt.exists_isometryEquiv_of_family`;
  O'Meara 1963, 42:17, p. 98);
* local and adelic compatibilities (`locAct_blockGL'_std_iff`, `comap_orthEmbBAf_locStab_intVec`), as in `SplitForm.lean`.

Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.SplitForm
import QuadFormsKB.Tamagawa.FrameHensel
import QuadFormsKB.Witt.Extension

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Frames

open QuadForm LocalDensity LocalDensity.DVR QuadFormsKB.Tamagawa Lattices NumberField IsDedekindDomain

/-! ### Block matrices and the orthogonal sum -/

section Algebra

variable {A : Type*} [CommRing A] {r n' : ℕ}

/-- **The block matrix** $\begin{pmatrix}P & B\\ C & D\end{pmatrix}$ in the coordinates $\mathrm{Fin}(r + n')$ (rows and columns $0, \dots, r-1$
for the first block). -/
def blockMat (P : Matrix (Fin r) (Fin r) A) (B : Matrix (Fin r) (Fin n') A) (C : Matrix (Fin n') (Fin r) A)
    (D : Matrix (Fin n') (Fin n') A) : Matrix (Fin (r + n')) (Fin (r + n')) A :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks P B C D)

@[simp] theorem blockMat_castAdd_castAdd (P : Matrix (Fin r) (Fin r) A) (B : Matrix (Fin r) (Fin n') A)
    (C : Matrix (Fin n') (Fin r) A) (D : Matrix (Fin n') (Fin n') A) (i j : Fin r) :
    blockMat P B C D (Fin.castAdd n' i) (Fin.castAdd n' j) = P i j := by
  simp [blockMat]

@[simp] theorem blockMat_castAdd_natAdd (P : Matrix (Fin r) (Fin r) A) (B : Matrix (Fin r) (Fin n') A)
    (C : Matrix (Fin n') (Fin r) A) (D : Matrix (Fin n') (Fin n') A) (i : Fin r) (j : Fin n') :
    blockMat P B C D (Fin.castAdd n' i) (Fin.natAdd r j) = B i j := by
  simp [blockMat]

@[simp] theorem blockMat_natAdd_castAdd (P : Matrix (Fin r) (Fin r) A) (B : Matrix (Fin r) (Fin n') A)
    (C : Matrix (Fin n') (Fin r) A) (D : Matrix (Fin n') (Fin n') A) (i : Fin n') (j : Fin r) :
    blockMat P B C D (Fin.natAdd r i) (Fin.castAdd n' j) = C i j := by
  simp [blockMat]

@[simp] theorem blockMat_natAdd_natAdd (P : Matrix (Fin r) (Fin r) A) (B : Matrix (Fin r) (Fin n') A)
    (C : Matrix (Fin n') (Fin r) A) (D : Matrix (Fin n') (Fin n') A) (i j : Fin n') :
    blockMat P B C D (Fin.natAdd r i) (Fin.natAdd r j) = D i j := by
  simp [blockMat]

theorem blockMat_mul (P B C D P' B' C' D') :
    blockMat (A := A) (r := r) (n' := n') P B C D * blockMat P' B' C' D' =
      blockMat (P * P' + B * C') (P * B' + B * D') (C * P' + D * C') (C * B' + D * D') := by
  rw [blockMat, blockMat, blockMat, ← Matrix.reindexLinearEquiv_apply A A, ← Matrix.reindexLinearEquiv_apply A A,
    ← Matrix.reindexLinearEquiv_apply A A, Matrix.reindexLinearEquiv_mul, Matrix.fromBlocks_multiply]

theorem blockMat_transpose (P : Matrix (Fin r) (Fin r) A) (B : Matrix (Fin r) (Fin n') A)
    (C : Matrix (Fin n') (Fin r) A) (D : Matrix (Fin n') (Fin n') A) :
    (blockMat P B C D)ᵀ = blockMat Pᵀ Cᵀ Bᵀ Dᵀ := by
  rw [blockMat, blockMat, Matrix.transpose_reindex, Matrix.fromBlocks_transpose]

theorem blockMat_one : blockMat (1 : Matrix (Fin r) (Fin r) A) 0 0 (1 : Matrix (Fin n') (Fin n') A) = 1 := by
  rw [blockMat, Matrix.fromBlocks_one]
  exact Matrix.reindex_apply _ _ _ ▸ Matrix.submatrix_one_equiv _

theorem blockMat_add (P B C D P' B' C' D') :
    blockMat (A := A) (r := r) (n' := n') P B C D + blockMat P' B' C' D' = blockMat (P + P') (B + B') (C + C') (D + D') := by
  rw [blockMat, blockMat, blockMat, ← Matrix.fromBlocks_add]
  rfl

theorem blockMat_map {S : Type*} [CommRing S] (f : A →+* S) (P : Matrix (Fin r) (Fin r) A) (B : Matrix (Fin r) (Fin n') A)
    (C : Matrix (Fin n') (Fin r) A) (D : Matrix (Fin n') (Fin n') A) :
    (blockMat P B C D).map f = blockMat (P.map f) (B.map f) (C.map f) (D.map f) := by
  rw [blockMat, blockMat, ← Matrix.fromBlocks_map]
  rfl

theorem det_blockMat_diag (P : Matrix (Fin r) (Fin r) A) (D : Matrix (Fin n') (Fin n') A) :
    (blockMat P 0 0 D).det = P.det * D.det := by
  rw [blockMat, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

theorem blockMat_injective_right {D D' : Matrix (Fin n') (Fin n') A}
    (h : blockMat (1 : Matrix (Fin r) (Fin r) A) 0 0 D = blockMat 1 0 0 D') : D = D' := by
  ext i j
  have := congrFun (congrFun h (Fin.natAdd r i)) (Fin.natAdd r j)
  simpa using this

theorem blockMat_inj {P P' : Matrix (Fin r) (Fin r) A} {B B' : Matrix (Fin r) (Fin n') A}
    {C C' : Matrix (Fin n') (Fin r) A} {D D' : Matrix (Fin n') (Fin n') A}
    (h : blockMat P B C D = blockMat P' B' C' D') : P = P' ∧ B = B' ∧ C = C' ∧ D = D' := by
  have h' := (Matrix.reindex finSumFinEquiv finSumFinEquiv).injective h
  exact Matrix.fromBlocks_inj.mp h'

theorem castAdd_le_natAdd (a : Fin r) (b : Fin n') : Fin.castAdd n' a ≤ Fin.natAdd r b :=
  Fin.le_iff_val_le_val.mpr (by show a.val ≤ r + b.val; omega)

theorem not_natAdd_le_castAdd (a : Fin n') (b : Fin r) : ¬ Fin.natAdd r a ≤ Fin.castAdd n' b := fun h => by
  have := Fin.le_iff_val_le_val.mp h
  change r + a.val ≤ b.val at this
  omega

theorem castAdd_ne_natAdd (a : Fin r) (b : Fin n') : Fin.castAdd n' a ≠ Fin.natAdd r b := fun h => by
  have := congrArg Fin.val h
  change a.val = r + b.val at this
  omega

theorem castAdd_le_castAdd_iff (a b : Fin r) : Fin.castAdd n' a ≤ Fin.castAdd n' b ↔ a ≤ b :=
  Fin.le_iff_val_le_val.trans (Fin.le_iff_val_le_val (a := a) (b := b)).symm

theorem natAdd_le_natAdd_iff (a b : Fin n') : Fin.natAdd r a ≤ Fin.natAdd r b ↔ a ≤ b := by
  rw [Fin.le_iff_val_le_val, Fin.le_iff_val_le_val (a := a)]
  change r + a.val ≤ r + b.val ↔ _
  omega

/-- The coefficients of $Q \circ X$ in terms of $M = X^{\mathsf T} C X$. -/
theorem coeff_compMat_eq (Q : QuadForm A r) (X : Matrix (Fin r) (Fin n') A) (i j : Fin n') :
    (Q.compMat X).coeff i j = if i ≤ j then
      (if i = j then (Xᵀ * Q.coeff * X : Matrix (Fin n') (Fin n') A) i i
      else (Xᵀ * Q.coeff * X : Matrix (Fin n') (Fin n') A) i j +
        (Xᵀ * Q.coeff * X : Matrix (Fin n') (Fin n') A) j i) else 0 := by
  rw [QuadForm.compMat_coeff]
  by_cases hij : i ≤ j
  · rw [if_pos hij, if_pos hij]
    by_cases he : i = j
    · subst he
      rw [if_pos rfl, if_pos rfl, QuadForm.eval_eq_dotProduct', ← QuadForm.transpose_mul_mul_apply]
    · rw [if_neg he, if_neg he, QuadForm.hessian, add_mulVec, dotProduct_add,
        Matrix.dotProduct_transpose_mulVec, QuadForm.transpose_mul_mul_apply, QuadForm.transpose_mul_mul_apply]
  · simp [hij]

/-- **The orthogonal sum** $T \perp Q'$: $(T\perp Q')(x) = T(x_0, \dots, x_{r-1}) + Q'(x_r, \dots, x_{r+n'-1})$. -/
@[kb "omeara1963" "§42A, p. 88 (orthogonal sum)"]
def blockForm (T : QuadForm A r) (Q' : QuadForm A n') : QuadForm A (r + n') where
  coeff := blockMat T.coeff 0 0 Q'.coeff
  upper := by
    intro i j hij
    simp only [id] at hij
    induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j =>
        have hji : j < i := Fin.lt_def.mpr (Fin.lt_def.mp hij)
        simpa using T.upper hji
      | right j => exact absurd hij (not_lt.mpr (castAdd_le_natAdd i j))
    | right i =>
      induction j using Fin.addCases with
      | left j => simp
      | right j =>
        have hji : j < i := by
          have := Fin.lt_def.mp hij
          change r + j.val < r + i.val at this
          exact Fin.lt_def.mpr (by omega)
        simpa using Q'.upper hji

theorem blockForm_coeff (T : QuadForm A r) (Q' : QuadForm A n') :
    (blockForm T Q').coeff = blockMat T.coeff 0 0 Q'.coeff := rfl

theorem hessian_blockForm (T : QuadForm A r) (Q' : QuadForm A n') :
    (blockForm T Q').hessian = blockMat T.hessian 0 0 Q'.hessian := by
  rw [QuadForm.hessian, blockForm_coeff, blockMat_transpose, blockMat_add]
  simp [QuadForm.hessian]

theorem det_hessian_blockForm (T : QuadForm A r) (Q' : QuadForm A n') :
    (blockForm T Q').hessian.det = T.hessian.det * Q'.hessian.det := by
  rw [hessian_blockForm, det_blockMat_diag]

theorem map_blockForm {S : Type*} [CommRing S] (f : A →+* S) (T : QuadForm A r) (Q' : QuadForm A n') :
    (blockForm T Q').map f = blockForm (T.map f) (Q'.map f) := by
  ext1
  simp [QuadForm.map, blockForm_coeff, blockMat_map]

/-- $(T\perp Q')(x) = T(x_{<r}) + Q'(x_{\ge r})$ over any algebra. -/
theorem evalIn_blockForm (K : Type*) [CommRing K] [Algebra A K] (T : QuadForm A r) (Q' : QuadForm A n')
    (x : Fin (r + n') → K) :
    (blockForm T Q').evalIn K x = T.evalIn K (fun i => x (Fin.castAdd n' i)) + Q'.evalIn K (fun j => x (Fin.natAdd r j)) := by
  simp only [QuadForm.evalIn, Fin.sum_univ_add, blockForm_coeff, blockMat_castAdd_castAdd, blockMat_castAdd_natAdd,
    blockMat_natAdd_castAdd, blockMat_natAdd_natAdd, castAdd_le_natAdd, not_natAdd_le_castAdd,
    castAdd_le_castAdd_iff, natAdd_le_natAdd_iff, ite_true, ite_false, Matrix.zero_apply, map_zero,
    zero_mul, Finset.sum_const_zero, add_zero, zero_add]

/-- $(T\perp Q')\circ\mathrm{diag}(P, D) = (T\circ P)\perp(Q'\circ D)$. -/
theorem compMat_blockMat_diag (T : QuadForm A r) (Q' : QuadForm A n') (P : Matrix (Fin r) (Fin r) A)
    (D : Matrix (Fin n') (Fin n') A) :
    (blockForm T Q').compMat (blockMat P 0 0 D) = blockForm (T.compMat P) (Q'.compMat D) := by
  have hM : (blockMat P 0 0 D)ᵀ * (blockForm T Q').coeff * blockMat P 0 0 D =
      blockMat (Pᵀ * T.coeff * P) 0 0 (Dᵀ * Q'.coeff * D) := by
    rw [blockForm_coeff, blockMat_transpose, blockMat_mul, blockMat_mul]
    simp
  ext i j
  rw [coeff_compMat_eq, hM, blockForm_coeff]
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [blockMat_castAdd_castAdd]
      rw [coeff_compMat_eq]
      simp [castAdd_le_castAdd_iff, Fin.castAdd_inj]
    | right j =>
      simp [castAdd_le_natAdd, castAdd_ne_natAdd]
  | right i =>
    induction j using Fin.addCases with
    | left j => simp [not_natAdd_le_castAdd]
    | right j =>
      simp only [blockMat_natAdd_natAdd]
      rw [coeff_compMat_eq]
      simp [natAdd_le_natAdd_iff, Fin.natAdd_inj]

/-- **The standard frame** $E = \binom{1_r}{0} \in M_{(r+n')\times r}$. -/
def stdFrameMat : Matrix (Fin (r + n')) (Fin r) A := Matrix.of fun i j => if i = Fin.castAdd n' j then 1 else 0

/-- The standard frame as a vector in the frame coordinates. -/
def stdFrame : Fin (r + n') × Fin r → A := fun p => stdFrameMat p.1 p.2

theorem toMat_stdFrame : toMat (stdFrame (A := A) (r := r) (n' := n')) = stdFrameMat := by
  ext i j; rfl

@[simp] theorem stdFrameMat_castAdd (i j : Fin r) :
    (stdFrameMat : Matrix (Fin (r + n')) (Fin r) A) (Fin.castAdd n' i) j = (1 : Matrix (Fin r) (Fin r) A) i j := by
  simp [stdFrameMat, Matrix.one_apply, Fin.castAdd_inj]

@[simp] theorem stdFrameMat_natAdd (i : Fin n') (j : Fin r) :
    (stdFrameMat : Matrix (Fin (r + n')) (Fin r) A) (Fin.natAdd r i) j = 0 := by
  simp only [stdFrameMat, Matrix.of_apply, ite_eq_right_iff]
  exact fun h => absurd h.symm (castAdd_ne_natAdd j i)

/-- $(T \perp Q')\circ E = T$. -/
theorem compMat_stdFrameMat (T : QuadForm A r) (Q' : QuadForm A n') :
    (blockForm T Q').compMat stdFrameMat = T := by
  have hM : ((stdFrameMat : Matrix (Fin (r + n')) (Fin r) A)ᵀ * (blockForm T Q').coeff *
      (stdFrameMat : Matrix (Fin (r + n')) (Fin r) A) : Matrix (Fin r) (Fin r) A) = T.coeff := by
    ext a b
    simp [Matrix.mul_apply, stdFrameMat, Matrix.transpose_apply, blockForm_coeff]
  ext i j
  rw [coeff_compMat_eq, hM]
  by_cases hij : i ≤ j
  · by_cases he : i = j
    · subst he; simp
    · have hlt : i < j := lt_of_le_of_ne hij he
      simp [hij, he, T.upper hlt]
  · have : j < i := not_le.mp hij
    simp [hij, T.upper this]

theorem formF_stdFrame [IsDomain A] [IsDiscreteValuationRing A] (T : QuadForm A r) (Q' : QuadForm A n') :
    formF (blockForm T Q') (stdFrame (A := A)) = tc T := by
  rw [formF_eq_tc_iff, toMat_stdFrame, compMat_stdFrameMat]

/-- $\mathrm{diag}(1, D)\,E = E$. -/
theorem blockMat_one_mul_stdFrameMat (D : Matrix (Fin n') (Fin n') A) :
    blockMat (1 : Matrix (Fin r) (Fin r) A) 0 0 D * stdFrameMat = stdFrameMat := by
  ext i j
  refine (Matrix.mul_apply (M := blockMat 1 0 0 D) (N := stdFrameMat)).trans ?_
  simp only [Fin.sum_univ_add]
  induction i using Fin.addCases with
  | left i => simp [Matrix.one_apply]
  | right i => simp

/-- $\mathrm{diag}(1_r, \cdot)$ on matrices. -/
def blockHomB : Matrix (Fin n') (Fin n') A →* Matrix (Fin (r + n')) (Fin (r + n')) A where
  toFun D := blockMat 1 0 0 D
  map_one' := blockMat_one
  map_mul' D D' := by
    simp only [blockMat_mul]
    simp

/-- $\mathrm{diag}(1_r, \cdot)$ on invertible matrices. -/
def blockGLB : GL (Fin n') A →* GL (Fin (r + n')) A := Units.map (blockHomB (r := r))

@[simp] theorem blockGLB_val (g : GL (Fin n') A) :
    (blockGLB (r := r) g).val = blockMat 1 0 0 g.val := rfl

end Algebra

/-! ### The orthogonal groups: $O(Q') \hookrightarrow O(T\perp Q')$ and the stabilizer of $E$ -/

section Orth

variable {F : Type*} [Field F] {r n' : ℕ} (T : QuadForm F r) (Q' : QuadForm F n')

local notation "QB" => blockForm T Q'

/-- `mem_orthGroup` for an arbitrary field $F$ (unfolding of the definition). -/
theorem mem_orthGroup_iff' {n : ℕ} (Q : QuadForm F n) {R : Type*} [CommRing R] [Algebra F R] {g : GL (Fin n) R} :
    g ∈ orthGroup Q R ↔ g.valᵀ * Q.hessian.map (algebraMap F R) * g.val = Q.hessian.map (algebraMap F R) :=
  Iff.rfl

/-- **Value-preserving matrices are isometries** over any $F$-algebra $R$, for an arbitrary field $F$
(`mem_orthGroup_of_evalIn`). -/
theorem mem_orthGroup_of_evalIn' {n : ℕ} (Q : QuadForm F n) {R : Type*} [CommRing R] [Algebra F R] {ρ : GL (Fin n) R}
    (h : ∀ z, Q.evalIn R (ρ.val *ᵥ z) = Q.evalIn R z) : ρ ∈ orthGroup Q R := by
  rw [mem_orthGroup_iff']
  ext i j
  have hp := QuadForm.polar_eq_hessian R Q (ρ.val *ᵥ Pi.single i 1) (ρ.val *ᵥ Pi.single j 1)
  have hp' := QuadForm.polar_eq_hessian R Q (Pi.single i 1) (Pi.single j 1)
  rw [← mulVec_add, h, h, h, hp'] at hp
  have e1 : ∀ A : Matrix (Fin n) (Fin n) R, A i j = Pi.single i (1 : R) ⬝ᵥ (A *ᵥ Pi.single j 1) := by
    intro A; simp
  rw [e1 (ρ.valᵀ * _ * ρ.val), e1 (Q.hessian.map (algebraMap F R)), ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec, vecMul_transpose]
  exact hp.symm

theorem hessian_map_blockForm (R : Type*) [CommRing R] [Algebra F R] :
    (QB).hessian.map (algebraMap F R) = blockMat (T.hessian.map (algebraMap F R)) 0 0 (Q'.hessian.map (algebraMap F R)) := by
  rw [hessian_blockForm, blockMat_map]
  simp

/-- **The embedding $O(Q')(R) \to O(T\perp Q')(R)$**, $g \mapsto \mathrm{diag}(1_r, g)$, for an $F$-algebra $R$. Its image fixes $E$,
and over a field with $\det H_T \ne 0$ it is the whole stabilizer of $E$ (`exists_orthEmbB_eq`). -/
def orthEmbB (R : Type*) [CommRing R] [Algebra F R] : orthGroup Q' R →* orthGroup QB R where
  toFun g := ⟨blockGLB (g : GL (Fin n') R), by
    have hg := (mem_orthGroup_iff' Q').mp g.2
    rw [mem_orthGroup_iff', hessian_map_blockForm, blockGLB_val, blockMat_transpose, blockMat_mul, blockMat_mul]
    simp [hg]⟩
  map_one' := by ext1; simp
  map_mul' a b := by ext1; simp

@[simp] theorem orthEmbB_val (R : Type*) [CommRing R] [Algebra F R] (g : orthGroup Q' R) :
    (orthEmbB T Q' R g : GL (Fin (r + n')) R).val = blockMat 1 0 0 (g : GL (Fin n') R).val := rfl

theorem orthEmbB_injective (R : Type*) [CommRing R] [Algebra F R] : Function.Injective (orthEmbB T Q' R) := by
  intro a b h
  apply Subtype.ext; apply Units.ext
  have := congrArg (fun g : orthGroup QB R => (g : GL (Fin (r + n')) R).val) h
  simp only [orthEmbB_val] at this
  exact blockMat_injective_right this

theorem orthEmbB_mul_stdFrameMat (R : Type*) [CommRing R] [Algebra F R] (g : orthGroup Q' R) :
    (orthEmbB T Q' R g : GL (Fin (r + n')) R).val * stdFrameMat = stdFrameMat :=
  blockMat_one_mul_stdFrameMat _

/-- **The stabilizer of $E$ is $O(Q')$:** over a field $K \supseteq F$ in which $\det H_T \ne 0$, every $\gamma \in O(T\perp Q')(K)$
with $\gamma E = E$ is $\mathrm{diag}(1_r, g)$ with $g \in O(Q')(K)$. *Proof:* the first $r$ columns are $E$; the first $r$ rows:
$E^{\mathsf T}H\gamma = (\gamma E)^{\mathsf T}H\gamma = E^{\mathsf T}H$ and $E^{\mathsf T}H = (H_T\ \ 0)$, so $H_T\cdot(\text{first } r \text{ rows of }\gamma) =
(H_T\ \ 0)$, and $H_T$ is invertible. Then $\gamma^{\mathsf T}H\gamma = H$ restricts to $g^{\mathsf T}H'g = H'$. -/
@[kb "weil1982" "§3.4 (stabilizer of a frame) [unverified]"]
theorem exists_orthEmbB_eq (K : Type*) [Field K] [Algebra F K] (hT : (T.hessian.map (algebraMap F K)).det ≠ 0)
    (γ : orthGroup QB K) (hγ : (γ : GL (Fin (r + n')) K).val * stdFrameMat = stdFrameMat) :
    ∃ g : orthGroup Q' K, orthEmbB T Q' K g = γ := by
  set A := (γ : GL (Fin (r + n')) K).val with hA
  have hγo := (mem_orthGroup_iff' QB).mp γ.2
  rw [hessian_map_blockForm] at hγo
  change Aᵀ * _ * A = _ at hγo
  set HT := T.hessian.map (algebraMap F K) with hHT
  set H' := Q'.hessian.map (algebraMap F K) with hH'
  have hu : IsUnit HT := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hT)
  -- the columns
  have hcol : ∀ i j, A i (Fin.castAdd n' j) = (stdFrameMat : Matrix (Fin (r + n')) (Fin r) K) i j := by
    intro i j
    have := (Matrix.mul_apply (M := A) (N := (stdFrameMat : Matrix (Fin (r + n')) (Fin r) K))).symm.trans
      (congrFun (congrFun hγ i) j)
    simpa [stdFrameMat] using this
  set P : Matrix (Fin r) (Fin r) K := A.submatrix (Fin.castAdd n') (Fin.castAdd n')
  set Bm : Matrix (Fin r) (Fin n') K := A.submatrix (Fin.castAdd n') (Fin.natAdd r)
  set Cm : Matrix (Fin n') (Fin r) K := A.submatrix (Fin.natAdd r) (Fin.castAdd n')
  set D : Matrix (Fin n') (Fin n') K := A.submatrix (Fin.natAdd r) (Fin.natAdd r)
  have hP : P = 1 := by ext i j; simpa [P] using hcol (Fin.castAdd n' i) j
  have hC : Cm = 0 := by ext i j; simpa [Cm] using hcol (Fin.natAdd r i) j
  have hAb : A = blockMat P Bm Cm D := by
    ext i j
    induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j => simp [P]
      | right j => simp [Bm]
    | right i =>
      induction j using Fin.addCases with
      | left j => simp [Cm]
      | right j => simp [D]
  rw [hP, hC] at hAb
  rw [hAb] at hγo
  simp only [blockMat_transpose, blockMat_mul] at hγo
  simp at hγo
  obtain ⟨-, hB, -, hD⟩ := blockMat_inj hγo
  have hBm : Bm = 0 := by
    have h1 : Bm = (HT⁻¹ * HT) * Bm := by
      rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)]
      exact (Matrix.one_mul _).symm
    rw [h1, Matrix.mul_assoc, hB]
    simp
  rw [hBm] at hAb hD
  simp only [Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add] at hD
  have hdet : D.det ≠ 0 := by
    have h := (γ : GL (Fin (r + n')) K).isUnit.map Matrix.detMonoidHom
    have h' := h.ne_zero
    rw [Matrix.coe_detMonoidHom, ← hA, hAb, det_blockMat_diag, Matrix.det_one, one_mul] at h'
    exact h'
  let gGL := Matrix.GeneralLinearGroup.mkOfDetNeZero D hdet
  have hgo : gGL ∈ orthGroup Q' K := by
    rw [mem_orthGroup_iff']
    exact hD
  refine ⟨⟨gGL, hgo⟩, ?_⟩
  apply Subtype.ext; apply Units.ext
  rw [orthEmbB_val]
  exact hAb.symm

/-- **Witt transitivity on the frames of $T$:** over a field $K \supseteq F$ in which $\det H_{T\perp Q'} \ne 0$ and $\det H_T \ne 0$,
every $X \in K^{(r+n')\times r}$ with $(T\perp Q')\circ X = T$ is $\gamma E$ for some $\gamma \in O(T\perp Q')(K)$ (Witt's extension theorem
for families, `QuadraticForm.Witt.exists_isometryEquiv_of_family`, every characteristic; O'Meara 1963, 42:17, p. 98). The columns of
$X$ and of $E$ have the same values and polar values, and both families are linearly independent since $H_T$ is invertible. -/
@[kb "omeara1963" "§42F, 42:17, p. 98 (Witt's theorem)"]
theorem exists_orthGroup_mul_stdFrameMat (K : Type*) [Field K] [Algebra F K]
    (hQ : ((QB).hessian.map (algebraMap F K)).det ≠ 0) (hT : (T.hessian.map (algebraMap F K)).det ≠ 0)
    {X : Matrix (Fin (r + n')) (Fin r) K} (hX : ((QB).map (algebraMap F K)).compMat X = T.map (algebraMap F K)) :
    ∃ γ : orthGroup QB K, (γ : GL (Fin (r + n')) K).val * stdFrameMat = X := by
  set f := algebraMap F K with hf
  set E : Matrix (Fin (r + n')) (Fin r) K := stdFrameMat with hE
  have hHk : ((QB).map f).hessian = (QB).hessian.map f := by
    simp [QuadForm.hessian, QuadForm.map, Matrix.transpose_map, Matrix.map_add]
  have hTk : (T.map f).hessian = T.hessian.map f := by
    simp [QuadForm.hessian, QuadForm.map, Matrix.transpose_map, Matrix.map_add]
  have hEmap : E = (stdFrameMat : Matrix (Fin (r + n')) (Fin r) F).map f := by
    ext i j
    simp only [hE, stdFrameMat, Matrix.of_apply, Matrix.map_apply]
    split_ifs <;> simp
  have hEc : ((QB).map f).compMat E = T.map f := by
    rw [hEmap, QuadForm.map_compMat, compMat_stdFrameMat]
  have hevalmap : ∀ x : Fin (r + n') → K, ((QB).map f).eval x = (QB).evalIn K x := fun x => by
    simp [QuadForm.eval, QuadForm.evalIn, QuadForm.map]
    rfl
  -- facts about any frame `Y` with `QB ∘ Y = T`
  have key : ∀ Y : Matrix (Fin (r + n')) (Fin r) K, ((QB).map f).compMat Y = T.map f →
      (∀ i, (QB).evalIn K (fun l => Y l i) = (T.map f).coeff i i) ∧
      ((Yᵀ * (QB).hessian.map f * Y : Matrix (Fin r) (Fin r) K) = T.hessian.map f) ∧
      (∀ c, Y *ᵥ c = 0 → c = 0) := by
    intro Y hY
    have hG : (Yᵀ * (QB).hessian.map f * Y : Matrix (Fin r) (Fin r) K) = T.hessian.map f := by
      have := congrArg QuadForm.hessian hY
      rwa [QuadForm.hessian_compMat, hHk, hTk] at this
    refine ⟨fun i => ?_, hG, fun c hc => ?_⟩
    · have := congrArg (fun S : QuadForm K r => S.coeff i i) hY
      simp only [QuadForm.compMat_coeff, le_refl, ite_true] at this
      rw [← hevalmap, this]
    · refine Matrix.eq_zero_of_mulVec_eq_zero hT ?_
      have h2 : (T.hessian.map f) *ᵥ c = Yᵀ *ᵥ ((QB).hessian.map f *ᵥ (Y *ᵥ c)) := by
        rw [← hG, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      rw [h2, hc]
      simp
  obtain ⟨hEv, hEG, hEi⟩ := key E hEc
  obtain ⟨hXv, hXG, hXi⟩ := key X hX
  set Q : QuadraticForm K (Fin (r + n') → K) := (QB).toQuadraticFormIn K with hQdef
  have hQeq : Q = (((QB).map f).toQuadraticFormIn K) := by
    refine QuadraticMap.ext fun x => ?_
    rw [hQdef, QuadForm.toQuadraticFormIn_apply, QuadForm.toQuadraticFormIn_apply]
    exact (hevalmap x).symm
  have hnd : (QuadraticMap.polarBilin Q).Nondegenerate := by
    rw [hQeq]
    exact QuadForm.nondegenerate_polarBilin_toQuadraticFormIn K (Q := (QB).map f)
      (by unfold QuadForm.Nondegenerate; rw [hHk]; exact hQ)
  have hpol : ∀ Y : Matrix (Fin (r + n')) (Fin r) K, Yᵀ * (QB).hessian.map f * Y = T.hessian.map f →
      ∀ i j, QuadraticMap.polar Q (fun l => Y l i) (fun l => Y l j) = T.hessian.map f i j := by
    intro Y hY i j
    simp only [QuadraticMap.polar, hQdef, QuadForm.toQuadraticFormIn_apply]
    rw [QuadForm.polar_eq_hessian K (QB), ← QuadForm.transpose_mul_mul_apply, hY]
  have hsum : ∀ (Y : Matrix (Fin (r + n')) (Fin r) K) (c : Fin r → K),
      ∑ i, c i • (fun l => Y l i) = Y *ᵥ c := by
    intro Y c
    ext l
    simp [Matrix.mulVec, dotProduct, mul_comm]
  obtain ⟨ρ, hρ⟩ := QuadraticForm.Witt.exists_isometryEquiv_of_family Q
    (QuadraticForm.radical_eq_bot_of_nondegenerate Q hnd) (fun i => fun l => E l i) (fun i => fun l => X l i)
    (fun i => by
      simp only [hQdef, QuadForm.toQuadraticFormIn_apply]
      rw [hEv, hXv])
    (fun i j => by rw [hpol E hEG, hpol X hXG])
    (fun c => by
      rw [QuadraticForm.ker_polarBilin_eq_bot Q hnd, Submodule.mem_bot, Submodule.mem_bot, hsum, hsum]
      exact (Iff.intro (hEi c) fun h => by simp [h]).trans (Iff.intro (hXi c) fun h => by simp [h]).symm)
  set M := LinearMap.toMatrix' ρ.toLinearEquiv.toLinearMap with hM
  have hdet : M.det ≠ 0 := by
    rw [hM, LinearMap.det_toMatrix']
    exact (LinearEquiv.isUnit_det' ρ.toLinearEquiv).ne_zero
  let γ := Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet
  have hγ : γ ∈ orthGroup QB K := by
    refine mem_orthGroup_of_evalIn' QB fun z => ?_
    have h1 : γ.val *ᵥ z = ρ z := LinearMap.toMatrix'_mulVec _ z
    rw [h1]
    have := ρ.map_app z
    simpa only [hQdef, QuadForm.toQuadraticFormIn_apply] using this
  refine ⟨⟨γ, hγ⟩, ?_⟩
  refine Matrix.ext fun l i => ?_
  refine (Matrix.mul_apply (M := γ.val) (N := E)).trans ?_
  have h2 := congrFun (hρ i) l
  have h3 : M l (Fin.castAdd n' i) = ρ (fun l => E l i) l := by
    have hv : (fun l => E l i) = Pi.single (Fin.castAdd n' i) (1 : K) := by
      ext l
      simp [hE, stdFrameMat, Pi.single_apply]
    rw [hv, hM, LinearMap.toMatrix'_apply]
    simp
  simp only [hE, stdFrameMat, Matrix.of_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact (h3.trans h2)

end Orth

/-! ### Local and adelic compatibilities -/

section Adelic

variable {F : Type*} [Field F] [NumberField F] {r n' : ℕ} (T : QuadForm F r) (Q' : QuadForm F n')

local notation "QB" => blockForm T Q'

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

theorem blockMat_one_mulVec_append {K : Type*} [CommRing K] (D : Matrix (Fin n') (Fin n') K) (a : Fin r → K)
    (b : Fin n' → K) :
    blockMat (1 : Matrix (Fin r) (Fin r) K) 0 0 D *ᵥ (Fin.append a b : Fin (r + n') → K) = Fin.append a (D *ᵥ b) := by
  ext i
  induction i using Fin.addCases with
  | left i => simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.one_apply]
  | right i => simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add]

theorem append_inj' {α : Type*} {a a' : Fin r → α} {b b' : Fin n' → α}
    (h : (Fin.append a b : Fin (r + n') → α) = Fin.append a' b') : a = a' ∧ b = b' :=
  ⟨funext fun i => by simpa using congrFun h (Fin.castAdd n' i),
    funext fun j => by simpa using congrFun h (Fin.natAdd r j)⟩

theorem mem_std_append {t : Fin r → Fv} {x : Fin n' → Fv} :
    (Fin.append t x : Fin (r + n') → Fv) ∈ std v ↔ t ∈ std v ∧ x ∈ std v := by
  simp only [mem_ball, neg_zero, WithZero.exp_zero]
  constructor
  · intro h
    exact ⟨fun i => by simpa using h (Fin.castAdd n' i), fun j => by simpa using h (Fin.natAdd r j)⟩
  · rintro ⟨h1, h2⟩ i
    induction i using Fin.addCases with
    | left i => simpa using h1 i
    | right j => simpa using h2 j

theorem mem_locAct_blockGLB_std {g : GL (Fin n') Fv} {t : Fin r → Fv} {x : Fin n' → Fv} :
    (Fin.append t x : Fin (r + n') → Fv) ∈ locAct v (blockGLB (r := r) g) (std v) ↔
      t ∈ std v ∧ x ∈ locAct v g (std v) := by
  simp only [mem_locAct]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [← Fin.append_castAdd_natAdd (f := y), mem_std_append] at hy
    rw [← Fin.append_castAdd_natAdd (f := y), blockGLB_val, blockMat_one_mulVec_append] at hyx
    have hyx := append_inj' hyx
    exact ⟨hyx.1 ▸ hy.1, _, hy.2, hyx.2⟩
  · rintro ⟨ht, z, hz, hzx⟩
    refine ⟨Fin.append t z, (mem_std_append v).mpr ⟨ht, hz⟩, ?_⟩
    rw [blockGLB_val, blockMat_one_mulVec_append, hzx]

/-- **$\mathrm{diag}(1_r, g)$ preserves $\mathfrak o_\mathfrak p^{r+n'}$ iff $g$ preserves $\mathfrak o_\mathfrak p^{n'}$.** -/
theorem locAct_blockGLB_std_iff (g : GL (Fin n') Fv) :
    locAct v (blockGLB (r := r) g) (std v) = std v ↔ locAct v g (std v) = std v := by
  constructor
  · intro h
    ext x
    have := congrArg (fun M => (Fin.append (0 : Fin r → Fv) x : Fin (r + n') → Fv) ∈ M) h
    simp only [eq_iff_iff] at this
    rw [mem_locAct_blockGLB_std, mem_std_append] at this
    simpa using this
  · intro h
    ext y
    obtain ⟨t, x, rfl⟩ : ∃ (t : Fin r → Fv) (x : Fin n' → Fv), y = Fin.append t x :=
      ⟨_, _, Fin.append_castAdd_natAdd.symm⟩
    rw [mem_locAct_blockGLB_std, mem_std_append, h]

theorem mem_stdStab_orthEmbB_iff (g : orthGroup Q' Fv) :
    orthEmbB T Q' Fv g ∈ stdStab QB v ↔ g ∈ stdStab Q' v :=
  locAct_blockGLB_std_iff v (g : GL (Fin n') Fv)

variable {v}

/-- **The adelic embedding** $O(Q')(\mathbb A_f) \to O(T\perp Q')(\mathbb A_f)$, $(h_\mathfrak p) \mapsto (\mathrm{diag}(1_r, h_\mathfrak p))$. -/
def orthEmbBAf : OAf Q' →* OAf QB where
  toFun h := ⟨fun v => orthEmbB T Q' (v.adicCompletion F) (h v), by
    filter_upwards [h.2] with v hv
    exact (mem_stdStab_orthEmbB_iff T Q' v _).mpr hv⟩
  map_one' := by ext v : 1; exact map_one (orthEmbB T Q' _)
  map_mul' a b := by ext v : 1; exact map_mul (orthEmbB T Q' _) _ _

theorem orthEmbBAf_apply (h : OAf Q') (v : HeightOneSpectrum (𝓞 F)) :
    (orthEmbBAf T Q' h) v = orthEmbB T Q' (v.adicCompletion F) (h v) := rfl

theorem orthEmbBAf_injective : Function.Injective (orthEmbBAf T Q') := by
  intro a b h
  ext v : 1
  exact orthEmbB_injective T Q' _ (congrArg (fun x : OAf QB => x v) h)

/-- **Compatibility with the rational points.** -/
theorem orthEmbBAf_diagF (γ : orthGroup Q' F) :
    orthEmbBAf T Q' (diagF Q' γ) = diagF QB (orthEmbB T Q' F γ) := by
  ext v : 1
  apply Subtype.ext; apply Units.ext
  show blockMat 1 0 0 ((γ : GL (Fin n') F).val.map (algebraMap F (v.adicCompletion F))) =
    (blockMat 1 0 0 (γ : GL (Fin n') F).val).map (algebraMap F (v.adicCompletion F))
  rw [blockMat_map]
  simp

/-- **The preimage of $O(\hat{\mathcal O}_F^{r+n'})$ is $O(\hat{\mathcal O}_F^{n'})$.** -/
theorem comap_orthEmbBAf_locStab_intVec :
    (locStab QB (stdLat F (r + n'))).comap (orthEmbBAf T Q') = locStab Q' (stdLat F n') := by
  ext h
  rw [Subgroup.mem_comap, mem_locStab_intVec, mem_locStab_intVec]
  exact forall_congr' fun v => mem_stdStab_orthEmbB_iff T Q' v (h v)

end Adelic

end QuadFormsKB.Tamagawa.Frames
