/-
# Integral models of 2-adic block decompositions

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), (3), p. 263 (bibliography key `conwaysloane1988`); the block decompositions are those of *Sphere Packings, Lattices and Groups* Ch. 15,
§7.3–7.4 (`IsTwoSymbolOf`, Cassels' blocks `DyBlock`).

A 2-adic symbol of a form comes with a decomposition into Cassels' blocks $2^eux^2$, $2^e\cdot2xy$,
$2^e(2x^2+2xy+2y^2)$ in an arbitrary order. This file gives the integral Gram matrix `intMat D` of a list of blocks
(`(intMat D).map Int.cast = dyMat D`), shows that reordering the blocks only renames the variables (`Reidx`), and
splits a decomposition into its blocks of exponent $0$ and the rest: `intMat D` is, up to renaming the variables,
`blk 2 (intMat D₀) (intMat D')` with $D_0$ the blocks of exponent $0$ and $D'$ the other blocks with the exponent
lowered by one (`reidx_split`); the symbol of $D'$ is the shifted symbol (`blockSymbol_lower`).
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicDensity

set_option linter.unusedSectionVars false

namespace QuadFormsKB.ConwaySloane.Mass.Two

open Matrix QuadFormsKB.Cassels QuadFormsKB.ConwaySloane

/-! ### Renaming the variables -/

/-- $M$ is $N$ with the variables renamed. -/
def Reidx {m n : ℕ} (M : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ e : Fin m ≃ Fin n, M = N.submatrix e e

theorem Reidx.refl {m : ℕ} (M : Matrix (Fin m) (Fin m) ℤ) : Reidx M M := ⟨Equiv.refl _, by simp⟩

theorem Reidx.trans {m n k : ℕ} {M : Matrix (Fin m) (Fin m) ℤ} {N : Matrix (Fin n) (Fin n) ℤ}
    {P : Matrix (Fin k) (Fin k) ℤ} (h₁ : Reidx M N) (h₂ : Reidx N P) : Reidx M P := by
  obtain ⟨e, rfl⟩ := h₁; obtain ⟨e', rfl⟩ := h₂
  exact ⟨e.trans e', by ext; simp⟩

theorem Reidx.symm {m n : ℕ} {M : Matrix (Fin m) (Fin m) ℤ} {N : Matrix (Fin n) (Fin n) ℤ} (h : Reidx M N) :
    Reidx N M := by
  obtain ⟨e, rfl⟩ := h
  exact ⟨e.symm, by ext; simp⟩

theorem Reidx.smul {m n : ℕ} {M : Matrix (Fin m) (Fin m) ℤ} {N : Matrix (Fin n) (Fin n) ℤ} (h : Reidx M N)
    (c : ℤ) : Reidx (c • M) (c • N) := by
  obtain ⟨e, rfl⟩ := h
  exact ⟨e, by ext i j; simp only [submatrix_apply, Matrix.smul_apply, smul_eq_mul]⟩

theorem orthSumMat_apply {a b : ℕ} (F : Matrix (Fin a) (Fin a) ℤ) (G : Matrix (Fin b) (Fin b) ℤ)
    (x y : Fin a ⊕ Fin b) : orthSumMat F G (finSumFinEquiv x) (finSumFinEquiv y) = fromBlocks F 0 0 G x y := by
  simp [dyadic_orthSumMat_eq]

@[simp] theorem orthSumMat_cc {a b : ℕ} (F : Matrix (Fin a) (Fin a) ℤ) (G : Matrix (Fin b) (Fin b) ℤ)
    (x y : Fin a) : orthSumMat F G (Fin.castAdd b x) (Fin.castAdd b y) = F x y := by
  have := orthSumMat_apply F G (Sum.inl x) (Sum.inl y); simpa using this

@[simp] theorem orthSumMat_cn {a b : ℕ} (F : Matrix (Fin a) (Fin a) ℤ) (G : Matrix (Fin b) (Fin b) ℤ)
    (x : Fin a) (y : Fin b) : orthSumMat F G (Fin.castAdd b x) (Fin.natAdd a y) = 0 := by
  have := orthSumMat_apply F G (Sum.inl x) (Sum.inr y); simpa using this

@[simp] theorem orthSumMat_nc {a b : ℕ} (F : Matrix (Fin a) (Fin a) ℤ) (G : Matrix (Fin b) (Fin b) ℤ)
    (x : Fin b) (y : Fin a) : orthSumMat F G (Fin.natAdd a x) (Fin.castAdd b y) = 0 := by
  have := orthSumMat_apply F G (Sum.inr x) (Sum.inl y); simpa using this

@[simp] theorem orthSumMat_nn {a b : ℕ} (F : Matrix (Fin a) (Fin a) ℤ) (G : Matrix (Fin b) (Fin b) ℤ)
    (x y : Fin b) : orthSumMat F G (Fin.natAdd a x) (Fin.natAdd a y) = G x y := by
  have := orthSumMat_apply F G (Sum.inr x) (Sum.inr y); simpa using this

/-- An orthogonal sum is determined by its values on `finSumFinEquiv`. -/
theorem orthSum_ext {a b c : ℕ} {M : Matrix (Fin (a + b)) (Fin (a + b)) ℤ}
    {N : Matrix (Fin c) (Fin c) ℤ} (e : Fin a ⊕ Fin b ≃ Fin c)
    (h : ∀ x y, M (finSumFinEquiv x) (finSumFinEquiv y) = N (e x) (e y)) :
    M = N.submatrix (finSumFinEquiv.symm.trans e) (finSumFinEquiv.symm.trans e) := by
  ext i j
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
  simp [h]

theorem reidx_orthSum_right {a b c : ℕ} (F : Matrix (Fin a) (Fin a) ℤ) {G : Matrix (Fin b) (Fin b) ℤ}
    {G' : Matrix (Fin c) (Fin c) ℤ} (h : Reidx G G') : Reidx (orthSumMat F G) (orthSumMat F G') := by
  obtain ⟨e, rfl⟩ := h
  refine ⟨_, orthSum_ext ((Equiv.sumCongr (Equiv.refl _) e).trans finSumFinEquiv) fun x y => ?_⟩
  rw [orthSumMat_apply]
  simp only [Equiv.trans_apply]
  rw [orthSumMat_apply]
  rcases x with x | x <;> rcases y with y | y <;> simp

theorem reidx_orthSum_left {a b c : ℕ} {F : Matrix (Fin a) (Fin a) ℤ} {F' : Matrix (Fin c) (Fin c) ℤ}
    (G : Matrix (Fin b) (Fin b) ℤ) (h : Reidx F F') : Reidx (orthSumMat F G) (orthSumMat F' G) := by
  obtain ⟨e, rfl⟩ := h
  refine ⟨_, orthSum_ext ((Equiv.sumCongr e (Equiv.refl _)).trans finSumFinEquiv) fun x y => ?_⟩
  rw [orthSumMat_apply]
  simp only [Equiv.trans_apply]
  rw [orthSumMat_apply]
  rcases x with x | x <;> rcases y with y | y <;> simp

theorem reidx_orthSum_zero {b : ℕ} (F : Matrix (Fin 0) (Fin 0) ℤ) (G : Matrix (Fin b) (Fin b) ℤ) :
    Reidx (orthSumMat F G) G := by
  refine ⟨_, orthSum_ext ((Equiv.sumCongr (Equiv.refl _) (Equiv.refl _)).trans
    ((Equiv.emptySum (Fin 0) (Fin b)))) fun x y => ?_⟩
  rw [orthSumMat_apply]
  rcases x with x | x
  · exact x.elim0
  rcases y with y | y
  · exact y.elim0
  rfl

theorem reidx_orthSum_assoc {a b c : ℕ} (F : Matrix (Fin a) (Fin a) ℤ) (G : Matrix (Fin b) (Fin b) ℤ)
    (H : Matrix (Fin c) (Fin c) ℤ) : Reidx (orthSumMat F (orthSumMat G H)) (orthSumMat (orthSumMat F G) H) := by
  let e : Fin a ⊕ Fin (b + c) ≃ Fin (a + b + c) :=
    (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm).trans ((Equiv.sumAssoc _ _ _).symm.trans
      ((Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv))
  refine ⟨_, orthSum_ext e fun x y => ?_⟩
  rw [orthSumMat_apply]
  rcases x with x | x
  · rcases y with y | y
    · simp [e, orthSumMat_apply]
    · obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective y
      rcases y with y | y <;> simp [e, orthSumMat_apply]
  · obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
    rcases y with y | y
    · rcases x with x | x <;> simp [e, orthSumMat_apply]
    · obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective y
      rcases x with x | x <;> rcases y with y | y <;> simp [e, orthSumMat_apply]

theorem reidx_orthSum_swap {a b c : ℕ} (F : Matrix (Fin a) (Fin a) ℤ) (G : Matrix (Fin b) (Fin b) ℤ)
    (H : Matrix (Fin c) (Fin c) ℤ) : Reidx (orthSumMat F (orthSumMat G H)) (orthSumMat G (orthSumMat F H)) := by
  let e : Fin a ⊕ Fin (b + c) ≃ Fin (b + (a + c)) :=
    (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm).trans ((Equiv.sumAssoc _ _ _).symm.trans
      ((Equiv.sumCongr (Equiv.sumComm _ _) (Equiv.refl _)).trans ((Equiv.sumAssoc _ _ _).trans
        ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv))))
  refine ⟨_, orthSum_ext e fun x y => ?_⟩
  rw [orthSumMat_apply]
  rcases x with x | x
  · rcases y with y | y
    · simp [e, orthSumMat_apply]
    · obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective y
      rcases y with y | y <;> simp [e, orthSumMat_apply]
  · obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
    rcases y with y | y
    · rcases x with x | x <;> simp [e, orthSumMat_apply]
    · obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective y
      rcases x with x | x <;> rcases y with y | y <;> simp [e, orthSumMat_apply]

/-! ### The integral Gram matrix of a block list -/

/-- The integral Gram matrix of a block: $(2^eu)$, $2^e\begin{pmatrix}0&1\\1&0\end{pmatrix}$,
$2^e\begin{pmatrix}2&1\\1&2\end{pmatrix}$ (exponent read as a natural number). -/
def bInt : (b : DyBlock) → Matrix (Fin b.dim) (Fin b.dim) ℤ
  | .sq e u => !![2 ^ e.toNat * u]
  | .hyp e => (2 ^ e.toNat : ℤ) • !![0, 1; 1, 0]
  | .ell e => (2 ^ e.toNat : ℤ) • !![2, 1; 1, 2]

/-- The integral Gram matrix of an orthogonal sum of blocks, in the order of the list (as `dyMat`). -/
def intMat : (D : List DyBlock) → Matrix (Fin (dyDim D)) (Fin (dyDim D)) ℤ
  | [] => 0
  | b :: D => orthSumMat (bInt b) (intMat D)

theorem orthSumMat_map {K L : Type*} [Zero K] [Zero L] {a b : ℕ} (f : K → L) (hf : f 0 = 0)
    (F : Matrix (Fin a) (Fin a) K) (G : Matrix (Fin b) (Fin b) K) :
    (orthSumMat F G).map f = orthSumMat (F.map f) (G.map f) := by
  rw [dyadic_orthSumMat_eq, dyadic_orthSumMat_eq, ← Matrix.submatrix_map, fromBlocks_map,
    Matrix.map_zero _ hf, Matrix.map_zero _ hf]

theorem zpow2 {e : ℤ} (he : 0 ≤ e) : (2 : ℚ_[2]) ^ e = (2 : ℚ_[2]) ^ e.toNat := by
  conv_lhs => rw [← Int.toNat_of_nonneg he]
  exact zpow_natCast _ _

theorem bInt_map (b : DyBlock) (he : 0 ≤ blockExp b) : (bInt b).map (Int.cast : ℤ → ℚ_[2]) = b.mat := by
  cases b with
  | sq e u =>
    simp only [blockExp] at he
    show (!![2 ^ e.toNat * u] : Matrix (Fin 1) (Fin 1) ℤ).map (Int.cast : ℤ → ℚ_[2]) =
      !![(2 : ℚ_[2]) ^ e * u]
    ext i j; fin_cases i; fin_cases j; simp [zpow2 he]
  | hyp e =>
    simp only [blockExp] at he
    show ((2 ^ e.toNat : ℤ) • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → ℚ_[2]) =
      (2 : ℚ_[2]) ^ e • !![0, 1; 1, 0]
    ext i j; fin_cases i <;> fin_cases j <;> simp [zpow2 he]
  | ell e =>
    simp only [blockExp] at he
    show ((2 ^ e.toNat : ℤ) • (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → ℚ_[2]) =
      (2 : ℚ_[2]) ^ e • !![2, 1; 1, 2]
    ext i j; fin_cases i <;> fin_cases j <;> simp [zpow2 he]

theorem intMat_map : ∀ (D : List DyBlock), (∀ b ∈ D, 0 ≤ blockExp b) →
    (intMat D).map (Int.cast : ℤ → ℚ_[2]) = dyMat D
  | [], _ => by ext i; exact i.elim0
  | b :: D, h => by
    have e1 := orthSumMat_map (Int.cast : ℤ → ℚ_[2]) Int.cast_zero (bInt b) (intMat D)
    rw [bInt_map b (h b (by simp)), intMat_map D fun c hc => h c (by simp [hc])] at e1
    exact e1

/-- **Reordering the blocks renames the variables.** -/
theorem reidx_of_perm {D D' : List DyBlock} (h : D.Perm D') : Reidx (intMat D) (intMat D') := by
  induction h with
  | nil => exact Reidx.refl _
  | cons b _ ih => exact reidx_orthSum_right _ ih
  | swap b c l => exact (reidx_orthSum_swap (bInt c) (bInt b) (intMat l))
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem reidx_append : ∀ (L₁ L₂ : List DyBlock), Reidx (intMat (L₁ ++ L₂)) (orthSumMat (intMat L₁) (intMat L₂))
  | [], L₂ => (reidx_orthSum_zero (intMat []) (intMat L₂)).symm
  | b :: L₁, L₂ =>
    (reidx_orthSum_right (bInt b) (reidx_append L₁ L₂)).trans (reidx_orthSum_assoc _ _ _)

/-- Lowering the exponent of a block by one. -/
def lowerB : DyBlock → DyBlock
  | .sq e u => .sq (e - 1) u
  | .hyp e => .hyp (e - 1)
  | .ell e => .ell (e - 1)

theorem orthSumMat_smul {a b : ℕ} (c : ℤ) (F : Matrix (Fin a) (Fin a) ℤ) (G : Matrix (Fin b) (Fin b) ℤ) :
    orthSumMat (c • F) (c • G) = c • orthSumMat F G := by
  ext i j
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
  rw [Matrix.smul_apply, orthSumMat_apply, orthSumMat_apply]
  rcases x with x | x <;> rcases y with y | y <;>
    simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.smul_apply,
      smul_eq_mul, Matrix.zero_apply, mul_zero]

theorem reidx_bInt_lower (b : DyBlock) (h : 1 ≤ blockExp b) : Reidx (bInt b) ((2 : ℤ) • bInt (lowerB b)) := by
  cases b with
  | sq e u =>
    refine ⟨Equiv.refl _, ?_⟩
    simp only [blockExp] at h
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, e = k + 1 := ⟨(e - 1).toNat, by omega⟩
    show (!![2 ^ ((k : ℤ) + 1).toNat * u] : Matrix (Fin 1) (Fin 1) ℤ) =
      (2 : ℤ) • !![2 ^ ((k : ℤ) + 1 - 1).toNat * u]
    ext i j; fin_cases i; fin_cases j
    simp [pow_succ]; ring
  | hyp e =>
    refine ⟨Equiv.refl _, ?_⟩
    simp only [blockExp] at h
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, e = k + 1 := ⟨(e - 1).toNat, by omega⟩
    show (2 ^ ((k : ℤ) + 1).toNat : ℤ) • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) =
      (2 : ℤ) • ((2 ^ ((k : ℤ) + 1 - 1).toNat : ℤ) • !![0, 1; 1, 0])
    rw [smul_smul]; congr 1
    rw [show ((k : ℤ) + 1).toNat = k + 1 by omega, show ((k : ℤ) + 1 - 1).toNat = k by omega, pow_succ]; ring
  | ell e =>
    refine ⟨Equiv.refl _, ?_⟩
    simp only [blockExp] at h
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, e = k + 1 := ⟨(e - 1).toNat, by omega⟩
    show (2 ^ ((k : ℤ) + 1).toNat : ℤ) • (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ) =
      (2 : ℤ) • ((2 ^ ((k : ℤ) + 1 - 1).toNat : ℤ) • !![2, 1; 1, 2])
    rw [smul_smul]; congr 1
    rw [show ((k : ℤ) + 1).toNat = k + 1 by omega, show ((k : ℤ) + 1 - 1).toNat = k by omega, pow_succ]; ring

theorem reidx_lower : ∀ (D : List DyBlock), (∀ b ∈ D, 1 ≤ blockExp b) →
    Reidx (intMat D) ((2 : ℤ) • intMat (D.map lowerB))
  | [], _ => ⟨Equiv.refl _, by ext i; exact i.elim0⟩
  | b :: D, h => by
    have h1 := reidx_bInt_lower b (h b (by simp))
    have h2 := reidx_lower D fun c hc => h c (by simp [hc])
    refine ((reidx_orthSum_left _ h1).trans (reidx_orthSum_right _ h2)).trans ?_
    rw [orthSumMat_smul]
    exact Reidx.refl _

/-- The blocks of exponent $0$. -/
def low (D : List DyBlock) : List DyBlock := D.filter fun b => blockExp b = 0

/-- The blocks of positive exponent, lowered by one. -/
def high (D : List DyBlock) : List DyBlock := (D.filter fun b => !decide (blockExp b = 0)).map lowerB

/-- **Splitting off the blocks of exponent $0$**: `intMat D` is `blk 2 (intMat (low D)) (intMat (high D))` up to
renaming the variables. -/
theorem reidx_split (D : List DyBlock) (h : ∀ b ∈ D, 0 ≤ blockExp b) :
    Reidx (intMat D) (blk 2 (intMat (low D)) (intMat (high D))) := by
  have hp := (List.filter_append_perm (fun b => decide (blockExp b = 0)) D).symm
  refine (reidx_of_perm hp).trans ((reidx_append _ _).trans ?_)
  have hpos : ∀ b ∈ D.filter (fun b => !decide (blockExp b = 0)), 1 ≤ blockExp b := by
    intro b hb
    simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hb
    have := h b hb.1
    omega
  refine (reidx_orthSum_right _ (reidx_lower _ hpos)).trans ?_
  rw [blk, ← dyadic_orthSumMat_eq]
  exact ⟨Equiv.refl _, rfl⟩

end QuadFormsKB.ConwaySloane.Mass.Two
