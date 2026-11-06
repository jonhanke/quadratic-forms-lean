/-
# Cancelling the unimodular constituent over $\mathbb Z_2$

J. W. S. Cassels, *Rational Quadratic Forms*, Ch. 8, Lemma 4.2 and its Corollary, pp. 120–122 (bibliography key
`cassels1978`), applied to the splitting step of formula (3) of J. H. Conway and N. J. A. Sloane, "Low-dimensional
lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419** (1988), p. 263 (`conwaysloane1988`).

**Proves** `zpEquiv_cancel_dyMat`: if $U$ is an orthogonal sum of blocks $u x^2$, $2xy$, $2x^2 + 2xy + 2y^2$ (exponent
$0$, so $U$ is unimodular) and $G_1$, $G_2$ are classically integral forms with
no unit on the diagonal (not properly primitive), then
$$U \perp G_1 \sim U \perp G_2 \implies G_1 \sim G_2 \quad (\mathbb Z_2\text{-equivalence}).$$
The proof cancels one block at a time with Cassels' Lemma 4.2 (`zpEquiv_cancel_unit`) for the blocks $u x^2$ and its
Corollary (`zpEquiv_cancel_binary`) for the binary blocks; a binary block is cancelled last (after renaming the
variables), because the Corollary needs the forms behind it to be not properly primitive.

In the splitting $U \perp 2B$ of formula (3), $G_1 = 2B$ and $G_2$ the perturbed form $2B + 4BWU^{-1}W^{\mathsf T}B$ both
have all entries even, so the perturbed second block never has to be classified. Indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicMain
import QuadFormsKB.Literature.Cassels.Ch8.DyadicCancel

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace QuadFormsKB.ConwaySloane.Mass.Two

open Matrix QuadFormsKB.Cassels QuadFormsKB.ConwaySloane

/-! ### Entries of an orthogonal sum -/

theorem orthSum_entry_cases {a b : ℕ} (F : Matrix (Fin a) (Fin a) ℚ_[2]) (G : Matrix (Fin b) (Fin b) ℚ_[2])
    (i j : Fin (a + b)) :
    orthSumMat F G i j = 0 ∨ (∃ i' j', orthSumMat F G i j = F i' j') ∨ ∃ i' j', orthSumMat F G i j = G i' j' := by
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j => exact Or.inr (Or.inl ⟨i, j, dyadic_orthSumMat_cc F G i j⟩)
    | right j => exact Or.inl (dyadic_orthSumMat_cn F G i j)
  | right i =>
    induction j using Fin.addCases with
    | left j => exact Or.inl (dyadic_orthSumMat_nc F G i j)
    | right j => exact Or.inr (Or.inr ⟨i, j, dyadic_orthSumMat_nn F G i j⟩)

theorem isClassIntegral_orthSum {a b : ℕ} {F : Matrix (Fin a) (Fin a) ℚ_[2]} {G : Matrix (Fin b) (Fin b) ℚ_[2]}
    (hF : IsClassIntegral F) (hG : IsClassIntegral G) : IsClassIntegral (orthSumMat F G) := by
  intro i j
  rcases orthSum_entry_cases F G i j with h | ⟨i', j', h⟩ | ⟨i', j', h⟩
  · rw [h, norm_zero]; exact zero_le_one
  · rw [h]; exact hF i' j'
  · rw [h]; exact hG i' j'

theorem orthSum_diag {a b : ℕ} (F : Matrix (Fin a) (Fin a) ℚ_[2]) (G : Matrix (Fin b) (Fin b) ℚ_[2])
    (j : Fin (a + b)) : (∃ j', orthSumMat F G j j = F j' j') ∨ ∃ j', orthSumMat F G j j = G j' j' := by
  induction j using Fin.addCases with
  | left j => exact Or.inl ⟨j, dyadic_orthSumMat_cc F G j j⟩
  | right j => exact Or.inr ⟨j, dyadic_orthSumMat_nn F G j j⟩

/-- An integral form has a unit on the diagonal iff it is properly primitive. -/
theorem isProperlyPrimitive_iff {m : ℕ} {G : Matrix (Fin m) (Fin m) ℚ_[2]} (hG : IsClassIntegral G) :
    IsProperlyPrimitive G ↔ ∃ j, ‖G j j‖ = 1 :=
  ⟨fun h => h.2, fun ⟨j, hj⟩ => ⟨⟨hG, j, j, hj⟩, j, hj⟩⟩

/-- For integral $G$ that is not properly primitive, $F \perp G$ is properly primitive iff $F$ has a unit on the
diagonal. -/
theorem isProperlyPrimitive_orthSum_iff {a b : ℕ} {F : Matrix (Fin a) (Fin a) ℚ_[2]}
    {G : Matrix (Fin b) (Fin b) ℚ_[2]} (hF : IsClassIntegral F) (hG : IsClassIntegral G)
    (hpp : ¬ IsProperlyPrimitive G) : IsProperlyPrimitive (orthSumMat F G) ↔ ∃ j, ‖F j j‖ = 1 := by
  rw [isProperlyPrimitive_iff (isClassIntegral_orthSum hF hG)]
  rw [isProperlyPrimitive_iff hG] at hpp
  constructor
  · rintro ⟨j, hj⟩
    rcases orthSum_diag F G j with ⟨j', h⟩ | ⟨j', h⟩
    · exact ⟨j', h ▸ hj⟩
    · exact absurd ⟨j', h ▸ hj⟩ hpp
  · rintro ⟨j, hj⟩
    exact ⟨Fin.castAdd b j, by rw [dyadic_orthSumMat_cc]; exact hj⟩

/-! ### The blocks of exponent $0$ -/

theorem norm_odd_int {u : ℤ} (hu : ¬ 2 ∣ u) : ‖(u : ℚ_[2])‖ = 1 :=
  le_antisymm (Padic.norm_int_le_one u) (not_lt.mp fun h => hu (by exact_mod_cast Padic.norm_intCast_lt_one_iff.mp h))

theorem valid_odd {u : ℤ} (h : u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) : ¬ 2 ∣ u := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem mat_sq_zero (u : ℤ) : (DyBlock.sq 0 u).mat = !![(u : ℚ_[2])] := by
  show !![(2 : ℚ_[2]) ^ (0 : ℤ) * u] = _
  simp

theorem mat_hyp_zero : (DyBlock.hyp 0).mat = !![0, 1; 1, 0] := by
  show (2 : ℚ_[2]) ^ (0 : ℤ) • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2]) = _
  simp

theorem mat_ell_zero : (DyBlock.ell 0).mat = !![2, 1; 1, 2] := by
  show (2 : ℚ_[2]) ^ (0 : ℤ) • (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ_[2]) = _
  simp

theorem mat_transpose_zero (b : DyBlock) (he : blockExp b = 0) : b.matᵀ = b.mat := by
  cases b with
  | sq e u => obtain rfl : e = 0 := he; rw [mat_sq_zero]; ext i j; fin_cases i; fin_cases j; rfl
  | hyp e => obtain rfl : e = 0 := he; rw [mat_hyp_zero]; ext i j; fin_cases i <;> fin_cases j <;> rfl
  | ell e => obtain rfl : e = 0 := he; rw [mat_ell_zero]; ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem integral_sq {u : ℤ} (hu : ¬ 2 ∣ u) : IsClassIntegral (!![(u : ℚ_[2])] : Matrix (Fin 1) (Fin 1) ℚ_[2]) := by
  intro i j; fin_cases i; fin_cases j; simpa using (norm_odd_int hu).le

theorem integral_hyp : IsClassIntegral (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2]) := by
  intro i j; fin_cases i <;> fin_cases j <;> simp

theorem integral_ell : IsClassIntegral (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ_[2]) := by
  have h2 : ‖(2 : ℚ_[2])‖ ≤ 1 := by rw [dyadic_norm_two_q]; norm_num
  intro i j; fin_cases i <;> fin_cases j <;> simp [h2]

theorem diag_hyp (j : Fin 2) : ‖(!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2]) j j‖ < 1 := by
  fin_cases j <;> simp

theorem diag_ell (j : Fin 2) : ‖(!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ_[2]) j j‖ < 1 := by
  have h2 : ‖(2 : ℚ_[2])‖ < 1 := by rw [dyadic_norm_two_q]; norm_num
  fin_cases j <;> simp [h2]

theorem mat_integral_zero (b : DyBlock) (hv : b.Valid) (he : blockExp b = 0) : IsClassIntegral b.mat := by
  cases b with
  | sq e u => obtain rfl : e = 0 := he; rw [mat_sq_zero]; exact integral_sq (valid_odd hv)
  | hyp e => obtain rfl : e = 0 := he; rw [mat_hyp_zero]; exact integral_hyp
  | ell e => obtain rfl : e = 0 := he; rw [mat_ell_zero]; exact integral_ell

theorem mat_diag_lt_zero (b : DyBlock) (he : blockExp b = 0) (hs : ¬ IsSqBlock b) (j : Fin b.dim) :
    ‖b.mat j j‖ < 1 := by
  cases b with
  | sq e u => exact absurd trivial hs
  | hyp e =>
    obtain rfl : e = 0 := he
    have := diag_hyp j
    rwa [← mat_hyp_zero] at this
  | ell e =>
    obtain rfl : e = 0 := he
    have := diag_ell j
    rwa [← mat_ell_zero] at this

theorem dyMat_transpose_zero : ∀ D : List DyBlock, (∀ b ∈ D, blockExp b = 0) → (dyMat D)ᵀ = dyMat D
  | [], _ => by ext i; exact i.elim0
  | b :: D, h => by
    show (orthSumMat b.mat (dyMat D))ᵀ = orthSumMat b.mat (dyMat D)
    rw [Lemma42.orthSumMat_transpose', mat_transpose_zero b (h b (by simp)),
      dyMat_transpose_zero D fun c hc => h c (by simp [hc])]

theorem dyMat_integral_zero : ∀ D : List DyBlock, (∀ b ∈ D, b.Valid) → (∀ b ∈ D, blockExp b = 0) →
    IsClassIntegral (dyMat D)
  | [], _, _ => fun i => i.elim0
  | b :: D, hv, h => isClassIntegral_orthSum (mat_integral_zero b (hv b (by simp)) (h b (by simp)))
      (dyMat_integral_zero D (fun c hc => hv c (by simp [hc])) fun c hc => h c (by simp [hc]))

theorem dyMat_diag_lt_zero : ∀ D : List DyBlock, (∀ b ∈ D, blockExp b = 0) → (∀ b ∈ D, ¬ IsSqBlock b) →
    ∀ j, ‖dyMat D j j‖ < 1
  | [], _, _ => fun j => j.elim0
  | b :: D, h, hs => fun j => by
    show ‖orthSumMat b.mat (dyMat D) j j‖ < 1
    rcases orthSum_diag b.mat (dyMat D) j with ⟨j', e⟩ | ⟨j', e⟩
    · rw [e]; exact mat_diag_lt_zero b (h b (by simp)) (hs b (by simp)) j'
    · rw [e]; exact dyMat_diag_lt_zero D (fun c hc => h c (by simp [hc])) (fun c hc => hs c (by simp [hc])) j'

/-! ### Renaming the variables -/

theorem orthSumMat_apply' {K : Type*} [Zero K] {a b : ℕ} (F : Matrix (Fin a) (Fin a) K)
    (G : Matrix (Fin b) (Fin b) K) (x y : Fin a ⊕ Fin b) :
    orthSumMat F G (finSumFinEquiv x) (finSumFinEquiv y) = fromBlocks F 0 0 G x y := by
  simp [dyadic_orthSumMat_eq]

theorem orthSumG_cc {K : Type*} [Zero K] {a b : ℕ} (F : Matrix (Fin a) (Fin a) K) (G : Matrix (Fin b) (Fin b) K)
    (x y : Fin a) : orthSumMat F G (Fin.castAdd b x) (Fin.castAdd b y) = F x y := by
  have := orthSumMat_apply' F G (Sum.inl x) (Sum.inl y); simpa using this

theorem orthSumG_cn {K : Type*} [Zero K] {a b : ℕ} (F : Matrix (Fin a) (Fin a) K) (G : Matrix (Fin b) (Fin b) K)
    (x : Fin a) (y : Fin b) : orthSumMat F G (Fin.castAdd b x) (Fin.natAdd a y) = 0 := by
  have := orthSumMat_apply' F G (Sum.inl x) (Sum.inr y); simpa using this

theorem orthSumG_nc {K : Type*} [Zero K] {a b : ℕ} (F : Matrix (Fin a) (Fin a) K) (G : Matrix (Fin b) (Fin b) K)
    (x : Fin b) (y : Fin a) : orthSumMat F G (Fin.natAdd a x) (Fin.castAdd b y) = 0 := by
  have := orthSumMat_apply' F G (Sum.inr x) (Sum.inl y); simpa using this

theorem orthSumG_nn {K : Type*} [Zero K] {a b : ℕ} (F : Matrix (Fin a) (Fin a) K) (G : Matrix (Fin b) (Fin b) K)
    (x y : Fin b) : orthSumMat F G (Fin.natAdd a x) (Fin.natAdd a y) = G x y := by
  have := orthSumMat_apply' F G (Sum.inr x) (Sum.inr y); simpa using this

/-- The renaming of the variables that swaps the first two summands. -/
def swapE (a b c : ℕ) : Fin a ⊕ Fin (b + c) ≃ Fin (b + (a + c)) :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm).trans ((Equiv.sumAssoc _ _ _).symm.trans
    ((Equiv.sumCongr (Equiv.sumComm _ _) (Equiv.refl _)).trans ((Equiv.sumAssoc _ _ _).trans
      ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv))))

/-- Swapping the first two summands of $F \perp (G \perp H)$ renames the variables. -/
theorem orthSumMat_swap {K : Type*} [Zero K] {a b c : ℕ} (F : Matrix (Fin a) (Fin a) K)
    (G : Matrix (Fin b) (Fin b) K) (H : Matrix (Fin c) (Fin c) K) :
    orthSumMat F (orthSumMat G H) = (orthSumMat G (orthSumMat F H)).submatrix
      (finSumFinEquiv.symm.trans (swapE a b c)) (finSumFinEquiv.symm.trans (swapE a b c)) := by
  set e := swapE a b c with he
  ext i j
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
  simp only [submatrix_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [orthSumMat_apply']
  rcases x with x | x
  · rcases y with y | y
    · simp [e, swapE, orthSumMat_apply', orthSumG_cc, orthSumG_cn, orthSumG_nc, orthSumG_nn]
    · obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective y
      rcases y with y | y <;> simp [e, swapE, orthSumMat_apply', orthSumG_cc, orthSumG_cn, orthSumG_nc, orthSumG_nn]
  · obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
    rcases y with y | y
    · rcases x with x | x <;> simp [e, swapE, orthSumMat_apply', orthSumG_cc, orthSumG_cn, orthSumG_nc, orthSumG_nn]
    · obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective y
      rcases x with x | x <;> rcases y with y | y <;> simp [e, swapE, orthSumMat_apply', orthSumG_cc, orthSumG_cn, orthSumG_nc, orthSumG_nn]

/-- $\mathbb Z_2$-equivalence is compatible with renaming the variables. -/
theorem zpEquiv_submatrix {k k' : ℕ} (e : Fin k ≃ Fin k') {F G : Matrix (Fin k') (Fin k') ℚ_[2]}
    (h : ZpEquiv F G) : ZpEquiv (F.submatrix e e) (G.submatrix e e) := by
  obtain ⟨T, rfl⟩ := h
  refine ⟨Units.map (Matrix.reindexAlgEquiv ℤ_[2] ℤ_[2] e.symm).toMonoidHom T, ?_⟩
  have hT : (Units.map (Matrix.reindexAlgEquiv ℤ_[2] ℤ_[2] e.symm).toMonoidHom T).val.map PadicInt.Coe.ringHom =
      (T.val.map PadicInt.Coe.ringHom).submatrix e e := by
    ext i j; simp [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  rw [hT, transpose_submatrix, ← submatrix_mul _ _ _ _ _ e.bijective, ← submatrix_mul _ _ _ _ _ e.bijective]

theorem zpEquiv_of_submatrix {k k' : ℕ} (e : Fin k ≃ Fin k') {F G : Matrix (Fin k') (Fin k') ℚ_[2]}
    (h : ZpEquiv (F.submatrix e e) (G.submatrix e e)) : ZpEquiv F G := by
  have := zpEquiv_submatrix e.symm h
  simpa using this

/-! ### Cancellation -/

theorem zpEquiv_orthSum_assoc {a b c : ℕ} (P : Matrix (Fin a) (Fin a) ℚ_[2]) (Q : Matrix (Fin b) (Fin b) ℚ_[2])
    (R₁ R₂ : Matrix (Fin c) (Fin c) ℚ_[2]) (h : ZpEquiv (orthSumMat (orthSumMat P Q) R₁) (orthSumMat (orthSumMat P Q) R₂)) :
    ZpEquiv (orthSumMat P (orthSumMat Q R₁)) (orthSumMat P (orthSumMat Q R₂)) := by
  have hh : a + (b + c) = a + b + c := by omega
  rw [dyadic_orthSumMat_assoc P Q R₁ hh, dyadic_orthSumMat_assoc P Q R₂ hh]
  exact dyadic_zpEquiv_cast hh h

/-- **Cancelling a unimodular block list over $\mathbb Z_2$** (Cassels, Ch. 8, Lemma 4.2 and Corollary, pp. 120–122):
for a list $D$ of blocks of exponent $0$ and integral symmetric $G_1$, $G_2$ that are not properly primitive,
$D \perp G_1 \sim D \perp G_2$ implies $G_1 \sim G_2$. A block $u x^2$ is cancelled at once by Lemma 4.2; a binary block
is first moved behind the rest of $D$ (renaming the variables), the rest is cancelled, and then the binary block, by
the Corollary (the forms behind it are then not properly primitive). -/
@[kb "cassels1978" "Ch. 8, Lemma 4.2 and Corollary, pp. 120–122 (cancelling a unimodular constituent)"]
theorem zpEquiv_cancel_dyMat : ∀ (D : List DyBlock), (∀ b ∈ D, b.Valid) → (∀ b ∈ D, blockExp b = 0) →
    ∀ {m : ℕ} {G₁ G₂ : Matrix (Fin m) (Fin m) ℚ_[2]}, G₁ᵀ = G₁ → G₂ᵀ = G₂ → IsClassIntegral G₁ →
      IsClassIntegral G₂ → ¬ IsProperlyPrimitive G₁ → ¬ IsProperlyPrimitive G₂ →
      ZpEquiv (orthSumMat (dyMat D) G₁) (orthSumMat (dyMat D) G₂) → ZpEquiv G₁ G₂
  | [], _, _, m, G₁, G₂, _, _, _, _, _, _, h => by
    have hm : dyDim [] + m = m := by simp [dyDim]
    have e : ∀ G : Matrix (Fin m) (Fin m) ℚ_[2], orthSumMat (dyMat []) G =
        G.submatrix (Fin.cast hm) (Fin.cast hm) := fun G => by
      ext i j
      have hi : i = Fin.natAdd (dyDim []) (Fin.cast hm i) := Fin.ext (by simp [dyDim]; rfl)
      have hj : j = Fin.natAdd (dyDim []) (Fin.cast hm j) := Fin.ext (by simp [dyDim]; rfl)
      conv_lhs => rw [hi, hj, dyadic_orthSumMat_nn]
      rfl
    rw [e, e] at h
    have := dyadic_zpEquiv_cast hm.symm h
    convert this using 1 <;> ext i j <;> rfl
  | b :: D, hv, he, m, G₁, G₂, h₁, h₂, hi₁, hi₂, hp₁, hp₂, h => by
    have hvD : ∀ c ∈ D, c.Valid := fun c hc => hv c (by simp [hc])
    have heD : ∀ c ∈ D, blockExp c = 0 := fun c hc => he c (by simp [hc])
    have hb0 : blockExp b = 0 := he b (by simp)
    have h' := zpEquiv_orthSum_assoc b.mat (dyMat D) G₁ G₂ h
    have hDs := dyMat_transpose_zero D heD
    have hDi := dyMat_integral_zero D hvD heD
    have hs₁ : (orthSumMat (dyMat D) G₁)ᵀ = orthSumMat (dyMat D) G₁ := by
      rw [Lemma42.orthSumMat_transpose', hDs, h₁]
    have hs₂ : (orthSumMat (dyMat D) G₂)ᵀ = orthSumMat (dyMat D) G₂ := by
      rw [Lemma42.orthSumMat_transpose', hDs, h₂]
    have hI₁ := isClassIntegral_orthSum hDi hi₁
    have hI₂ := isClassIntegral_orthSum hDi hi₂
    -- a binary block: move it behind `D`, cancel `D`, then cancel the block
    have binary : ∀ H : Matrix (Fin 2) (Fin 2) ℚ_[2], (H = !![0, 1; 1, 0] ∨ H = !![2, 1; 1, 2]) →
        ZpEquiv (orthSumMat H (orthSumMat (dyMat D) G₁)) (orthSumMat H (orthSumMat (dyMat D) G₂)) →
        ZpEquiv G₁ G₂ := by
      intro H hH hHe
      have hHs : Hᵀ = H := by
        rcases hH with rfl | rfl <;> ext i j <;> fin_cases i <;> fin_cases j <;> rfl
      have hHi : IsClassIntegral H := by rcases hH with rfl | rfl; exacts [integral_hyp, integral_ell]
      have hHd : ∀ j, ‖H j j‖ < 1 := by rcases hH with rfl | rfl; exacts [diag_hyp, diag_ell]
      rw [orthSumMat_swap H (dyMat D) G₁, orthSumMat_swap H (dyMat D) G₂] at hHe
      have hD := zpEquiv_of_submatrix _ hHe
      have hpp : ∀ G : Matrix (Fin m) (Fin m) ℚ_[2], IsClassIntegral G → ¬ IsProperlyPrimitive G →
          ¬ IsProperlyPrimitive (orthSumMat H G) := fun G hG hp => by
        rw [isProperlyPrimitive_orthSum_iff hHi hG hp]; rintro ⟨j, hj⟩; exact (hHd j).ne hj
      have hHG := zpEquiv_cancel_dyMat D hvD heD
        (by rw [Lemma42.orthSumMat_transpose', hHs, h₁]) (by rw [Lemma42.orthSumMat_transpose', hHs, h₂])
        (isClassIntegral_orthSum hHi hi₁) (isClassIntegral_orthSum hHi hi₂) (hpp G₁ hi₁ hp₁) (hpp G₂ hi₂ hp₂) hD
      exact zpEquiv_cancel_binary hH h₁ h₂ hi₁ hi₂ hp₁ hp₂ hHG
    cases b with
    | sq e u =>
      obtain rfl : e = 0 := hb0
      rw [mat_sq_zero] at h'
      refine zpEquiv_cancel_dyMat D hvD heD h₁ h₂ hi₁ hi₂ hp₁ hp₂ ?_
      refine zpEquiv_cancel_unit (norm_odd_int (valid_odd (hv (.sq 0 u) (by simp)))) hs₁ hs₂ hI₁ hI₂ ?_ h'
      rw [isProperlyPrimitive_orthSum_iff hDi hi₁ hp₁, isProperlyPrimitive_orthSum_iff hDi hi₂ hp₂]
    | hyp e =>
      obtain rfl : e = 0 := hb0
      rw [mat_hyp_zero] at h'
      exact binary _ (Or.inl rfl) h'
    | ell e =>
      obtain rfl : e = 0 := hb0
      rw [mat_ell_zero] at h'
      exact binary _ (Or.inr rfl) h'

end QuadFormsKB.ConwaySloane.Mass.Two
