/-
# Splitting off the odd part of the unimodular constituent at $p = 2$

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), (3), p. 263, and §12, p. 281 (bibliography key `conwaysloane1988`); J. W. S. Cassels, *Rational Quadratic
Forms*, Ch. 8, Lemma 4.2 (`cassels1978`).

For $O$ the model of one or two blocks $u x^2$ of exponent $0$ ($O = \langle u\rangle$ or $\langle u, v\rangle$, $u, v$
odd) and $M$ integral symmetric with even diagonal (any scales), the lattice $O \perp M$ is split as in
`TwoAdicRho.lean`, although $M$ is not divisible by $2$:
* every isometry $X$ of $O \perp M$ modulo $2^r$ ($r$ large) has an invertible $O$-block (`isUnit_toBlocks₁₁_odd`): over
  $\mathbb F_2$ the vector $c = (1, \dots, 1, 0, \dots, 0)$ is characteristic, so the row and column sums of the block
  are $1$, which forces $\det X_{11} = 1$ for $a \le 2$ (`det_toBlocks₁₁_odd`);
* hence the block count identity (`card_fromBlocks_eq_sum_of_unit`); the first factor is $N_r(O)$ iff
  $O + W^{\mathsf T}MW \sim O$ (`GoodO1`), and $0$ otherwise; the second is $N_r(M)$ iff moreover the perturbed block
  $M + MWO^{-1}W^{\mathsf T}M$ has even diagonal (Cassels' cancellation, `zEq_pertCO`), and $0$ otherwise
  (`card_secondO_of_odd`);
* `countN_blk_odd`: $N_r(O \perp M) = \#\{W \text{ good}\}\,N_r(O)\,N_r(M)$; the condition depends on $W$ modulo $8$
  (`goodO_of_allDvd`), and `alphaP_blk_odd`: $\alpha_2(O \perp M) = \rho_O(M)\,\alpha_2(O)\,\alpha_2(M)$, $\rho_O$ = `rhoO`
  the proportion of good $W$ modulo $8$.
Indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicRho

set_option linter.unusedSectionVars false

namespace QuadFormsKB.ConwaySloane.Mass.Two

open Matrix QuadFormsKB.Cassels QuadFormsKB.ConwaySloane

/-! ### Quadratic forms over $\mathbb F_2$ -/

section CharTwo

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem zmod2_mul_self (x : ZMod 2) : x * x = x := by fin_cases x <;> rfl

/-- Over $\mathbb F_2$, $y^{\mathsf T}Sy = \sum_k S_{kk}y_k$ for symmetric $S$. -/
theorem quad_char_two (S : Matrix ι ι (ZMod 2)) (hS : Sᵀ = S) (y : ι → ZMod 2) :
    y ⬝ᵥ (S *ᵥ y) = ∑ k, S k k * y k := by
  classical
  have hsum : y ⬝ᵥ (S *ᵥ y) = ∑ p ∈ (Finset.univ : Finset ι) ×ˢ Finset.univ, y p.1 * S p.1 p.2 * y p.2 := by
    simp only [dotProduct, mulVec, Finset.mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hsum, ← Finset.diag_union_offDiag, Finset.sum_union (Finset.disjoint_diag_offDiag _)]
  have hoff : ∑ p ∈ (Finset.univ : Finset ι).offDiag, y p.1 * S p.1 p.2 * y p.2 = 0 := by
    refine Finset.sum_involution (fun p _ => (p.2, p.1)) (fun p _ => ?_) (fun p hp _ => ?_)
      (fun p hp => ?_) (fun p _ => rfl)
    · have : S p.2 p.1 = S p.1 p.2 := by rw [← transpose_apply S p.1 p.2, hS]
      rw [this, show y p.1 * S p.1 p.2 * y p.2 + y p.2 * S p.1 p.2 * y p.1 =
        2 * (y p.1 * S p.1 p.2 * y p.2) by ring]
      rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]
    · rw [Finset.mem_offDiag] at hp
      intro h; exact hp.2.2 (by rw [Prod.ext_iff] at h; exact h.1.symm)
    · rw [Finset.mem_offDiag] at hp ⊢; exact ⟨hp.2.1, hp.1, fun h => hp.2.2 h.symm⟩
  rw [hoff, add_zero]
  refine Finset.sum_bij' (fun p _ => p.1) (fun k _ => (k, k)) (fun p _ => Finset.mem_univ _)
    (fun k _ => by simp [Finset.mem_diag]) (fun p hp => ?_) (fun k _ => rfl) (fun p hp => ?_)
  · rw [Finset.mem_diag] at hp; exact Prod.ext rfl hp.2
  · rw [Finset.mem_diag] at hp
    rw [← hp.2, mul_comm (y p.1), mul_assoc, zmod2_mul_self]

theorem diag_conj (S X : Matrix ι ι (ZMod 2)) (hS : Sᵀ = S) (j : ι) :
    (Xᵀ * S * X) j j = ∑ k, S k k * X k j := by
  rw [← quad_char_two S hS (fun k => X k j)]
  simp only [Matrix.mul_apply, transpose_apply, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end CharTwo

section OddBlock

variable {a b : ℕ}

/-- The indicator vector of the first block. -/
def cvec : Fin a ⊕ Fin b → ZMod 2 := Sum.elim (fun _ => 1) (fun _ => 0)

variable {M : Matrix (Fin b) (Fin b) (ZMod 2)}

theorem fromBlocks_one_symm (hM : Mᵀ = M) :
    (fromBlocks (1 : Matrix (Fin a) (Fin a) (ZMod 2)) 0 0 M)ᵀ = fromBlocks 1 0 0 M := by
  rw [fromBlocks_transpose]; simp [hM]

/-- Over $\mathbb F_2$, an isometry of $1 \perp M$ ($M$ symmetric with zero diagonal) has column sums of its first
block row equal to the indicator of the first block. -/
theorem colsum_odd (hM : Mᵀ = M) (hd : ∀ i, M i i = 0) {X : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) (ZMod 2)}
    (hX : Xᵀ * fromBlocks 1 0 0 M * X = fromBlocks 1 0 0 M) (j : Fin a ⊕ Fin b) :
    ∑ i : Fin a, X (Sum.inl i) j = cvec j := by
  have h := congrFun (congrFun hX j) j
  rw [diag_conj _ _ (fromBlocks_one_symm hM)] at h
  rw [Fintype.sum_sum_type] at h
  simp only [fromBlocks_apply₁₁, fromBlocks_apply₂₂, one_apply_eq, one_mul, hd, zero_mul,
    Finset.sum_const_zero, add_zero] at h
  rw [h]
  rcases j with j | j
  · simp [cvec]
  · simp [cvec, hd]

theorem rowsum_odd (hM : Mᵀ = M) (hd : ∀ i, M i i = 0) {X : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) (ZMod 2)}
    (hX : Xᵀ * fromBlocks 1 0 0 M * X = fromBlocks 1 0 0 M) (hu : IsUnit X) (i : Fin a) :
    ∑ j : Fin a, X (Sum.inl i) (Sum.inl j) = 1 := by
  set A := fromBlocks (1 : Matrix (Fin a) (Fin a) (ZMod 2)) 0 0 M
  have hXd : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det X).mp hu
  set Y := X⁻¹
  have hXY : X * Y = 1 := Matrix.mul_nonsing_inv X hXd
  have hYX : Y * X = 1 := Matrix.nonsing_inv_mul X hXd
  have hY : Yᵀ * A * Y = A := by
    calc Yᵀ * A * Y = Yᵀ * (Xᵀ * A * X) * Y := by rw [hX]
      _ = (X * Y)ᵀ * A * (X * Y) := by simp only [transpose_mul, Matrix.mul_assoc]
      _ = A := by rw [hXY, transpose_one, Matrix.one_mul, Matrix.mul_one]
  have hAX : A * X = Yᵀ * A := by
    calc A * X = (X * Y)ᵀ * A * X := by rw [hXY, transpose_one, Matrix.one_mul]
      _ = Yᵀ * (Xᵀ * A * X) := by simp only [transpose_mul, Matrix.mul_assoc]
      _ = Yᵀ * A := by rw [hX]
  have hAc : A *ᵥ cvec = cvec := by
    funext k
    rcases k with k | k
    · simp [A, mulVec, dotProduct, Fintype.sum_sum_type, cvec, fromBlocks_apply₁₁, one_apply]
    · simp [A, mulVec, dotProduct, Fintype.sum_sum_type, cvec]
  have key : A *ᵥ (X *ᵥ cvec) = Yᵀ *ᵥ cvec := by rw [mulVec_mulVec, hAX, ← mulVec_mulVec, hAc]
  have h1 := congrFun key (Sum.inl i)
  have hl : (A *ᵥ (X *ᵥ cvec)) (Sum.inl i) = ∑ j : Fin a, X (Sum.inl i) (Sum.inl j) := by
    simp [A, mulVec, dotProduct, Fintype.sum_sum_type, cvec, fromBlocks_apply₁₁, one_apply]
  have hr : (Yᵀ *ᵥ cvec) (Sum.inl i) = ∑ k : Fin a, Y (Sum.inl k) (Sum.inl i) := by
    simp [mulVec, dotProduct, Fintype.sum_sum_type, cvec]
  rw [hl, hr, colsum_odd hM hd hY (Sum.inl i)] at h1
  simpa [cvec] using h1

/-- **The first block of an isometry of $1 \perp M$ over $\mathbb F_2$ is invertible** ($a \le 2$, $M$ symmetric with
zero diagonal, the isometry invertible). -/
theorem det_toBlocks₁₁_odd (ha : a = 1 ∨ a = 2) (hM : Mᵀ = M) (hd : ∀ i, M i i = 0)
    {X : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) (ZMod 2)}
    (hX : Xᵀ * fromBlocks 1 0 0 M * X = fromBlocks 1 0 0 M) (hu : IsUnit X) : X.toBlocks₁₁.det = 1 := by
  have hc := fun j : Fin a => colsum_odd hM hd hX (Sum.inl j)
  have hr := rowsum_odd hM hd hX hu
  rcases ha with rfl | rfl
  · have := hc 0
    simp only [Fin.sum_univ_one, cvec, Sum.elim_inl] at this
    rw [Matrix.det_fin_one]; exact this
  · have c0 := hc 0; have c1 := hc 1; have r0 := hr 0; have r1 := hr 1
    simp only [Fin.sum_univ_two, cvec, Sum.elim_inl] at c0 c1 r0 r1
    rw [Matrix.det_fin_two]
    simp only [toBlocks₁₁, of_apply]
    generalize X (Sum.inl 0) (Sum.inl 0) = p at *
    generalize X (Sum.inl 0) (Sum.inl 1) = q at *
    generalize X (Sum.inl 1) (Sum.inl 0) = s at *
    generalize X (Sum.inl 1) (Sum.inl 1) = t at *
    revert p q s t
    decide

end OddBlock

/-! ### The block count identity when every solution has an invertible first block -/

section BlocksGen

variable {R : Type*} [CommRing R] {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable {U : Matrix α α R} {C : Matrix β β R}

theorem eq_blockSol_of_unit (hU : IsUnit U.det) {X : Matrix (α ⊕ β) (α ⊕ β) R}
    (hX : Xᵀ * fromBlocks U 0 0 C * X = fromBlocks U 0 0 C) (hP : IsUnit X.toBlocks₁₁.det) :
    X = blockSol U C (X.toBlocks₂₁ * X.toBlocks₁₁⁻¹) X.toBlocks₁₁ X.toBlocks₂₂ := by
  set P := X.toBlocks₁₁; set Q := X.toBlocks₁₂; set S := X.toBlocks₂₁; set Z := X.toBlocks₂₂
  have hXe : X = fromBlocks P Q S Z := (fromBlocks_toBlocks X).symm
  rw [hXe, fromBlocks_eqn] at hX
  obtain ⟨-, e12, -, -⟩ := fromBlocks_inj.mp hX
  have hPi' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hP
  have hS : S * P⁻¹ * P = S := by rw [Matrix.mul_assoc, hPi', Matrix.mul_one]
  have hPT : IsUnit Pᵀ.det := by rwa [Matrix.det_transpose]
  have hQ : Q = -(U⁻¹ * (S * P⁻¹)ᵀ * C * Z) := by
    have h0 : Pᵀ * (U * Q + (S * P⁻¹)ᵀ * C * Z) = 0 := by
      rw [Matrix.mul_add, transpose_mul, ← e12]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Pᵀ P⁻¹ᵀ, ← transpose_mul, hPi', transpose_one, Matrix.one_mul]
    have h0' : U * Q + (S * P⁻¹)ᵀ * C * Z = 0 := by
      have := congrArg (fun M => Pᵀ⁻¹ * M) h0
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPT] using this
    have := congrArg (fun M => U⁻¹ * M) h0'
    simp only [Matrix.mul_add, Matrix.mul_zero, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU,
      Matrix.one_mul] at this
    rw [eq_neg_iff_add_eq_zero, this]
  rw [blockSol, hS, ← hQ]; exact hXe

theorem card_fiber_of_unit (hUs : Uᵀ = U) (hU : IsUnit U.det) (hCs : Cᵀ = C)
    (hall : ∀ X : Matrix (α ⊕ β) (α ⊕ β) R, Xᵀ * fromBlocks U 0 0 C * X = fromBlocks U 0 0 C →
      IsUnit X.toBlocks₁₁.det) (W : Matrix β α R) :
    Nat.card {X : {X : Matrix (α ⊕ β) (α ⊕ β) R // Xᵀ * fromBlocks U 0 0 C * X = fromBlocks U 0 0 C} //
        X.1.toBlocks₂₁ * X.1.toBlocks₁₁⁻¹ = W} =
      Nat.card ({Y : Matrix α α R // Yᵀ * pertU U C W * Y = U} × {Z : Matrix β β R // Zᵀ * pertC U C W * Z = C}) := by
  refine Nat.card_congr
    { toFun := fun X => (⟨X.1.1.toBlocks₁₁, ?_⟩, ⟨X.1.1.toBlocks₂₂, ?_⟩)
      invFun := fun YZ => ⟨⟨blockSol U C W YZ.1.1 YZ.2.1, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have h := eq_blockSol_of_unit hU X.1.2 (hall _ X.1.2)
    have h2 := X.1.2
    rw [h, blockSol_eqn hUs hU hCs, X.2] at h2
    exact (fromBlocks_inj.mp h2).1
  · have h := eq_blockSol_of_unit hU X.1.2 (hall _ X.1.2)
    have h2 := X.1.2
    rw [h, blockSol_eqn hUs hU hCs, X.2] at h2
    exact (fromBlocks_inj.mp h2).2.2.2
  · rw [blockSol_eqn hUs hU hCs, YZ.1.2, YZ.2.2]
  · have hY : IsUnit YZ.1.1.det := by
      have h := congrArg Matrix.det YZ.1.2
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
      rw [← h] at hU
      exact isUnit_of_mul_isUnit_right hU
    simp only [blockSol, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₁₁]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hY, Matrix.mul_one]
  · rintro ⟨⟨X, hX⟩, rfl⟩
    exact Subtype.ext (Subtype.ext (eq_blockSol_of_unit hU hX (hall _ hX)).symm)
  · intro YZ
    simp [blockSol]

/-- **The block count identity when every solution has an invertible first block.** -/
theorem card_fromBlocks_eq_sum_of_unit [Fintype R] (hUs : Uᵀ = U) (hU : IsUnit U.det) (hCs : Cᵀ = C)
    (hall : ∀ X : Matrix (α ⊕ β) (α ⊕ β) R, Xᵀ * fromBlocks U 0 0 C * X = fromBlocks U 0 0 C →
      IsUnit X.toBlocks₁₁.det) :
    Nat.card {X : Matrix (α ⊕ β) (α ⊕ β) R // Xᵀ * fromBlocks U 0 0 C * X = fromBlocks U 0 0 C} =
      ∑ W : Matrix β α R, Nat.card {Y : Matrix α α R // Yᵀ * pertU U C W * Y = U} *
        Nat.card {Z : Matrix β β R // Zᵀ * pertC U C W * Z = C} := by
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv fun X : {X : Matrix (α ⊕ β) (α ⊕ β) R //
      Xᵀ * fromBlocks U 0 0 C * X = fromBlocks U 0 0 C} => X.1.toBlocks₂₁ * X.1.toBlocks₁₁⁻¹), Nat.card_sigma]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [card_fiber_of_unit hUs hU hCs hall W, Nat.card_prod]

end BlocksGen

/-! ### Every isometry of $O \perp M$ modulo $2^r$ has an invertible $O$-block -/

section Inv

variable {a b r : ℕ} [NeZero (2 ^ r)]

theorem two_dvd_pow (hr : 1 ≤ r) : 2 ∣ 2 ^ r := dvd_pow_self 2 (by omega)

/-- The reduction $\mathbb Z/2^r \to \mathbb F_2$. -/
abbrev red2 (hr : 1 ≤ r) : ZMod (2 ^ r) →+* ZMod 2 := ZMod.castHom (two_dvd_pow hr) (ZMod 2)

theorem isUnit_of_red2 (hr : 1 ≤ r) {x : ZMod (2 ^ r)} (h : red2 hr x = 1) : IsUnit x := by
  rw [← ZMod.natCast_zmod_val x]
  have : ¬ 2 ∣ (x.val : ℤ) := by
    rintro ⟨k, hk⟩
    rw [ZMod.castHom_apply, ZMod.cast_eq_val] at h
    have h' : ((x.val : ℤ) : ZMod 2) = 1 := by exact_mod_cast h
    rw [hk] at h'
    push_cast at h'
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul] at h'
    exact zero_ne_one h'
  exact_mod_cast isUnit_odd this

theorem odd_of_sq_mul {z d : ℤ} (hd : ¬ (2 : ℤ) ^ r ∣ d) (h : ((z : ZMod (2 ^ r))) ^ 2 * d = d) : ¬ 2 ∣ z := by
  intro h2
  apply hd
  have h1 : ((((z ^ 2 - 1) * d : ℤ)) : ZMod (2 ^ r)) = 0 := by push_cast; rw [sub_mul, one_mul, h, sub_self]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
  have hc : IsCoprime ((2 : ℤ) ^ r) (z ^ 2 - 1) := by
    refine IsCoprime.pow_left ?_
    obtain ⟨k, rfl⟩ := h2
    exact ⟨2 * k ^ 2, -1, by ring⟩
  push_cast at h1
  exact hc.dvd_of_dvd_mul_left h1

variable {O : Matrix (Fin a) (Fin a) ℤ} {M : Matrix (Fin b) (Fin b) ℤ}

/-- **The $O$-block of an isometry of $O \perp M$ is invertible** ($O$ of size $a \le 2$ congruent to $1$ modulo $2$,
$M$ symmetric with even diagonal, $r$ large: $2^r \nmid \det O\det M$): the characteristic vector argument. -/
theorem isUnit_toBlocks₁₁_odd (hr : 1 ≤ r) (ha : a = 1 ∨ a = 2) (hO2 : O.map (Int.castRingHom (ZMod 2)) = 1)
    (hMs : Mᵀ = M) (hMe : EvenDiag M) (hdet : ¬ (2 : ℤ) ^ r ∣ O.det * M.det)
    {X : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) (ZMod (2 ^ r))}
    (hX : Xᵀ * fromBlocks (red r O) 0 0 (red r M) * X = fromBlocks (red r O) 0 0 (red r M)) :
    IsUnit X.toBlocks₁₁.det := by
  -- `X` is invertible
  have hXu : IsUnit X.det := by
    have hd := congrArg Matrix.det hX
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_fromBlocks_zero₂₁] at hd
    have e : (red r O).det * (red r M).det = ((O.det * M.det : ℤ) : ZMod (2 ^ r)) := by
      rw [show (red r O).det = ((O.det : ℤ) : ZMod (2 ^ r)) from
          (RingHom.map_det (Int.castRingHom (ZMod (2 ^ r))) O).symm,
        show (red r M).det = ((M.det : ℤ) : ZMod (2 ^ r)) from
          (RingHom.map_det (Int.castRingHom (ZMod (2 ^ r))) M).symm]
      push_cast; ring
    rw [e] at hd
    have h2 : (((X.det.val : ℤ) : ZMod (2 ^ r))) ^ 2 * ((O.det * M.det : ℤ) : ZMod (2 ^ r)) =
        ((O.det * M.det : ℤ) : ZMod (2 ^ r)) := by
      rw [show ((X.det.val : ℤ) : ZMod (2 ^ r)) = X.det by exact_mod_cast ZMod.natCast_zmod_val X.det]
      linear_combination hd
    have := isUnit_odd (r := r) (odd_of_sq_mul hdet h2)
    rwa [show ((X.det.val : ℤ) : ZMod (2 ^ r)) = X.det by exact_mod_cast ZMod.natCast_zmod_val X.det] at this
  -- reduce modulo 2
  set φ := red2 (r := r) hr
  have hφ : ∀ z : ℤ, φ (z : ZMod (2 ^ r)) = (z : ZMod 2) := fun z => map_intCast φ z
  set Mb := M.map (Int.castRingHom (ZMod 2))
  have hA : (fromBlocks (red r O) 0 0 (red r M)).map φ = fromBlocks (1 : Matrix (Fin a) (Fin a) (ZMod 2)) 0 0 Mb := by
    rw [Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero φ), ← hO2]
    congr 1 <;> ext i j <;> simp [hφ, Mb]
  have hX2 : (X.map φ)ᵀ * fromBlocks 1 0 0 Mb * X.map φ = fromBlocks 1 0 0 Mb := by
    rw [← hA, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hX]
  have hMbs : Mbᵀ = Mb := by simp only [Mb, ← Matrix.transpose_map, hMs]
  have hMbd : ∀ i, Mb i i = 0 := by
    intro i
    obtain ⟨k, hk⟩ := hMe i
    simp only [Mb, map_apply, Int.coe_castRingHom, hk]
    push_cast
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]
  have hXu2 : IsUnit (X.map φ) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    rw [show (X.map φ).det = φ X.det from (RingHom.map_det φ X).symm]
    exact hXu.map φ
  have h1 := det_toBlocks₁₁_odd ha hMbs hMbd hX2 hXu2
  refine isUnit_of_red2 hr ?_
  rw [RingHom.map_det]
  exact h1

end Inv

/-! ### The first factor -/

section FirstO

variable {a b r : ℕ} [NeZero (2 ^ r)] {O : Matrix (Fin a) (Fin a) ℤ} {M : Matrix (Fin b) (Fin b) ℤ}

/-- $O + W^{\mathsf T}MW$ is $\mathbb Z_2$-equivalent to $O$. -/
def GoodO1 (O : Matrix (Fin a) (Fin a) ℤ) (M : Matrix (Fin b) (Fin b) ℤ) (W : Matrix (Fin b) (Fin a) ℤ) : Prop :=
  ZpEquiv (O.map (Int.cast : ℤ → ℚ_[2])) ((O + Wᵀ * M * W).map (Int.cast : ℤ → ℚ_[2]))

theorem pertU_redO (W : Matrix (Fin b) (Fin a) (ZMod (2 ^ r))) :
    pertU (red r O) (red r M) W = red r (O + (lift W)ᵀ * M * lift W) := by
  rw [pertU, red_add, red_mul, red_mul, red_transpose, red_lift]

theorem card_firstO_of_good (W : Matrix (Fin b) (Fin a) (ZMod (2 ^ r))) (h : GoodO1 O M (lift W)) :
    Nat.card {Y : Matrix (Fin a) (Fin a) (ZMod (2 ^ r)) //
      Yᵀ * pertU (red r O) (red r M) W * Y = red r O} = countN 2 r O := by
  obtain ⟨G, hG, hGe⟩ := exists_unit_congr_of_zpEquiv (p := 2) h r
  rw [pertU_redO]
  change Nat.card {Y : Matrix (Fin a) (Fin a) (ZMod (2 ^ r)) //
      Yᵀ * (O + (lift W)ᵀ * M * lift W).map (Int.castRingHom (ZMod (2 ^ r))) * Y =
        O.map (Int.castRingHom (ZMod (2 ^ r)))} = _
  rw [← hGe, card_congr_unit hG]
  rfl

theorem card_firstO_of_not_good (hr : 3 ≤ r) (hOs : Oᵀ = O) (hO : ¬ 2 ∣ O.det) (hMs : Mᵀ = M)
    (W : Matrix (Fin b) (Fin a) (ZMod (2 ^ r))) (h : ¬ GoodO1 O M (lift W)) :
    Nat.card {Y : Matrix (Fin a) (Fin a) (ZMod (2 ^ r)) //
      Yᵀ * pertU (red r O) (red r M) W * Y = red r O} = 0 := by
  rw [Nat.card_eq_zero]
  left
  refine ⟨fun ⟨Y, hY⟩ => h ?_⟩
  rw [pertU_redO] at hY
  set O' := O + (lift W)ᵀ * M * lift W with hO'
  have hO's : O'ᵀ = O' := by rw [hO', transpose_add, quad_symm hMs, hOs]
  have hd := congrArg Matrix.det hY
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  have hu := isUnit_red_det (r := r) hO
  rw [← hd] at hu
  have hO'd : ¬ 2 ∣ O'.det := by
    refine not_two_dvd_of_isUnit (r := r) (by omega) ?_
    rw [show ((O'.det : ℤ) : ZMod (2 ^ r)) = (red r O').det from
      RingHom.map_det (Int.castRingHom (ZMod (2 ^ r))) O']
    exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hu)
  have hY' : red r ((lift Y)ᵀ * O' * lift Y) = red r O := by
    rw [red_mul, red_mul, red_transpose, red_lift]; exact hY
  have hdY : ¬ 2 ∣ (lift Y).det := by
    refine not_two_dvd_of_isUnit (r := r) (by omega) ?_
    rw [show (((lift Y).det : ℤ) : ZMod (2 ^ r)) = (red r (lift Y)).det from
      RingHom.map_det (Int.castRingHom (ZMod (2 ^ r))) (lift Y), red_lift]
    exact isUnit_of_mul_isUnit_right hu
  have h8 := allDvd_of_red_eq hY'
  refine (dyadic_zpEquiv_of_int O' O (lift Y) hO's hOs (Int.not_even_iff_odd.mp fun he =>
    hO'd (even_iff_two_dvd.mp he)) (Int.not_even_iff_odd.mp fun he => hdY (even_iff_two_dvd.mp he))
    fun i j => ?_).symm
  have := (pow_dvd_pow (2 : ℤ) hr).trans (h8 i j)
  norm_num at this
  exact this

end FirstO

/-! ### The second factor -/

section SecondO

variable {b : ℕ} {L : List DyBlock} {M : Matrix (Fin b) (Fin b) ℤ}

/-- The condition on $W$ for $O \perp M$: $O + W^{\mathsf T}MW \sim O$ and the perturbed second block
$M + MWO^{-1}W^{\mathsf T}M$ has even diagonal (equivalently $MW\operatorname{adj}(O)W^{\mathsf T}M$ has even
diagonal). -/
def GoodO {a : ℕ} (O : Matrix (Fin a) (Fin a) ℤ) (M : Matrix (Fin b) (Fin b) ℤ) (W : Matrix (Fin b) (Fin a) ℤ) :
    Prop :=
  GoodO1 O M W ∧ EvenDiag (M * W * O.adjugate * Wᵀ * M)

theorem not_pp_of_diag_dvd {m : ℕ} {G : Matrix (Fin m) (Fin m) ℤ_[2]} (h : ∀ i, (2 : ℤ_[2]) ∣ G i i) :
    ¬ IsProperlyPrimitive (G.map PadicInt.Coe.ringHom) := by
  rintro ⟨-, j, hj⟩
  obtain ⟨y, hy⟩ := h j
  have hu : IsUnit ((2 : ℤ_[2]) * y) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_def, ← hy]
    simpa using hj
  have h2 : IsUnit (2 : ℤ_[2]) := isUnit_of_mul_isUnit_left hu
  rw [PadicInt.isUnit_iff] at h2
  have := PadicInt.norm_p (p := 2)
  norm_num at this
  rw [this] at h2
  norm_num at h2

theorem two_dvd_cast_of_even {z : ℤ} (h : 2 ∣ z) : (2 : ℤ_[2]) ∣ (z : ℤ_[2]) := by
  obtain ⟨k, rfl⟩ := h; exact ⟨k, by push_cast; ring⟩

/-- **The perturbed second block is equivalent to $M$ when $W$ is good** (over $\mathbb Z_2$). -/
theorem zEq_pertCO (hv : ∀ c ∈ L, c.Valid) (he : ∀ c ∈ L, blockExp c = 0) (hMs : Mᵀ = M) (hMe : EvenDiag M)
    {W : Matrix (Fin b) (Fin (dyDim L)) ℤ} (h : GoodO (intMat L) M W) :
    ZEq (M.map (Int.castRingHom ℤ_[2]))
      (pertC ((intMat L).map (Int.castRingHom ℤ_[2])) (M.map (Int.castRingHom ℤ_[2]))
        (W.map (Int.castRingHom ℤ_[2]))) := by
  set ι₂ := Int.castRingHom ℤ_[2]
  set U := intMat L with hUdef
  set Uz := U.map ι₂
  set Mz := M.map ι₂
  set Wz := W.map ι₂
  have hUs : Uᵀ = U := (isSymm_intMat L).eq
  have hUd := det_odd_of_zero hv he
  have hUu : IsUnit Uz.det :=
    dyadic_unit_det_map U (Int.not_even_iff_odd.mp fun h => hUd (even_iff_two_dvd.mp h))
  have hUzs : Uzᵀ = Uz := by simp only [Uz, ← Matrix.transpose_map, hUs]
  have hMzs : Mzᵀ = Mz := by simp only [Mz, ← Matrix.transpose_map, hMs]
  have hU' : pertU Uz Mz Wz = (U + Wᵀ * M * W).map ι₂ := by
    rw [pertU, Matrix.map_add _ (map_add ι₂), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have hG₁ : ZEq Uz (pertU Uz Mz Wz) := by
    rw [hU']
    have := h.1
    unfold GoodO1 at this
    rw [← map_coe_int, ← map_coe_int] at this
    exact zpEquiv_coe_iff.mp this
  set Pz := pertC Uz Mz Wz with hPz
  set T₀ := blockSol Uz Mz Wz 1 1 with hT₀
  have hT : T₀ᵀ * Matrix.fromBlocks Uz 0 0 Mz * T₀ = Matrix.fromBlocks (pertU Uz Mz Wz) 0 0 Pz := by
    rw [hT₀, blockSol_eqn hUzs hUu hMzs Wz 1 1]; simp [hPz]
  have hU'u : IsUnit (pertU Uz Mz Wz).det := by
    obtain ⟨T, hTu, hTe⟩ := hG₁
    rw [← hTe, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    have := (Matrix.isUnit_iff_isUnit_det T).mp hTu
    exact (this.mul hUu).mul this
  have hT₀u : IsUnit T₀ := by
    rw [Matrix.isUnit_iff_isUnit_det, hT₀, blockSol, Matrix.mul_one, Matrix.mul_one, det_fromBlocks_one₂₂]
    have e : (1 : Matrix (Fin (dyDim L)) (Fin (dyDim L)) ℤ_[2]) - -(Uz⁻¹ * Wzᵀ * Mz) * Wz =
        Uz⁻¹ * pertU Uz Mz Wz := by
      rw [pertU, Matrix.mul_add, Matrix.nonsing_inv_mul _ hUu, Matrix.neg_mul, sub_neg_eq_add]
      simp only [Matrix.mul_assoc]
    rw [e, Matrix.det_mul]
    exact (Matrix.isUnit_nonsing_inv_det _ hUu).mul hU'u
  have hZ : ZEq (Matrix.fromBlocks Uz 0 0 Mz) (Matrix.fromBlocks Uz 0 0 Pz) :=
    ZEq.trans ⟨T₀, hT₀u, hT⟩ (ZEq.fromBlocks hG₁.symm (ZEq.refl Pz))
  have hZ' := hZ.submatrix (finSumFinEquiv.symm : Fin (dyDim L + b) ≃ Fin (dyDim L) ⊕ Fin b)
  rw [← zpEquiv_coe_iff] at hZ'
  have hsum : ∀ N : Matrix (Fin b) (Fin b) ℤ_[2],
      ((Matrix.fromBlocks Uz 0 0 N).submatrix finSumFinEquiv.symm finSumFinEquiv.symm).map PadicInt.Coe.ringHom =
        orthSumMat (dyMat L) (N.map PadicInt.Coe.ringHom) := fun N => by
    rw [dyadic_orthSumMat_eq, ← Matrix.submatrix_map, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _),
      Matrix.map_zero _ (map_zero _)]
    congr 2
    rw [map_coe_int, intMat_map L fun c hc => (he c hc).ge]
  rw [hsum, hsum] at hZ'
  have hPzs : Pzᵀ = Pz := by
    rw [hPz, pertC, transpose_add, hMzs]
    simp only [transpose_mul, hMzs, transpose_transpose, transpose_nonsing_inv, hUzs, Matrix.mul_assoc]
  -- the diagonals are even
  have hMd : ∀ i, (2 : ℤ_[2]) ∣ Mz i i := fun i => two_dvd_cast_of_even (hMe i)
  have hPd : ∀ i, (2 : ℤ_[2]) ∣ Pz i i := by
    intro i
    have hinv : Uz⁻¹ = Ring.inverse Uz.det • Uz.adjugate := Matrix.inv_def Uz
    have hadj : Uz.adjugate = U.adjugate.map ι₂ := (RingHom.map_adjugate ι₂ U).symm
    have e : Pz = Mz + Ring.inverse Uz.det • (M * W * U.adjugate * Wᵀ * M).map ι₂ := by
      rw [hPz, pertC, hinv, hadj]
      simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.mul_smul, Matrix.smul_mul]
      rfl
    rw [e, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact dvd_add (hMd i) (dvd_mul_of_dvd_right (two_dvd_cast_of_even (h.2 i)) _)
  have hc := zpEquiv_cancel_dyMat L hv he (by rw [← Matrix.transpose_map, hMzs])
    (by rw [← Matrix.transpose_map, hPzs]) (integral_coe _) (integral_coe _) (not_pp_of_diag_dvd hMd)
    (not_pp_of_diag_dvd hPd) hZ'
  exact zpEquiv_coe_iff.mp hc

/-- **The second factor when $W$ is good**: it is $N_r(M)$. -/
theorem card_secondO_of_good {r : ℕ} [NeZero (2 ^ r)] (hv : ∀ c ∈ L, c.Valid) (he : ∀ c ∈ L, blockExp c = 0)
    (hMs : Mᵀ = M) (hMe : EvenDiag M) (W : Matrix (Fin b) (Fin (dyDim L)) (ZMod (2 ^ r)))
    (h : GoodO (intMat L) M (lift W)) :
    Nat.card {Z : Matrix (Fin b) (Fin b) (ZMod (2 ^ r)) //
      Zᵀ * pertC (red r (intMat L)) (red r M) W * Z = red r M} = countN 2 r M := by
  obtain ⟨G, hG, hGe⟩ := (zEq_pertCO hv he hMs hMe h).map r
  have hUd := det_odd_of_zero hv he
  have hUu : IsUnit ((intMat L).map (Int.castRingHom ℤ_[2])).det :=
    dyadic_unit_det_map _ (Int.not_even_iff_odd.mp fun h => hUd (even_iff_two_dvd.mp h))
  have hP : (pertC ((intMat L).map (Int.castRingHom ℤ_[2])) (M.map (Int.castRingHom ℤ_[2]))
      ((lift W).map (Int.castRingHom ℤ_[2]))).map (PadicInt.toZModPow r) =
      pertC (red r (intMat L)) (red r M) W := by
    rw [pertC, pertC, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
      Matrix.transpose_map, map_nonsing_inv' _ _ hUu, map_red_int, map_red_int, map_red_int, red_lift]
  rw [hP, map_red_int] at hGe
  rw [← hGe, card_congr_unit hG]
  rfl

theorem odd_of_sq_mul_unit {r : ℕ} [NeZero (2 ^ r)] (hr : 1 ≤ r) {z d : ℤ} (hd : ¬ (2 : ℤ) ^ r ∣ d)
    {e : ZMod (2 ^ r)} (he : IsUnit e) (h : ((z : ZMod (2 ^ r))) ^ 2 * d * e = d) : ¬ 2 ∣ z := by
  intro h2
  apply hd
  set w : ℤ := (((he.unit⁻¹ : (ZMod (2 ^ r))ˣ) : ZMod (2 ^ r)).val : ℤ)
  have hw : ((w : ℤ) : ZMod (2 ^ r)) = ((he.unit⁻¹ : (ZMod (2 ^ r))ˣ) : ZMod (2 ^ r)) := by
    simp only [w]; exact_mod_cast ZMod.natCast_zmod_val _
  have hwodd : ¬ 2 ∣ w := not_two_dvd_of_isUnit hr (by rw [hw]; exact Units.isUnit _)
  have h1 : ((((z ^ 2 - w) * d : ℤ)) : ZMod (2 ^ r)) = 0 := by
    push_cast
    rw [hw]
    have hu : ((he.unit⁻¹ : (ZMod (2 ^ r))ˣ) : ZMod (2 ^ r)) * e = 1 := by
      exact he.val_inv_mul
    linear_combination ((he.unit⁻¹ : (ZMod (2 ^ r))ˣ) : ZMod (2 ^ r)) * h +
      (-(z : ZMod (2 ^ r)) ^ 2 * d) * hu
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
  have hc : IsCoprime ((2 : ℤ) ^ r) (z ^ 2 - w) := by
    refine IsCoprime.pow_left ?_
    obtain ⟨k, rfl⟩ := h2
    obtain ⟨m, hm⟩ : ∃ m, w = 2 * m + 1 := ⟨w / 2, by omega⟩
    exact ⟨2 * k ^ 2 - m, -1, by rw [hm]; ring⟩
  push_cast at h1
  exact hc.dvd_of_dvd_mul_left h1

theorem lift_map_two {r : ℕ} [NeZero (2 ^ r)] (hr : 1 ≤ r) {m k : Type*} (W : Matrix m k (ZMod (2 ^ r))) :
    (lift W).map (Int.castRingHom (ZMod 2)) = W.map (red2 hr) := by
  ext i j
  simp only [lift, map_apply, Int.coe_castRingHom, Int.cast_natCast, ZMod.castHom_apply, ZMod.cast_eq_val]

/-- **The second factor when the perturbed block has an odd diagonal entry**: it is $0$ (an equivalence would carry
the diagonal of $M$, which is even, to that of $C'_W$ modulo $2$). -/
theorem card_secondO_of_odd {r : ℕ} [NeZero (2 ^ r)] (hr : 1 ≤ r) (hv : ∀ c ∈ L, c.Valid)
    (he : ∀ c ∈ L, blockExp c = 0) (hO2 : (intMat L).map (Int.castRingHom (ZMod 2)) = 1) (hMs : Mᵀ = M)
    (hMe : EvenDiag M) (hdetM : ¬ (2 : ℤ) ^ r ∣ M.det) (W : Matrix (Fin b) (Fin (dyDim L)) (ZMod (2 ^ r)))
    (h1 : GoodO1 (intMat L) M (lift W))
    (h2 : ¬ EvenDiag (M * lift W * (intMat L).adjugate * (lift W)ᵀ * M)) :
    Nat.card {Z : Matrix (Fin b) (Fin b) (ZMod (2 ^ r)) //
      Zᵀ * pertC (red r (intMat L)) (red r M) W * Z = red r M} = 0 := by
  rw [Nat.card_eq_zero]
  left
  refine ⟨fun ⟨Z, hZ⟩ => h2 ?_⟩
  set O := intMat L with hOdef
  have hOs : Oᵀ = O := (isSymm_intMat L).eq
  have hUd := det_odd_of_zero hv he
  have hOu := isUnit_red_det (r := r) hUd
  -- `det (U'_W)` is a unit
  obtain ⟨G, hG, hGe⟩ := exists_unit_congr_of_zpEquiv (p := 2) h1 r
  have hU'u : IsUnit (pertU (red r O) (red r M) W).det := by
    rw [pertU_redO]
    change IsUnit ((O + (lift W)ᵀ * M * lift W).map (Int.castRingHom (ZMod (2 ^ r)))).det
    rw [← hGe, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    have := (Matrix.isUnit_iff_isUnit_det G).mp hG
    exact (this.mul hOu).mul this
  set B' := (red r O)⁻¹ * Wᵀ * red r M
  have hP : pertC (red r O) (red r M) W = red r M * (1 + W * B') := by
    rw [pertC, Matrix.mul_add, Matrix.mul_one]; simp only [B', Matrix.mul_assoc]
  have he' : IsUnit (1 + W * B').det := by
    rw [Matrix.det_one_add_mul_comm]
    have e : (1 : Matrix (Fin (dyDim L)) (Fin (dyDim L)) (ZMod (2 ^ r))) + B' * W =
        (red r O)⁻¹ * pertU (red r O) (red r M) W := by
      rw [pertU, Matrix.mul_add, Matrix.nonsing_inv_mul _ hOu]; simp only [B', Matrix.mul_assoc]
    rw [e, Matrix.det_mul]
    exact (Matrix.isUnit_nonsing_inv_det _ hOu).mul hU'u
  -- `Z` is invertible
  have hZu : IsUnit Z.det := by
    have hd := congrArg Matrix.det hZ
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hP, Matrix.det_mul] at hd
    have hMr : (red r M).det = ((M.det : ℤ) : ZMod (2 ^ r)) :=
      (RingHom.map_det (Int.castRingHom (ZMod (2 ^ r))) M).symm
    have hz : ((Z.det.val : ℤ) : ZMod (2 ^ r)) = Z.det := by exact_mod_cast ZMod.natCast_zmod_val Z.det
    have h3 : ((Z.det.val : ℤ) : ZMod (2 ^ r)) ^ 2 * (M.det : ZMod (2 ^ r)) * (1 + W * B').det =
        (M.det : ZMod (2 ^ r)) := by
      rw [hz, ← hMr]; linear_combination hd
    have := odd_of_sq_mul_unit hr hdetM he' h3
    rw [← hz]; exact isUnit_odd this
  -- reduce modulo 2
  set φ := red2 (r := r) hr
  set Zb := Z.map φ
  set Pb := (pertC (red r O) (red r M) W).map φ
  set Mb := M.map (Int.castRingHom (ZMod 2))
  have hMb : (red r M).map φ = Mb := by ext i j; simp [Mb, φ]
  have hOb : (red r O).map φ = 1 := by
    rw [← hO2]; ext i j; simp [φ]
  have hinv : ((red r O)⁻¹).map φ = 1 := by rw [map_nonsing_inv' φ _ hOu, hOb, inv_one]
  set Wb := W.map φ
  have hPb : Pb = Mb + Mb * Wb * Wbᵀ * Mb := by
    simp only [Pb, pertC, Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.transpose_map, hMb, hinv,
      Matrix.mul_one, Wb]
  have hZb : Zbᵀ * Pb * Zb = Mb := by
    simp only [Zb, Pb, ← Matrix.transpose_map, ← Matrix.map_mul, hZ, hMb]
  have hMbs : Mbᵀ = Mb := by simp only [Mb, ← Matrix.transpose_map, hMs]
  have hMbd : ∀ i, Mb i i = 0 := by
    intro i
    obtain ⟨k, hk⟩ := hMe i
    simp only [Mb, map_apply, Int.coe_castRingHom, hk]
    push_cast
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]
  have hPbs : Pbᵀ = Pb := by
    rw [hPb]; simp only [transpose_add, transpose_mul, hMbs, transpose_transpose, Matrix.mul_assoc]
  -- the diagonal of `Pb` vanishes
  have hdiag : ∀ j, ∑ k, Pb k k * Zb k j = 0 := by
    intro j
    rw [← diag_conj Pb Zb hPbs j, hZb, hMbd]
  have hZbu : IsUnit Zbᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose,
      show Zb.det = φ Z.det from (RingHom.map_det φ Z).symm]
    exact hZu.map φ
  have hd0 : (fun k => Pb k k) = 0 := by
    have hv0 : Zbᵀ *ᵥ (fun k => Pb k k) = 0 := by
      funext j
      simp only [mulVec, dotProduct, transpose_apply, Pi.zero_apply]
      rw [← hdiag j]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have hZd : IsUnit Zbᵀ.det := (Matrix.isUnit_iff_isUnit_det _).mp hZbu
    calc (fun k => Pb k k) = (Zbᵀ⁻¹ * Zbᵀ) *ᵥ (fun k => Pb k k) := by
          rw [Matrix.nonsing_inv_mul _ hZd, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hv0, Matrix.mulVec_zero]
  -- and it is the diagonal of `N` modulo 2
  have hN : (M * lift W * O.adjugate * (lift W)ᵀ * M).map (Int.castRingHom (ZMod 2)) = Mb * Wb * Wbᵀ * Mb := by
    have hadj : O.adjugate.map (Int.castRingHom (ZMod 2)) = 1 := by
      rw [← RingHom.mapMatrix_apply, RingHom.map_adjugate, RingHom.mapMatrix_apply, hO2, Matrix.adjugate_one]
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, lift_map_two hr,
      hadj, Matrix.mul_one]
  intro k
  have hk := congrFun hd0 k
  simp only [Pi.zero_apply] at hk
  rw [hPb, Matrix.add_apply, hMbd, zero_add, ← hN, map_apply, Int.coe_castRingHom,
    ZMod.intCast_zmod_eq_zero_iff_dvd] at hk
  exact_mod_cast hk

end SecondO

/-! ### The count -/

section CountO

variable {b : ℕ} {L : List DyBlock} {M : Matrix (Fin b) (Fin b) ℤ}

/-- **The block count identity for $O \perp M$** ($O$ the model of one or two blocks $u x^2$ of exponent $0$, $M$
symmetric with even diagonal): $N_r(O \perp M) = \#\{W : W \text{ good}\}\,N_r(O)\,N_r(M)$ for $r \ge 3$ with
$2^r \nmid \det O\det M$. -/
@[kb "conwaysloane1988" "(18), p. 281 (splitting off the odd part of the unimodular constituent, p = 2)"]
theorem countN_blk_odd {r : ℕ} (hr : 3 ≤ r) (hv : ∀ c ∈ L, c.Valid) (he : ∀ c ∈ L, blockExp c = 0)
    (ha : dyDim L = 1 ∨ dyDim L = 2) (hO2 : (intMat L).map (Int.castRingHom (ZMod 2)) = 1) (hMs : Mᵀ = M)
    (hMe : EvenDiag M) (hdet : ¬ (2 : ℤ) ^ r ∣ (intMat L).det * M.det) :
    countN 2 r (blk 1 (intMat L) M) = Nat.card {W : Matrix (Fin b) (Fin (dyDim L)) (ZMod (2 ^ r)) //
      GoodO (intMat L) M (lift W)} * countN 2 r (intMat L) * countN 2 r M := by
  classical
  have : NeZero (2 ^ r) := ⟨by positivity⟩
  set U := intMat L
  have hUs : Uᵀ = U := (isSymm_intMat L).eq
  have hUd := det_odd_of_zero hv he
  have hdetM : ¬ (2 : ℤ) ^ r ∣ M.det := fun h => hdet (dvd_mul_of_dvd_right h _)
  have hmap : (blk 1 U M).map (Int.castRingHom (ZMod (2 ^ r))) =
      (fromBlocks (red r U) 0 0 (red r M)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [blk, ← Matrix.submatrix_map, fromBlocks_map, Matrix.map_zero _ (map_zero _),
      Matrix.map_zero _ (map_zero _)]
    simp
    rfl
  have hUbs : (red r U)ᵀ = red r U := by rw [← red_transpose, hUs]
  have hMbs : (red r M)ᵀ = red r M := by rw [← red_transpose, hMs]
  unfold countN
  rw [hmap, card_sol_submatrix, card_fromBlocks_eq_sum_of_unit hUbs (isUnit_red_det hUd) hMbs
    (fun X hX => isUnit_toBlocks₁₁_odd (by omega) ha hO2 hMs hMe hdet hX)]
  have hterm : ∀ W : Matrix (Fin b) (Fin (dyDim L)) (ZMod (2 ^ r)),
      Nat.card {Y : Matrix (Fin (dyDim L)) (Fin (dyDim L)) (ZMod (2 ^ r)) //
        Yᵀ * pertU (red r U) (red r M) W * Y = red r U} *
      Nat.card {Z : Matrix (Fin b) (Fin b) (ZMod (2 ^ r)) //
        Zᵀ * pertC (red r U) (red r M) W * Z = red r M} =
      if GoodO U M (lift W) then countN 2 r U * countN 2 r M else 0 := by
    intro W
    by_cases h1 : GoodO1 U M (lift W)
    · by_cases h2 : EvenDiag (M * lift W * U.adjugate * (lift W)ᵀ * M)
      · rw [if_pos ⟨h1, h2⟩, card_firstO_of_good W h1, card_secondO_of_good hv he hMs hMe W ⟨h1, h2⟩]
      · rw [if_neg (fun h => h2 h.2), card_secondO_of_odd (by omega) hv he hO2 hMs hMe hdetM W h1 h2, mul_zero]
    · rw [if_neg (fun h => h1 h.1), card_firstO_of_not_good hr hUs hUd hMs W h1, zero_mul]
  rw [Finset.sum_congr rfl fun W _ => hterm W, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, smul_eq_mul]
  unfold countN
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  ring

end CountO

/-! ### Periodicity, the proportion $\rho_O$, and the density -/

section RhoO

variable {a b : ℕ} {O : Matrix (Fin a) (Fin a) ℤ} {M : Matrix (Fin b) (Fin b) ℤ}

theorem exists_eight_smul {W W' : Matrix (Fin b) (Fin a) ℤ} (hW : AllDvd 8 (W' - W)) :
    ∃ E : Matrix (Fin b) (Fin a) ℤ, W' = W + (8 : ℤ) • E := by
  refine ⟨Matrix.of fun i j => (W' i j - W i j) / 8, ?_⟩
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  have := hW i j
  simp only [Matrix.sub_apply] at this
  rw [Int.mul_ediv_cancel' this]; ring

theorem det_odd_of_goodO1 (hOd : ¬ 2 ∣ O.det) {W : Matrix (Fin b) (Fin a) ℤ} (h : GoodO1 O M W) :
    ¬ 2 ∣ (O + Wᵀ * M * W).det := by
  obtain ⟨G, hG, hGe⟩ := exists_unit_congr_of_zpEquiv (p := 2) h 1
  have hd := congrArg Matrix.det hGe
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  refine not_two_dvd_of_isUnit (r := 1) le_rfl ?_
  rw [show (((O + Wᵀ * M * W).det : ℤ) : ZMod (2 ^ 1)) = ((O + Wᵀ * M * W).map (Int.castRingHom _)).det from
    RingHom.map_det (Int.castRingHom (ZMod (2 ^ 1))) _, ← hd]
  have hGd := (Matrix.isUnit_iff_isUnit_det G).mp hG
  refine (hGd.mul ?_).mul hGd
  rw [show (O.map (Int.castRingHom (ZMod (2 ^ 1)))).det = ((O.det : ℤ) : ZMod (2 ^ 1)) from
    (RingHom.map_det (Int.castRingHom (ZMod (2 ^ 1))) O).symm]
  exact isUnit_odd hOd

theorem goodO_of_allDvd (hOs : Oᵀ = O) (hOd : ¬ 2 ∣ O.det) (hMs : Mᵀ = M) {W W' : Matrix (Fin b) (Fin a) ℤ}
    (hW : AllDvd 8 (W' - W)) (h : GoodO O M W) : GoodO O M W' := by
  obtain ⟨E, rfl⟩ := exists_eight_smul hW
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1.trans (dyadic_zpEquiv_of_int _ _ 1 ?_ ?_ ?_ (by simp) fun i j => ?_), fun i => ?_⟩
  · rw [transpose_add, quad_symm hMs, hOs]
  · rw [transpose_add, quad_symm hMs, hOs]
  · exact Int.not_even_iff_odd.mp fun he => det_odd_of_goodO1 hOd h1 (even_iff_two_dvd.mp he)
  · simp only [transpose_one, Matrix.one_mul, Matrix.mul_one]
    refine ⟨-((Eᵀ * M * W + Wᵀ * M * E + (8 : ℤ) • (Eᵀ * M * E)) i j), ?_⟩
    simp only [transpose_add, transpose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  · obtain ⟨k, hk⟩ := h2 i
    refine ⟨k + 4 * ((M * E * O.adjugate * Wᵀ * M) i i + (M * W * O.adjugate * Eᵀ * M) i i) +
      32 * (M * E * O.adjugate * Eᵀ * M) i i, ?_⟩
    have e : M * (W + (8 : ℤ) • E) * O.adjugate * (W + (8 : ℤ) • E)ᵀ * M = M * W * O.adjugate * Wᵀ * M +
        (8 : ℤ) • (M * E * O.adjugate * Wᵀ * M + M * W * O.adjugate * Eᵀ * M) +
        (64 : ℤ) • (M * E * O.adjugate * Eᵀ * M) := by
      simp only [transpose_add, transpose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
        Matrix.mul_smul, smul_add, smul_smul]
      abel_nf
    rw [e, Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.add_apply, hk,
      smul_eq_mul, smul_eq_mul]
    ring

/-- **The proportion $\rho_O(M)$**: $8^{-ab}\,\#\{W \in M_{b\times a}(\mathbb Z/8) : W \text{ good}\}$ (`GoodO`). -/
noncomputable def rhoO (O : Matrix (Fin a) (Fin a) ℤ) (M : Matrix (Fin b) (Fin b) ℤ) : ℝ :=
  (Nat.card {W : Matrix (Fin b) (Fin a) (ZMod (2 ^ 3)) // GoodO O M (lift W)} : ℝ) / 8 ^ (b * a)

theorem allDvd_lift_reduce8 {r : ℕ} (hr : 3 ≤ r) [NeZero (2 ^ r)] (W : Matrix (Fin b) (Fin a) (ZMod (2 ^ r))) :
    AllDvd 8 (lift (W.map (ZMod.castHom (pow_dvd_pow 2 hr) (ZMod (2 ^ 3)))) - lift W) := by
  intro i j
  simp only [Matrix.sub_apply, lift, map_apply, ZMod.castHom_apply]
  rw [ZMod.cast_eq_val, ZMod.val_natCast]
  have h := Nat.mod_add_div (W i j).val (2 ^ 3)
  refine ⟨-(((W i j).val / 2 ^ 3 : ℕ) : ℤ), ?_⟩
  have h' : (((W i j).val % 2 ^ 3 : ℕ) : ℤ) + 2 ^ 3 * (((W i j).val / 2 ^ 3 : ℕ) : ℤ) = ((W i j).val : ℤ) := by
    exact_mod_cast h
  linarith

theorem goodO_iff_reduce {r : ℕ} (hr : 3 ≤ r) [NeZero (2 ^ r)] (hOs : Oᵀ = O) (hOd : ¬ 2 ∣ O.det) (hMs : Mᵀ = M)
    (W : Matrix (Fin b) (Fin a) (ZMod (2 ^ r))) :
    GoodO O M (lift (W.map (ZMod.castHom (pow_dvd_pow 2 hr) (ZMod (2 ^ 3))))) ↔ GoodO O M (lift W) := by
  have h := allDvd_lift_reduce8 hr W
  refine ⟨fun hg => goodO_of_allDvd hOs hOd hMs ?_ hg, fun hg => goodO_of_allDvd hOs hOd hMs h hg⟩
  have := allDvd_neg h
  rwa [neg_sub] at this

theorem castHom_surj8 {r : ℕ} (hr : 3 ≤ r) :
    Function.Surjective ((ZMod.castHom (pow_dvd_pow 2 hr) (ZMod (2 ^ 3))).toAddMonoidHom.mapMatrix :
      Matrix (Fin b) (Fin a) (ZMod (2 ^ r)) →+ Matrix (Fin b) (Fin a) (ZMod (2 ^ 3))) := by
  intro V
  have hs := ZMod.ringHom_surjective (ZMod.castHom (pow_dvd_pow 2 hr) (ZMod (2 ^ 3)))
  refine ⟨Matrix.of fun i j => Classical.choose (hs (V i j)), ?_⟩
  ext i j
  exact Classical.choose_spec (hs (V i j))

/-- **$\rho_O$ from any level $r \ge 3$.** -/
theorem card_goodO_div {r : ℕ} (hr : 3 ≤ r) [NeZero (2 ^ r)] (hOs : Oᵀ = O) (hOd : ¬ 2 ∣ O.det) (hMs : Mᵀ = M) :
    (Nat.card {W : Matrix (Fin b) (Fin a) (ZMod (2 ^ r)) // GoodO O M (lift W)} : ℝ) / (2 ^ r) ^ (b * a) =
      rhoO O M := by
  classical
  have := card_comp_div _ (castHom_surj8 (a := a) (b := b) hr) (fun V => GoodO O M (lift V))
  simp only [AddMonoidHom.mapMatrix_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe] at this
  simp only [goodO_iff_reduce hr hOs hOd hMs] at this
  unfold rhoO
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card, Fintype.card_subtype]
  convert this using 2
  · rw [Fintype.card_eq_nat_card, Matrix.card_matrix]
    simp [Nat.card_eq_fintype_card, ZMod.card, mul_comm]
  · rw [Fintype.card_eq_nat_card, Matrix.card_matrix]
    simp [Nat.card_eq_fintype_card, ZMod.card, mul_comm]

theorem blk_one_isSymm {U : Matrix (Fin a) (Fin a) ℤ} (hUs : U.IsSymm) (hMs : M.IsSymm) : (blk 1 U M).IsSymm := by
  unfold blk Matrix.IsSymm
  rw [Matrix.transpose_submatrix, fromBlocks_transpose, hUs.eq, transpose_smul, hMs.eq]
  simp only [transpose_zero]

theorem blk_one_det (U : Matrix (Fin a) (Fin a) ℤ) (M : Matrix (Fin b) (Fin b) ℤ) :
    (blk 1 U M).det = U.det * M.det := by
  unfold blk
  rw [Matrix.det_submatrix_equiv_self, det_fromBlocks_zero₂₁]
  simp

theorem not_pow_dvd_of_lt {d : ℤ} (hd : d ≠ 0) {r : ℕ} (hr : d.natAbs < r) : ¬ (2 : ℤ) ^ r ∣ d := by
  intro h
  have h1 : (2 ^ r : ℕ) ∣ d.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr h
    simpa using this
  have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr hd) h1
  have h3 : r < 2 ^ r := Nat.lt_two_pow_self
  omega

variable {L : List DyBlock}

/-- **$\alpha_2(O \perp M) = \rho_O(M)\,\alpha_2(O)\,\alpha_2(M)$** for $O$ the model of one or two blocks $u x^2$ of
exponent $0$ and $M$ symmetric with even diagonal, $\det M \ne 0$ (Conway–Sloane 1988, §12, p. 281; splitting off the
odd part of the unimodular constituent at $p = 2$). -/
@[kb "conwaysloane1988" "§12, p. 281 (splitting off the odd part of the unimodular constituent, p = 2)"]
theorem alphaP_blk_odd (hv : ∀ c ∈ L, c.Valid) (he : ∀ c ∈ L, blockExp c = 0) (ha : dyDim L = 1 ∨ dyDim L = 2)
    (hO2 : (intMat L).map (Int.castRingHom (ZMod 2)) = 1) (hMs : M.IsSymm) (hMe : EvenDiag M) (hM : M.det ≠ 0) :
    alphaP 2 (blk 1 (intMat L) M) = rhoO (intMat L) M * alphaP 2 (intMat L) * alphaP 2 M := by
  have hUs := isSymm_intMat L
  have hUd := det_odd_of_zero hv he
  have hU0 : (intMat L).det ≠ 0 := fun h => hUd (h ▸ dvd_zero _)
  have hd0 : (intMat L).det * M.det ≠ 0 := mul_ne_zero hU0 hM
  have hblk0 : (blk 1 (intMat L) M).det ≠ 0 := by rw [blk_one_det]; exact hd0
  obtain ⟨r1, h1⟩ := alphaP_stabilizes Nat.prime_two (blk_one_isSymm hUs hMs) hblk0
  obtain ⟨r2, h2⟩ := alphaP_stabilizes Nat.prime_two hUs hU0
  obtain ⟨r3, h3⟩ := alphaP_stabilizes Nat.prime_two hMs hM
  set r := max (max r1 r2) (max r3 (max 3 ((intMat L).det * M.det).natAbs.succ))
  have : NeZero (2 ^ r) := ⟨by positivity⟩
  have hr3 : 3 ≤ r := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hrd : ((intMat L).det * M.det).natAbs < r :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  rw [← h1 r (le_trans (le_max_left _ _) (le_max_left _ _)), ← h2 r (le_trans (le_max_right _ _) (le_max_left _ _)),
    ← h3 r (le_trans (le_max_left _ _) (le_max_right _ _)),
    countN_blk_odd hr3 hv he ha hO2 hMs.eq hMe (not_pow_dvd_of_lt hd0 hrd), tri_add,
    ← card_goodO_div hr3 hUs.eq hUd hMs.eq]
  push_cast
  rw [mul_add, mul_add, pow_add, pow_add, ← pow_mul, mul_comm (r : ℕ) (b * dyDim L)]
  push_cast
  field_simp

theorem goodO_zero : GoodO O M 0 := by
  refine ⟨?_, fun i => ⟨0, by simp⟩⟩
  unfold GoodO1
  simp only [transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero]
  exact ZpEquiv.refl _

theorem rhoO_pos : 0 < rhoO O M := by
  unfold rhoO
  have : NeZero (2 ^ 3) := ⟨by norm_num⟩
  have hne : Nonempty {W : Matrix (Fin b) (Fin a) (ZMod (2 ^ 3)) // GoodO O M (lift W)} :=
    ⟨⟨0, by
      have : lift (0 : Matrix (Fin b) (Fin a) (ZMod (2 ^ 3))) = 0 := by ext i j; simp [lift]
      rw [this]; exact goodO_zero⟩⟩
  have := Nat.card_pos (α := {W : Matrix (Fin b) (Fin a) (ZMod (2 ^ 3)) // GoodO O M (lift W)})
  positivity

end RhoO

end QuadFormsKB.ConwaySloane.Mass.Two
