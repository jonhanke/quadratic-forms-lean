/-
# The block count identity for $N(p^r)$ (Conway–Sloane 1988, (3) and (18))

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), (18), p. 281, and (3), p. 263 (bibliography key `conwaysloane1988`).

The $p$-adic density $\alpha_p(f)$ is the limit of $N(p^r)p^{-rn(n-1)/2}$, where $N(p^r)$ counts the $X$ modulo $p^r$
with $X^{\mathsf T}AX \equiv A$ (`countN`). This file proves, over an arbitrary commutative ring $R$, the identity that
splits off a unimodular constituent: for the block matrix $A = \begin{pmatrix}U & 0\\0 & \pi B\end{pmatrix}$ with
$\det U$ a unit and $\pi$ nilpotent (over $\mathbb Z/p^r$: $\pi = p$),
$$\#\{X : X^{\mathsf T}AX = A\} = \sum_{W}\#\{Y : Y^{\mathsf T}(U + W^{\mathsf T}\pi BW)Y = U\}\cdot
  \#\{Z : Z^{\mathsf T}(\pi B + \pi BWU^{-1}W^{\mathsf T}\pi B)Z = \pi B\}$$
(`card_fromBlocks_eq_sum`, $W$ running over the $b\times a$ matrices), by the change of variables
$X = \begin{pmatrix}Y & -U^{-1}W^{\mathsf T}\pi BZ\\ WY & Z\end{pmatrix}$. When $2$ is a unit in $R$ both perturbed forms
are congruent to the unperturbed ones (`exists_congr_one_add`: $S(1+M) = G^{\mathsf T}SG$ for $G$ a square root of
$1 + M$ that is a polynomial in $M$), so
$$\#\{X : X^{\mathsf T}AX = A\} = |R|^{ab}\cdot\#\{Y : Y^{\mathsf T}UY = U\}\cdot\#\{Z : Z^{\mathsf T}\pi BZ = \pi B\}
\qquad(\text{`card\_fromBlocks\_odd`}).$$
At $p = 2$ the identity `card_fromBlocks_eq_sum` still holds, but the perturbed forms need not be congruent to $U$ and
$\pi B$. Indices of the blocks are arbitrary finite types; there is no 1-based shift.
-/
import Mathlib
import QuadFormsKB.Citation

set_option linter.unusedSectionVars false

namespace QuadFormsKB.ConwaySloane.Mass

open Matrix Polynomial

section Sqrt

variable {R : Type*} [CommRing R]

/-- A polynomial square root of $1 + X$ modulo $X^N$ when $2$ is a unit (Newton's method,
`Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero`). -/
theorem exists_poly_sqrt (h2 : IsUnit (2 : R)) (N : ℕ) : ∃ g : R[X], (X : R[X]) ^ N ∣ g ^ 2 - (1 + X) := by
  let I : Ideal R[X] := Ideal.span {(X : R[X]) ^ N}
  let x : R[X] ⧸ I := Ideal.Quotient.mk I X
  have hx : IsNilpotent x := ⟨N, by
    simp only [x, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, I]
    exact Ideal.mem_span_singleton_self _⟩
  let P : (R[X] ⧸ I)[X] := X ^ 2 - Polynomial.C (1 + x)
  have h1 : IsNilpotent (aeval (1 : R[X] ⧸ I) P) := by
    have : aeval (1 : R[X] ⧸ I) P = -x := by simp [P]
    rw [this]; exact hx.neg
  have h2' : IsUnit (aeval (1 : R[X] ⧸ I) (derivative P)) := by
    have : aeval (1 : R[X] ⧸ I) (derivative P) = 2 := by
      simp [P]; norm_num
    rw [this]; have h := h2.map (algebraMap R (R[X] ⧸ I)); rwa [map_ofNat] at h
  obtain ⟨r, -, hr⟩ := (existsUnique_nilpotent_sub_and_aeval_eq_zero h1 h2').exists
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective r
  refine ⟨g, ?_⟩
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  have : aeval (Ideal.Quotient.mk I g) P = Ideal.Quotient.mk I (g ^ 2 - (1 + X)) := by
    simp [P, x]
  rw [← this]; exact hr

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A square root of $1 + M$ for a nilpotent matrix $M$, as a polynomial in $M$, when $2$ is a unit. -/
theorem exists_aeval_sq (h2 : IsUnit (2 : R)) {M : Matrix n n R} (hM : IsNilpotent M) :
    ∃ g : R[X], (aeval M g) ^ 2 = 1 + M := by
  obtain ⟨N, hN⟩ := hM
  obtain ⟨g, q, hq⟩ := exists_poly_sqrt h2 N
  refine ⟨g, ?_⟩
  have := congrArg (aeval M) hq
  simp only [map_sub, map_pow, map_add, map_one, aeval_X, map_mul, hN, zero_mul] at this
  exact sub_eq_zero.mp this

theorem transpose_aeval_mul {S M : Matrix n n R} (hSM : Mᵀ * S = S * M) (g : R[X]) :
    (aeval M g)ᵀ * S = S * aeval M g := by
  have hpow : ∀ k : ℕ, (M ^ k)ᵀ * S = S * M ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', transpose_mul, Matrix.mul_assoc, hSM, ← Matrix.mul_assoc, ih, Matrix.mul_assoc,
        ← pow_succ, pow_succ']
  induction g using Polynomial.induction_on' with
  | add p q hp hq => simp [transpose_add, Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial k a =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.one_mul,
      transpose_smul, Matrix.mul_smul, hpow]

/-- **Congruence of a nilpotent perturbation** (the odd-$p$ step of `card_fromBlocks_odd`): if $2$ is a unit, $S$ is
symmetric, $M$ is nilpotent and $SM$ is symmetric ($M^{\mathsf T}S = SM$), then $S(1 + M) = G^{\mathsf T}SG$ for an
invertible $G$ (a square root of $1 + M$). -/
theorem exists_congr_one_add (h2 : IsUnit (2 : R)) {S M : Matrix n n R} (hSM : Mᵀ * S = S * M)
    (hM : IsNilpotent M) : ∃ G : Matrix n n R, IsUnit G ∧ Gᵀ * S * G = S * (1 + M) := by
  obtain ⟨g, hg⟩ := exists_aeval_sq h2 hM
  refine ⟨aeval M g, ?_, ?_⟩
  · have hu : IsUnit ((aeval M g) * (aeval M g)) := by
      rw [← sq, hg, add_comm]; exact hM.isUnit_add_one
    exact isUnit_of_mul_isUnit_left hu
  · rw [transpose_aeval_mul hSM, Matrix.mul_assoc, ← sq, hg]

end Sqrt

section Count

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Counting solutions is invariant under a congruence $S \mapsto G^{\mathsf T}SG$ with $G$ invertible. -/
theorem card_congr_unit {G : Matrix ι ι R} (hG : IsUnit G) (S T : Matrix ι ι R) :
    Nat.card {Y : Matrix ι ι R // Yᵀ * (Gᵀ * S * G) * Y = T} = Nat.card {Y : Matrix ι ι R // Yᵀ * S * Y = T} := by
  obtain ⟨u, rfl⟩ := hG
  refine Nat.card_congr
    { toFun := fun Y => ⟨(u : Matrix ι ι R) * Y.1, by
        have h := Y.2; rw [transpose_mul]; simpa only [Matrix.mul_assoc] using h⟩
      invFun := fun Y => ⟨(↑u⁻¹ : Matrix ι ι R) * Y.1, by
        have h := Y.2
        rw [transpose_mul]
        have e : (Y.1ᵀ * (↑u⁻¹ : Matrix ι ι R)ᵀ) * ((u : Matrix ι ι R)ᵀ * S * (u : Matrix ι ι R)) * ((↑u⁻¹ : Matrix ι ι R) * Y.1)
            = Y.1ᵀ * ((u : Matrix ι ι R) * (↑u⁻¹ : Matrix ι ι R))ᵀ * S *
              ((u : Matrix ι ι R) * (↑u⁻¹ : Matrix ι ι R)) * Y.1 := by
          simp only [transpose_mul, Matrix.mul_assoc]
        rw [e, Units.mul_inv, transpose_one, Matrix.mul_one, Matrix.mul_one]; exact h⟩
      left_inv := fun Y => Subtype.ext (by simp [← Matrix.mul_assoc])
      right_inv := fun Y => Subtype.ext (by simp [← Matrix.mul_assoc]) }

/-- If $\pi$ is nilpotent, $U - \pi K$ has a unit determinant whenever $U$ does. -/
theorem isUnit_det_sub_smul {U : Matrix ι ι R} (hU : IsUnit U.det) {π : R} (hπ : IsNilpotent π)
    (K : Matrix ι ι R) : IsUnit (U - π • K).det := by
  have hUu : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).mpr hU
  have hN : IsNilpotent (π • (U⁻¹ * K)) := by
    obtain ⟨k, hk⟩ := hπ
    exact ⟨k, by rw [_root_.smul_pow, hk, zero_smul]⟩
  have h1 : IsUnit (1 - π • (U⁻¹ * K)) := by
    rw [sub_eq_add_neg, add_comm]; exact hN.neg.isUnit_add_one
  have : U - π • K = U * (1 - π • (U⁻¹ * K)) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU,
      Matrix.one_mul]
  rw [this, Matrix.det_mul]
  exact hU.mul ((Matrix.isUnit_iff_isUnit_det _).mp h1)

end Count

section Blocks

variable {R : Type*} [CommRing R] {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

/-- The perturbed first block $U + W^{\mathsf T}CW$. -/
def pertU (U : Matrix a a R) (C : Matrix b b R) (W : Matrix b a R) : Matrix a a R := U + Wᵀ * C * W

/-- The perturbed second block $C + CWU^{-1}W^{\mathsf T}C$. -/
noncomputable def pertC (U : Matrix a a R) (C : Matrix b b R) (W : Matrix b a R) : Matrix b b R :=
  C + C * W * U⁻¹ * Wᵀ * C

/-- The block matrix $\begin{pmatrix}Y & -U^{-1}W^{\mathsf T}CZ\\ WY & Z\end{pmatrix}$ of the change of variables. -/
noncomputable def blockSol (U : Matrix a a R) (C : Matrix b b R) (W : Matrix b a R) (Y : Matrix a a R)
    (Z : Matrix b b R) : Matrix (a ⊕ b) (a ⊕ b) R :=
  fromBlocks Y (-(U⁻¹ * Wᵀ * C * Z)) (W * Y) Z

variable {U : Matrix a a R} {C : Matrix b b R}

omit [DecidableEq b] in
theorem blockSol_eqn (hUs : Uᵀ = U) (hU : IsUnit U.det) (hCs : Cᵀ = C) (W : Matrix b a R) (Y : Matrix a a R)
    (Z : Matrix b b R) :
    (blockSol U C W Y Z)ᵀ * fromBlocks U 0 0 C * blockSol U C W Y Z =
      fromBlocks (Yᵀ * pertU U C W * Y) 0 0 (Zᵀ * pertC U C W * Z) := by
  have hUi : U⁻¹ᵀ = U⁻¹ := by rw [transpose_nonsing_inv, hUs]
  have h1 : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv _ hU
  have h2 : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul _ hU
  simp only [blockSol, fromBlocks_transpose, fromBlocks_multiply, pertU, pertC, transpose_neg, transpose_mul,
    hUi, hCs, transpose_transpose, Matrix.mul_zero, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg]
  congr 1
  · simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U, h1, Matrix.one_mul, neg_add_cancel]
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U⁻¹ U, h2, Matrix.one_mul, neg_add_cancel]
  · simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, neg_neg]
    rw [← Matrix.mul_assoc U⁻¹ U, h2, Matrix.one_mul, add_comm]

omit [DecidableEq a] [DecidableEq b] in
/-- The blocks of $X^{\mathsf T}AX$ for $A = U \oplus C$. -/
theorem fromBlocks_eqn (P : Matrix a a R) (Q : Matrix a b R) (S : Matrix b a R) (Z : Matrix b b R) :
    (fromBlocks P Q S Z)ᵀ * fromBlocks U 0 0 C * fromBlocks P Q S Z =
      fromBlocks (Pᵀ * U * P + Sᵀ * C * S) (Pᵀ * U * Q + Sᵀ * C * Z) (Qᵀ * U * P + Zᵀ * C * S)
        (Qᵀ * U * Q + Zᵀ * C * Z) := by
  simp [fromBlocks_transpose, fromBlocks_multiply]

/-- Every solution has the shape `blockSol`: its first diagonal block is invertible (the entries of $C$ are
multiples of the nilpotent $\pi$) and its upper right block is $-U^{-1}W^{\mathsf T}CZ$, $W = X_{21}X_{11}^{-1}$. -/
theorem eq_blockSol (hU : IsUnit U.det) {π : R} (hπ : IsNilpotent π) {B : Matrix b b R}
    (hC : C = π • B) {X : Matrix (a ⊕ b) (a ⊕ b) R} (hX : Xᵀ * fromBlocks U 0 0 C * X = fromBlocks U 0 0 C) :
    IsUnit X.toBlocks₁₁.det ∧
      X = blockSol U C (X.toBlocks₂₁ * X.toBlocks₁₁⁻¹) X.toBlocks₁₁ X.toBlocks₂₂ := by
  set P := X.toBlocks₁₁; set Q := X.toBlocks₁₂; set S := X.toBlocks₂₁; set Z := X.toBlocks₂₂
  have hXe : X = fromBlocks P Q S Z := (fromBlocks_toBlocks X).symm
  rw [hXe, fromBlocks_eqn] at hX
  obtain ⟨e11, e12, -, -⟩ := fromBlocks_inj.mp hX
  -- the first block is invertible
  have hP : IsUnit P.det := by
    have e : Pᵀ * U * P = U - π • (Sᵀ * B * S) := by
      have h' : Sᵀ * C * S = π • (Sᵀ * B * S) := by rw [hC]; simp [Matrix.mul_smul, Matrix.smul_mul]
      rw [← h', eq_sub_iff_add_eq, e11]
    have hu := isUnit_det_sub_smul hU hπ (Sᵀ * B * S)
    rw [← e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hu
    exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hu)
  refine ⟨hP, ?_⟩
  have hPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hP
  have hPi' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hP
  have hS : S * P⁻¹ * P = S := by rw [Matrix.mul_assoc, hPi', Matrix.mul_one]
  -- the upper right block
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

/-- The fiber over $W$ of the change of variables. -/
theorem card_fiber (hUs : Uᵀ = U) (hU : IsUnit U.det) (hCs : Cᵀ = C) {π : R} (hπ : IsNilpotent π)
    {B : Matrix b b R} (hC : C = π • B) (W : Matrix b a R) :
    Nat.card {X : {X : Matrix (a ⊕ b) (a ⊕ b) R // Xᵀ * fromBlocks U 0 0 C * X = fromBlocks U 0 0 C} //
        X.1.toBlocks₂₁ * X.1.toBlocks₁₁⁻¹ = W} =
      Nat.card ({Y : Matrix a a R // Yᵀ * pertU U C W * Y = U} × {Z : Matrix b b R // Zᵀ * pertC U C W * Z = C}) := by
  refine Nat.card_congr
    { toFun := fun X => (⟨X.1.1.toBlocks₁₁, ?_⟩, ⟨X.1.1.toBlocks₂₂, ?_⟩)
      invFun := fun YZ => ⟨⟨blockSol U C W YZ.1.1 YZ.2.1, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · obtain ⟨-, h⟩ := eq_blockSol hU hπ hC X.1.2
    have h2 := X.1.2
    rw [h, blockSol_eqn hUs hU hCs, X.2] at h2
    exact (fromBlocks_inj.mp h2).1
  · obtain ⟨-, h⟩ := eq_blockSol hU hπ hC X.1.2
    have h2 := X.1.2
    rw [h, blockSol_eqn hUs hU hCs, X.2] at h2
    exact (fromBlocks_inj.mp h2).2.2.2
  · rw [blockSol_eqn hUs hU hCs, YZ.1.2, YZ.2.2]
  · -- the first block of a solution is invertible
    have hY : IsUnit YZ.1.1.det := by
      have h := congrArg Matrix.det YZ.1.2
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
      rw [← h] at hU
      exact isUnit_of_mul_isUnit_right hU
    simp only [blockSol, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₁₁]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hY, Matrix.mul_one]
  · rintro ⟨⟨X, hX⟩, rfl⟩
    obtain ⟨-, h⟩ := eq_blockSol hU hπ hC hX
    exact Subtype.ext (Subtype.ext h.symm)
  · intro YZ
    simp [blockSol]

/-- **The block count identity** (all $p$): for $A = U \oplus \pi B$ with $U$ symmetric with unit determinant, $B$
symmetric and $\pi$ nilpotent,
$\#\{X : X^{\mathsf T}AX = A\} = \sum_W \#\{Y : Y^{\mathsf T}(U + W^{\mathsf T}\pi BW)Y = U\}\cdot
\#\{Z : Z^{\mathsf T}(\pi B + \pi BWU^{-1}W^{\mathsf T}\pi B)Z = \pi B\}$. -/
@[kb "conwaysloane1988" "(18), p. 281 (splitting off a unimodular constituent)"]
theorem card_fromBlocks_eq_sum [Fintype R] (hUs : Uᵀ = U) (hU : IsUnit U.det) (hCs : Cᵀ = C) {π : R}
    (hπ : IsNilpotent π) {B : Matrix b b R} (hC : C = π • B) :
    Nat.card {X : Matrix (a ⊕ b) (a ⊕ b) R // Xᵀ * fromBlocks U 0 0 C * X = fromBlocks U 0 0 C} =
      ∑ W : Matrix b a R, Nat.card {Y : Matrix a a R // Yᵀ * pertU U C W * Y = U} *
        Nat.card {Z : Matrix b b R // Zᵀ * pertC U C W * Z = C} := by
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv fun X : {X : Matrix (a ⊕ b) (a ⊕ b) R //
      Xᵀ * fromBlocks U 0 0 C * X = fromBlocks U 0 0 C} => X.1.toBlocks₂₁ * X.1.toBlocks₁₁⁻¹), Nat.card_sigma]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [card_fiber hUs hU hCs hπ hC W, Nat.card_prod]

theorem isNilpotent_smul {π : R} (hπ : IsNilpotent π) {m : Type*} [Fintype m] [DecidableEq m]
    (N : Matrix m m R) : IsNilpotent (π • N) := by
  obtain ⟨k, hk⟩ := hπ
  exact ⟨k, by rw [_root_.smul_pow, hk, zero_smul]⟩

/-- **The block count identity when $2$ is a unit** (odd $p$): for $A = U \oplus \pi B$ ($U$ symmetric with unit
determinant, $B$ symmetric, $\pi$ nilpotent),
$\#\{X : X^{\mathsf T}AX = A\} = |R|^{ab}\,\#\{Y : Y^{\mathsf T}UY = U\}\,\#\{Z : Z^{\mathsf T}\pi BZ = \pi B\}$. -/
@[kb "conwaysloane1988" "(18), p. 281 (splitting off a unimodular constituent, p odd)"]
theorem card_fromBlocks_odd [Fintype R] (h2 : IsUnit (2 : R)) (hUs : Uᵀ = U) (hU : IsUnit U.det) {π : R}
    (hπ : IsNilpotent π) {B : Matrix b b R} (hBs : Bᵀ = B) :
    Nat.card {X : Matrix (a ⊕ b) (a ⊕ b) R // Xᵀ * fromBlocks U 0 0 (π • B) * X = fromBlocks U 0 0 (π • B)} =
      Fintype.card (Matrix b a R) * Nat.card {Y : Matrix a a R // Yᵀ * U * Y = U} *
        Nat.card {Z : Matrix b b R // Zᵀ * (π • B) * Z = π • B} := by
  have hCs : (π • B)ᵀ = π • B := by rw [transpose_smul, hBs]
  have hUi : U⁻¹ᵀ = U⁻¹ := by rw [transpose_nonsing_inv, hUs]
  rw [card_fromBlocks_eq_sum hUs hU hCs hπ rfl, mul_assoc, ← Finset.card_univ, ← smul_eq_mul,
    ← Finset.sum_const]
  refine Finset.sum_congr rfl fun W _ => ?_
  congr 1
  · -- the first block: `U + WᵀCW = U(1 + M)`
    obtain ⟨G, hG, hGe⟩ := exists_congr_one_add h2 (S := U) (M := U⁻¹ * (Wᵀ * (π • B) * W))
      (by rw [transpose_mul, hUi, transpose_mul, transpose_mul, hCs, transpose_transpose, Matrix.mul_assoc,
            Matrix.nonsing_inv_mul _ hU, Matrix.mul_one, ← Matrix.mul_assoc U U⁻¹, Matrix.mul_nonsing_inv _ hU,
            Matrix.one_mul, Matrix.mul_assoc])
      (by
        have : U⁻¹ * (Wᵀ * (π • B) * W) = π • (U⁻¹ * (Wᵀ * B * W)) := by
          simp [Matrix.mul_smul, Matrix.smul_mul]
        rw [this]; exact isNilpotent_smul hπ _)
    have e : pertU U (π • B) W = Gᵀ * U * G := by
      rw [hGe, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU, Matrix.one_mul,
        pertU]
    rw [e, card_congr_unit hG]
  · -- the second block: `C + CWU⁻¹WᵀC = C(1 + M')`
    obtain ⟨G, hG, hGe⟩ := exists_congr_one_add h2 (S := π • B) (M := W * U⁻¹ * Wᵀ * (π • B))
      (by
        rw [transpose_mul, transpose_mul, transpose_mul, hCs, hUi, transpose_transpose]
        simp only [Matrix.mul_assoc])
      (by
        have : W * U⁻¹ * Wᵀ * (π • B) = π • (W * U⁻¹ * Wᵀ * B) := by
          simp
        rw [this]; exact isNilpotent_smul hπ _)
    have e : pertC U (π • B) W = Gᵀ * (π • B) * G := by
      rw [hGe, Matrix.mul_add, Matrix.mul_one, pertC]
      simp only [Matrix.mul_assoc]
    rw [e, card_congr_unit hG]

end Blocks

end QuadFormsKB.ConwaySloane.Mass
