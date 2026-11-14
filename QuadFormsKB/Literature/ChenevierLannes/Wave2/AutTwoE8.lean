/-
# Chenevier–Lannes: $|O(E_8 \oplus E_8)| \le 2\,|O(E_8)|^2$

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §3.3.1, p. 57 ($O(E_8 \oplus E_8)$ is the wreath product
$S_2 \wr O(E_8)$). Printed page numbers. Indices are 0-based.

**Layer.** $E_8 \oplus E_8$ is `Lattices.twoE8 = QuadForm.orthSum e8 e8`, an integral form in $16 = 8 + 8$ variables
whose Hessian is block diagonal with two copies of the Cartan matrix $E$ of $E_8$ (`Hanke2011Structure.hessian_orthSum`).
An automorphism is a matrix $g \in \mathrm{GL}_{16}(\mathbb{Z})$ with $g^{\mathsf T} H g = H$
(`Siegel.eval_mulVec_eq_iff_hessian`). We write $g$ in blocks $\begin{pmatrix} P & R \\ S & U \end{pmatrix}$ (indices
$\mathrm{Fin}\,8 \oplus \mathrm{Fin}\,8$, through `finSumFinEquiv`).

**Proves** (unconditional):
- `root_split`: a vector $(u, v)$ of $E_8 \oplus E_8$ of norm $2$ has $u = 0$ or $v = 0$ (both halves are positive
  definite and even);
- `e8_connected`: the Dynkin diagram of $E_8$ (the graph of the off-diagonal nonzero entries of $E$) is connected;
- `card_aut_twoE8_le`: $|O(E_8 \oplus E_8)| \le 2\,|O(E_8)|^2$.

**Method** (the book's argument, made explicit). The basis vectors are roots (norm $2$), so every column of $g$ is a
root, hence lies in one of the two summands (`root_split`). Two columns $i, j$ of the same summand with $E_{ij} \ne 0$
have images with nonzero inner product, so they lie in the same summand; by connectedness of the Dynkin diagram the
eight columns of each summand go to one summand. They cannot all go to the same one ($g$ is invertible). So either
$R = S = 0$ (then $P, U \in O(E_8)$), or $P = U = 0$ (then $S, R \in O(E_8)$): an injection of $O(E_8 \oplus E_8)$ into
$\{0, 1\} \times O(E_8) \times O(E_8)$. The bound is an equality (`card_aut_twoE8`, proved in `Witt.lean` from the mass).
-/
import QuadFormsKB.Literature.ChenevierLannes.Classification

open Matrix

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Lattices

/-- The Cartan matrix of $E_8$, as the Hessian of `Siegel.e8`. -/
local notation "E" => e8.hessian

/-- The Hessian of $E_8 \oplus E_8$ in block form: $\mathrm{diag}(E, E)$. -/
theorem twoE8_hessian_blocks :
    (twoE8.hessian : Matrix (Fin (8 + 8)) (Fin (8 + 8)) ℤ).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks E 0 0 E := by
  show (QuadForm.orthSum e8 e8).hessian.submatrix finSumFinEquiv finSumFinEquiv = _
  rw [Hanke2011Structure.hessian_orthSum]
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

/-- $u^{\mathsf T}Eu \ge 0$, with equality only for $u = 0$; in fact $u^{\mathsf T}Eu = 2\,E_8(u)$. -/
private theorem e8_quad (u : Fin 8 → ℤ) : u ⬝ᵥ (E *ᵥ u) = 2 * e8.eval u :=
  (LocalDensity.two_mul_eval_eq_hessian e8 u).symm

/-- **Roots of $E_8 \oplus E_8$ lie in one summand**: if $u^{\mathsf T}Eu + v^{\mathsf T}Ev = 2$ then $u = 0$ or
$v = 0$. -/
theorem root_split {u v : Fin 8 → ℤ} (h : u ⬝ᵥ (E *ᵥ u) + v ⬝ᵥ (E *ᵥ v) = 2) : u = 0 ∨ v = 0 := by
  rw [e8_quad, e8_quad] at h
  by_contra hne
  push_neg at hne
  have hu := e8_posDef u hne.1
  have hv := e8_posDef v hne.2
  omega

/-- **The Dynkin diagram of $E_8$ is connected**: a Boolean function on the vertices that is constant along the edges
($E_{ij} \ne 0$) is constant. -/
theorem e8_connected : ∀ f : Fin 8 → Bool, (∀ i j, E i j ≠ 0 → f i = f j) → ∀ i, f i = f 0 := by
  intro f hf
  have e : ∀ i j : Fin 8, CartanMatrix.E 8 i j ≠ 0 → f i = f j := by rw [← e8_hessian]; exact hf
  have h02 := e 0 2 (by decide)
  have h13 := e 1 3 (by decide)
  have h23 := e 2 3 (by decide)
  have h34 := e 3 4 (by decide)
  have h45 := e 4 5 (by decide)
  have h56 := e 5 6 (by decide)
  have h67 := e 6 7 (by decide)
  intro i
  fin_cases i
  · rfl
  · exact h13.trans (h23.symm.trans h02.symm)
  · exact h02.symm
  · exact h23.symm.trans h02.symm
  · exact h34.symm.trans (h23.symm.trans h02.symm)
  · exact h45.symm.trans (h34.symm.trans (h23.symm.trans h02.symm))
  · exact h56.symm.trans (h45.symm.trans (h34.symm.trans (h23.symm.trans h02.symm)))
  · exact h67.symm.trans (h56.symm.trans (h45.symm.trans (h34.symm.trans (h23.symm.trans h02.symm))))

/-- The diagonal entry $(A^{\mathsf T} E A)_{jj}$ is $c^{\mathsf T}Ec$ for the column $c$ of $A$. -/
private theorem diag_eq_quad (A : Matrix (Fin 8) (Fin 8) ℤ) (j : Fin 8) :
    (Aᵀ * E * A) j j = (fun c => A c j) ⬝ᵥ (E *ᵥ fun c => A c j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

/-- A column pair of the block $\begin{pmatrix} X \\ Y \end{pmatrix}$ of an automorphism: the relation
$X^{\mathsf T}EX + Y^{\mathsf T}EY = E$ (one diagonal block of $g^{\mathsf T}Hg = H$). -/
private theorem column_type {X Y : Matrix (Fin 8) (Fin 8) ℤ} (h : Xᵀ * E * X + Yᵀ * E * Y = E) :
    ∀ i, (fun c => X c i) = 0 ∨ (fun c => Y c i) = 0 := by
  have hd : ∀ i, E i i = 2 := by rw [e8_hessian]; decide
  intro i
  apply root_split
  have := congrFun (congrFun h i) i
  rw [Matrix.add_apply, diag_eq_quad, diag_eq_quad, hd] at this
  exact this

/-- In the situation of `column_type`, all eight columns are of the same type (connectedness of the Dynkin diagram). -/
private theorem column_type_const {X Y : Matrix (Fin 8) (Fin 8) ℤ} (h : Xᵀ * E * X + Yᵀ * E * Y = E) :
    (X = 0) ∨ (Y = 0) := by
  classical
  have ht := column_type h
  -- f i = true iff the column i of Y vanishes
  let f : Fin 8 → Bool := fun i => decide ((fun c => Y c i) = 0)
  have hX : ∀ i, f i = false → (fun c => X c i) = 0 := by
    intro i hi
    rcases ht i with h1 | h1
    · exact h1
    · simp [f, h1] at hi
  have hY : ∀ i, f i = true → (fun c => Y c i) = 0 := fun i hi => by simpa [f] using hi
  have hedge : ∀ i j, E i j ≠ 0 → f i = f j := by
    intro i j hij
    by_contra hne
    apply hij
    have e := congrFun (congrFun h i) j
    rw [← e, Matrix.add_apply]
    cases hfi : f i <;> cases hfj : f j <;> rw [hfi, hfj] at hne
    · exact absurd rfl hne
    · have h1 := congrFun (hX i hfi)
      have h2 := congrFun (hY j hfj)
      simp only [Pi.zero_apply] at h1 h2
      simp [Matrix.mul_apply, h1, h2]
    · have h1 := congrFun (hY i hfi)
      have h2 := congrFun (hX j hfj)
      simp only [Pi.zero_apply] at h1 h2
      simp [Matrix.mul_apply, h1, h2]
    · exact absurd rfl hne
  have hc := e8_connected f hedge
  cases h0 : f 0
  · left
    ext c i
    have := congrFun (hX i ((hc i).trans h0)) c
    simpa using this
  · right
    ext c i
    have := congrFun (hY i ((hc i).trans h0)) c
    simpa using this

/-- From $A^{\mathsf T}EA = E$: $A$ is an automorphism of $E_8$. -/
private noncomputable def toAutE8 (A : Matrix (Fin 8) (Fin 8) ℤ) (h : Aᵀ * E * A = E) : Aut e8 :=
  ⟨Matrix.nonsingInvUnit A (by
      have := congrArg Matrix.det h
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, e8_det] at this
      exact IsUnit.of_mul_eq_one (A.det) (by linarith)),
    (eval_mulVec_eq_iff_hessian e8 e8 A).mpr h⟩

private theorem toAutE8_val (A : Matrix (Fin 8) (Fin 8) ℤ) (h : Aᵀ * E * A = E) :
    ((toAutE8 A h : GL (Fin 8) ℤ) : Matrix (Fin 8) (Fin 8) ℤ) = A := rfl

/-- **Block form of an automorphism of $E_8 \oplus E_8$**: either $g = \mathrm{diag}(X, Y)$ or
$g = \begin{pmatrix} 0 & Y \\ X & 0 \end{pmatrix}$ with $X, Y \in O(E_8)$. -/
private theorem aut_twoE8_blocks (g : Aut twoE8) : ∃ b : Bool, ∃ X Y : Aut e8,
    (((g : GL (Fin 16) ℤ) : Matrix (Fin 16) (Fin 16) ℤ) : Matrix (Fin (8 + 8)) (Fin (8 + 8)) ℤ).submatrix
        (finSumFinEquiv : Fin 8 ⊕ Fin 8 ≃ Fin (8 + 8)) (finSumFinEquiv : Fin 8 ⊕ Fin 8 ≃ Fin (8 + 8)) =
      if b then Matrix.fromBlocks 0 ((Y : GL (Fin 8) ℤ) : Matrix (Fin 8) (Fin 8) ℤ)
        ((X : GL (Fin 8) ℤ) : Matrix (Fin 8) (Fin 8) ℤ) 0
      else Matrix.fromBlocks ((X : GL (Fin 8) ℤ) : Matrix (Fin 8) (Fin 8) ℤ) 0 0
        ((Y : GL (Fin 8) ℤ) : Matrix (Fin 8) (Fin 8) ℤ) := by
  set M : Matrix (Fin (8 + 8)) (Fin (8 + 8)) ℤ := ((g : GL (Fin 16) ℤ) : Matrix (Fin 16) (Fin 16) ℤ) with hM
  set G := M.submatrix finSumFinEquiv finSumFinEquiv with hG
  have hgH : Mᵀ * twoE8.hessian * M = twoE8.hessian := (eval_mulVec_eq_iff_hessian twoE8 twoE8 M).mp g.2
  have hGH : Gᵀ * Matrix.fromBlocks E 0 0 E * G = Matrix.fromBlocks E 0 0 E := by
    rw [← twoE8_hessian_blocks, hG, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, hgH]
  -- invertibility: G has a right inverse
  have hinv : ∃ K : Matrix (Fin 8 ⊕ Fin 8) (Fin 8 ⊕ Fin 8) ℤ, G * K = 1 := by
    refine ⟨(((g : GL (Fin 16) ℤ)⁻¹ : GL (Fin 16) ℤ) : Matrix (Fin (8 + 8)) (Fin (8 + 8)) ℤ).submatrix
      finSumFinEquiv finSumFinEquiv, ?_⟩
    rw [hG, Matrix.submatrix_mul_equiv, hM, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.submatrix_one_equiv]
  obtain ⟨K, hK⟩ := hinv
  rw [← Matrix.fromBlocks_toBlocks G] at hGH hK
  set P := G.toBlocks₁₁
  set R := G.toBlocks₁₂
  set S := G.toBlocks₂₁
  set U := G.toBlocks₂₂
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hGH
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hGH
  obtain ⟨h11, -, -, h22⟩ := Matrix.fromBlocks_inj.mp hGH
  -- a zero top (or bottom) block row contradicts G K = 1
  rcases column_type_const h11 with hP | hS <;> rcases column_type_const h22 with hR | hU
  · -- P = 0, R = 0: the top block row of G vanishes
    exfalso
    have := congrFun (congrFun hK (Sum.inl 0)) (Sum.inl 0)
    simp [Matrix.mul_apply, Fintype.sum_sum_type, hP, hR] at this
  · -- P = 0, U = 0: swap
    refine ⟨true, toAutE8 S (by simpa [hP] using h11), toAutE8 R (by simpa [hU] using h22), ?_⟩
    simp only [toAutE8_val, ite_true]
    rw [← Matrix.fromBlocks_toBlocks G]
    rw [show G.toBlocks₁₁ = 0 from hP, show G.toBlocks₂₂ = 0 from hU]
  · -- S = 0, R = 0: no swap
    refine ⟨false, toAutE8 P (by simpa [hS] using h11), toAutE8 U (by simpa [hR] using h22), ?_⟩
    simp only [toAutE8_val, Bool.false_eq_true, ite_false]
    rw [← Matrix.fromBlocks_toBlocks G]
    rw [show G.toBlocks₂₁ = 0 from hS, show G.toBlocks₁₂ = 0 from hR]
  · -- S = 0, U = 0: the bottom block row of G vanishes
    exfalso
    have := congrFun (congrFun hK (Sum.inr 0)) (Sum.inr 0)
    simp [Matrix.mul_apply, Fintype.sum_sum_type, hS, hU] at this

/-- **$|O(E_8 \oplus E_8)| \le 2\,|O(E_8)|^2$** (Chenevier–Lannes, §3.3.1, p. 57: $O(E_8 \oplus E_8) = S_2 \wr O(E_8)$):
every automorphism of $E_8 \oplus E_8$ preserves or exchanges the two summands $E_8$. Unconditional. -/
@[kb "chenevierlannes2019" "§3.3.1, p. 57 (O(E_8 ⊕ E_8) ⊆ S_2 ≀ O(E_8))"]
theorem card_aut_twoE8_le : Nat.card (Aut twoE8) ≤ 2 * Nat.card (Aut e8) ^ 2 := by
  classical
  have : Finite (Aut e8) := Nat.finite_of_card_ne_zero e8_posDef.card_aut_pos.ne'
  choose b X Y hXY using aut_twoE8_blocks
  let Φ : Aut twoE8 → Bool × Aut e8 × Aut e8 := fun g => (b g, X g, Y g)
  have hΦ : Function.Injective Φ := by
    intro g g' h
    simp only [Φ, Prod.mk.injEq] at h
    obtain ⟨hb, hX, hY⟩ := h
    have e := hXY g
    rw [hb, hX, hY, ← hXY g'] at e
    apply Subtype.ext; apply Units.ext
    have := congrArg (fun N => N.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) e
    simpa [Matrix.submatrix_submatrix] using this
  calc Nat.card (Aut twoE8) ≤ Nat.card (Bool × Aut e8 × Aut e8) := Nat.card_le_card_of_injective Φ hΦ
    _ = 2 * Nat.card (Aut e8) ^ 2 := by
      rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
      ring

end QuadFormsKB.ChenevierLannes
