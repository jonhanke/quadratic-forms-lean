/-
# Cassels, Chapter 9, Example 15 (iv): the possible orders of the group of proper integral automorphs

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 9, *Examples*, Ex. 15 (iv) (p. 166). Indices are
0-based: Cassels' variables $x, y, z$ are $x_0, x_1, x_2$ here.

**Statement** (`ex15ivOrders`, the named statement `Ch9Ex6.Ex15ivOrders` of `Ex6Ex15.lean`, now proved): for every
positive definite rational ternary form $Q$ the group $\mathrm{RatAutPlus}(Q)$ of proper integral automorphs
($T \in \mathrm{GL}_3(\mathbb Z)$, $\det T = 1$, $Q(T\vec x) = Q(\vec x)$) has order $1, 2, 4, 6, 8, 12$ or $24$. The
converse (each of these orders occurs) is `Ch9Ex6.ex15_iv_occur`. Unconditional: no assumed inputs.

**Proof** (reconstructed; Cassels gives only a hint): the classical counting of poles of a finite group of rotations,
done in exact arithmetic.
* *Rotations* (`Def`, `IsRot`, `bil`): $A$ the Gram matrix of $Q$ (symmetric, positive on nonzero rational vectors);
  an automorph $g$ has $g^{\mathsf T}Ag = A$ and $\det g = 1$. Then $\det(g - 1) = 0$ (`IsRot.det_sub_one`), so $g$ fixes a
  nonzero vector, and the cross product satisfies $g\,A^{-1}(v \times w) = A^{-1}\bigl((gv) \times (gw)\bigr)$
  (`IsRot.equivariant`). A rotation fixing two vectors with nonzero cross product also fixes
  $A^{-1}(v \times w)$, hence fixes three independent vectors and is the identity (`IsRot.eq_one_of_fixed_two`).
* *Cyclic stabilisers* (`stab_cyclic`): a finite group of rotations all fixing a vector $e \ne 0$ commutes with
  $y \mapsto A^{-1}(e \times y)$; in an orthogonal basis $e, x, A^{-1}(e \times x)$ it acts on $x$ by
  $x \mapsto a x + b\,A^{-1}(e \times x)$, and $h \mapsto a + b\sqrt{\lambda}\,i$ is an injective homomorphism into
  $\mathbb C$, so the group is cyclic (finite subgroups of the unit group of a domain are cyclic).
* *Poles* (`Prim`, `Pole`, `PoleSet`): primitive integer vectors fixed by some automorph $\ne 1$. A nonidentity
  automorph fixes exactly two of them, $\pm e$ (`card_fixedBy`); the group permutes the poles. The stabiliser of a
  pole is cyclic, nontrivial, with element orders in $\{1, 2, 3, 4, 6\}$ by Example 15 (i)
  (`Siegel.orderOf_mem_of_proper_automorph`), hence has order $2, 3, 4$ or $6$ (`stab_card`).
* *Counting* (`count_classify`, `diophantine`): Burnside's lemma and the orbit-stabiliser formula give
  $\sum_\omega N/n_\omega + 2N = kN + 2$, whose solutions with $n_\omega \in \{2, 3, 4, 6\}$, $n_\omega \mid N$ are
  $N \in \{1, 2, 3, 4, 6, 8, 12, 24\}$ (cyclic, dihedral, tetrahedral and octahedral cases).
* *Excluding $N = 3$* (`card_ratAutPlus_mem`): an element of order $3$ forces one of order $2$ by Example 15 (ii)
  (`Ch9Ex6.ex15_ii`), impossible in a group of order $3$.

*Errata/updates:* none found.
-/
import QuadFormsKB.Literature.Cassels.Ch9.Ex6Ex15

open Matrix

namespace QuadFormsKB.Cassels.Ch9Ex15Orders

/-- Helper: the bilinear form $B_A(x, y) = x^{\mathsf T} A y$. -/
def bil (A : Matrix (Fin 3) (Fin 3) ℚ) (x y : Fin 3 → ℚ) : ℚ := x ⬝ᵥ (A *ᵥ y)

/-- Helper: a symmetric rational matrix, positive on nonzero vectors. -/
structure Def (A : Matrix (Fin 3) (Fin 3) ℚ) : Prop where
  symm : Aᵀ = A
  pos : ∀ x : Fin 3 → ℚ, x ≠ 0 → 0 < bil A x x

/-- Helper: a rotation for `A`: $g^{\mathsf T}Ag = A$, $\det g = 1$. -/
structure IsRot (A g : Matrix (Fin 3) (Fin 3) ℚ) : Prop where
  orth : gᵀ * A * g = A
  det : g.det = 1

section
variable {A : Matrix (Fin 3) (Fin 3) ℚ}

/-- Helper: moving a matrix across the dot product, $(g x) \cdot w = x \cdot (g^{\mathsf T} w)$. -/
theorem mulVec_dot (g : Matrix (Fin 3) (Fin 3) ℚ) (x w : Fin 3 → ℚ) :
    (g *ᵥ x) ⬝ᵥ w = x ⬝ᵥ (gᵀ *ᵥ w) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]

/-- Helper: symmetry $B_A(x, y) = B_A(y, x)$ of the form of a definite matrix `A` (`hA`). -/
theorem bil_comm (hA : Def A) (x y : Fin 3 → ℚ) : bil A x y = bil A y x := by
  unfold bil
  rw [Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, hA.symm]

/-- Helper: additivity of $B_A(x, \cdot)$ in the second argument. -/
theorem bil_add_right (x y z : Fin 3 → ℚ) : bil A x (y + z) = bil A x y + bil A x z := by
  simp [bil, Matrix.mulVec_add, dotProduct_add]

/-- Helper: $B_A(x, c y) = c\,B_A(x, y)$ for a scalar `c`. -/
theorem bil_smul_right (x y : Fin 3 → ℚ) (c : ℚ) : bil A x (c • y) = c * bil A x y := by
  simp [bil, Matrix.mulVec_smul, dotProduct_smul]

/-- Helper: additivity of $B_A$ in the first argument (`hA`: `A` definite). -/
theorem bil_add_left (hA : Def A) (x y z : Fin 3 → ℚ) : bil A (x + y) z = bil A x z + bil A y z := by
  rw [bil_comm hA, bil_add_right, bil_comm hA z x, bil_comm hA z y]

/-- Helper: $B_A(c x, y) = c\,B_A(x, y)$ (`hA`: `A` definite). -/
theorem bil_smul_left (hA : Def A) (x y : Fin 3 → ℚ) (c : ℚ) : bil A (c • x) y = c * bil A x y := by
  rw [bil_comm hA, bil_smul_right, bil_comm hA y x]

/-- Helper: $B_A(x, 0) = 0$. -/
theorem bil_zero_right (x : Fin 3 → ℚ) : bil A x 0 = 0 := by simp [bil]

/-- Helper: $B_A(0, x) = 0$ (`hA`: `A` definite). -/
theorem bil_zero_left (hA : Def A) (x : Fin 3 → ℚ) : bil A 0 x = 0 := by
  rw [bil_comm hA, bil_zero_right]

/-- Helper: $B_A(x, x) \ne 0$ for a nonzero vector `x` (`hx`) and a definite matrix `A` (`hA`). -/
theorem Def.ne_zero_of_pos (hA : Def A) {x : Fin 3 → ℚ} (hx : x ≠ 0) : bil A x x ≠ 0 :=
  (hA.pos x hx).ne'

/-- Helper: a definite matrix `A` (`hA`) kills only the zero vector (`h`: $Ax = 0$). -/
theorem Def.mulVec_eq_zero (hA : Def A) {x : Fin 3 → ℚ} (h : A *ᵥ x = 0) : x = 0 := by
  by_contra hx
  have := hA.pos x hx
  simp [bil, h] at this

/-- Helper: a $3 \times 3$ rational matrix `M` with trivial kernel (`h`) has nonzero determinant. -/
theorem det_ne_of_forall {M : Matrix (Fin 3) (Fin 3) ℚ} (h : ∀ v, M *ᵥ v = 0 → v = 0) :
    M.det ≠ 0 := by
  intro hd
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  exact hv (h v hMv)

/-- Helper: a definite matrix `A` (`hA`) has nonzero determinant. -/
theorem Def.det_ne (hA : Def A) : A.det ≠ 0 := det_ne_of_forall fun _ h => hA.mulVec_eq_zero h

/-- Helper: $A(A^{-1}z) = z$ for a definite matrix `A` (`hA`) and any vector `z`. -/
theorem Def.mulVec_inv (hA : Def A) (z : Fin 3 → ℚ) : A *ᵥ (A⁻¹ *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hA.det_ne), Matrix.one_mulVec]

/-- Helper: a rotation preserves the form. -/
theorem IsRot.bil_eq {g : Matrix (Fin 3) (Fin 3) ℚ} (hg : IsRot A g) (x y : Fin 3 → ℚ) :
    bil A (g *ᵥ x) (g *ᵥ y) = bil A x y := by
  have := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℚ => x ⬝ᵥ (M *ᵥ y)) hg.orth
  simp only [bil] at this ⊢
  rw [← this, mulVec_dot, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- Helper: $M^{\mathsf T}\bigl((Mv) \times (Mw)\bigr) = \det(M)\,(v \times w)$ for a $3 \times 3$ matrix `M` and
vectors `v`, `w`. -/
theorem cross_mulVec (M : Matrix (Fin 3) (Fin 3) ℚ) (v w : Fin 3 → ℚ) :
    Mᵀ *ᵥ ((M *ᵥ v) ⨯₃ (M *ᵥ w)) = M.det • (v ⨯₃ w) := by
  ext i
  fin_cases i <;>
  simp [cross_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.det_fin_three] <;> ring

/-- Helper: a matrix `M` of nonzero determinant (`hM`) with $Md = 0$ (`h`) has $d = 0$. -/
theorem mulVec_cancel {M : Matrix (Fin 3) (Fin 3) ℚ} (hM : M.det ≠ 0) {d : Fin 3 → ℚ}
    (h : M *ᵥ d = 0) : d = 0 := by
  by_contra hd
  exact hM (Matrix.exists_mulVec_eq_zero_iff.1 ⟨d, hd, h⟩)

/-- Helper: **equivariance of the cross product.** For a rotation `g` of the definite matrix `A` (`hA`, `hg`),
$g\,A^{-1}(v \times w) = A^{-1}\bigl((gv) \times (gw)\bigr)$. -/
theorem IsRot.equivariant (hA : Def A) {g : Matrix (Fin 3) (Fin 3) ℚ} (hg : IsRot A g)
    (v w : Fin 3 → ℚ) :
    g *ᵥ (A⁻¹ *ᵥ (v ⨯₃ w)) = A⁻¹ *ᵥ ((g *ᵥ v) ⨯₃ (g *ᵥ w)) := by
  have hdet : (gᵀ * A).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_transpose, hg.det, one_mul]; exact hA.det_ne
  have e1 : (gᵀ * A) *ᵥ (g *ᵥ (A⁻¹ *ᵥ (v ⨯₃ w))) = v ⨯₃ w := by
    rw [Matrix.mulVec_mulVec, hg.orth, hA.mulVec_inv]
  have e2 : (gᵀ * A) *ᵥ (A⁻¹ *ᵥ ((g *ᵥ v) ⨯₃ (g *ᵥ w))) = v ⨯₃ w := by
    rw [← Matrix.mulVec_mulVec, hA.mulVec_inv, cross_mulVec, hg.det, one_smul]
  have key : (gᵀ * A) *ᵥ (g *ᵥ (A⁻¹ *ᵥ (v ⨯₃ w)) - A⁻¹ *ᵥ ((g *ᵥ v) ⨯₃ (g *ᵥ w))) = 0 := by
    rw [Matrix.mulVec_sub, e1, e2, sub_self]
  exact sub_eq_zero.1 (mulVec_cancel hdet key)

/-- Helper: the matrix with columns `a`, `b`, `c`. -/
def colMat (a b c : Fin 3 → ℚ) : Matrix (Fin 3) (Fin 3) ℚ := Matrix.of fun i j => ![a, b, c] j i

/-- Helper: the matrix with columns `a`, `b`, `c` sends `v` to $v_0 a + v_1 b + v_2 c$. -/
theorem colMat_mulVec (a b c v : Fin 3 → ℚ) :
    colMat a b c *ᵥ v = v 0 • a + v 1 • b + v 2 • c := by
  ext i; simp [colMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring

/-- Helper: $g \cdot [a\,b\,c] = [ga\,gb\,gc]$ for the column matrices. -/
theorem mul_colMat (g : Matrix (Fin 3) (Fin 3) ℚ) (a b c : Fin 3 → ℚ) :
    g * colMat a b c = colMat (g *ᵥ a) (g *ᵥ b) (g *ᵥ c) := by
  ext i j
  fin_cases j <;> simp [colMat, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- Helper: if $[a\,b\,c]$ is invertible (`hdet`) and `g` fixes its columns (`h`) then $g = 1$. -/
theorem eq_one_of_mul_colMat {g : Matrix (Fin 3) (Fin 3) ℚ} {a b c : Fin 3 → ℚ}
    (hdet : (colMat a b c).det ≠ 0) (h : g * colMat a b c = colMat a b c) : g = 1 := by
  have hu : IsUnit (colMat a b c) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  calc g = g * (colMat a b c * (colMat a b c)⁻¹) := by
        rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.mul_one]
    _ = (g * colMat a b c) * (colMat a b c)⁻¹ := by rw [Matrix.mul_assoc]
    _ = 1 := by rw [h, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet)]

/-- Helper: a rotation fixing two vectors with nonzero cross product is the identity. -/
theorem IsRot.eq_one_of_fixed_two (hA : Def A) {g : Matrix (Fin 3) (Fin 3) ℚ} (hg : IsRot A g)
    {e e' : Fin 3 → ℚ} (he : g *ᵥ e = e) (he' : g *ᵥ e' = e') (hc : e ⨯₃ e' ≠ 0) : g = 1 := by
  set n : Fin 3 → ℚ := A⁻¹ *ᵥ (e ⨯₃ e') with hn
  have hgn : g *ᵥ n = n := by rw [hn, hg.equivariant hA, he, he']
  have hAn : A *ᵥ n = e ⨯₃ e' := hA.mulVec_inv _
  have hn0 : n ≠ 0 := by
    intro h; rw [h, Matrix.mulVec_zero] at hAn; exact hc hAn.symm
  have h1 : bil A n e = 0 := by
    rw [bil_comm hA]; simp [bil, hAn]
  have h2 : bil A n e' = 0 := by
    rw [bil_comm hA]; simp [bil, hAn]
  have hdet : (colMat e e' n).det ≠ 0 := by
    apply det_ne_of_forall
    intro v hv
    rw [colMat_mulVec] at hv
    have h3 := congrArg (bil A n) hv
    rw [bil_add_right, bil_add_right, bil_smul_right, bil_smul_right, bil_smul_right, h1, h2,
      bil_zero_right] at h3
    have hv2 : v 2 = 0 := by
      have : v 2 * bil A n n = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right (hA.ne_zero_of_pos hn0)
    rw [hv2, zero_smul, add_zero] at hv
    have h4 := congrArg (fun u => u ⨯₃ e') hv
    have h5 := congrArg (fun u => e ⨯₃ u) hv
    simp at h4 h5
    have hv0 : v 0 = 0 := by
      rcases h4 with h | h
      · exact h
      · exact absurd h hc
    have hv1 : v 1 = 0 := by
      rcases h5 with h | h
      · exact h
      · exact absurd h hc
    ext i; fin_cases i <;> simp [hv0, hv1, hv2]
  refine eq_one_of_mul_colMat hdet ?_
  rw [mul_colMat, he, he', hgn]

/-- Helper: a rotation has $\det(g - 1) = 0$ (it fixes a nonzero vector). -/
theorem IsRot.det_sub_one (hA : Def A) {g : Matrix (Fin 3) (Fin 3) ℚ} (hg : IsRot A g) :
    (g - 1).det = 0 := by
  have hAu : IsUnit A := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hA.det_ne)
  set K : Matrix (Fin 3) (Fin 3) ℚ := A⁻¹ * gᵀ * A with hK
  have hKg : K * g = 1 := by
    have : K * g = A⁻¹ * (gᵀ * A * g) := by rw [hK]; simp only [Matrix.mul_assoc]
    rw [this, hg.orth, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hA.det_ne)]
  have hgK : g * K = 1 := mul_eq_one_comm.1 hKg
  have h1 : g - 1 = g * (1 - K) := by rw [Matrix.mul_sub, hgK, Matrix.mul_one]
  have h2 : 1 - K = A⁻¹ * (1 - gᵀ) * A := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hA.det_ne), hK]
  have h3 : (1 - K).det = (1 - gᵀ).det := by
    rw [h2, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    field_simp [hA.det_ne]
  have h4 : (1 - gᵀ).det = -(g - 1).det := by
    have e1 : (1 - gᵀ) = (1 - g)ᵀ := by simp [Matrix.transpose_sub]
    have : (1 - g) = -(g - 1) := by abel
    rw [e1, Matrix.det_transpose, this, Matrix.det_neg]; simp only [Fintype.card_fin]; ring
  have h5 : (g - 1).det = -(g - 1).det := by
    calc (g - 1).det = (g * (1 - K)).det := by rw [← h1]
      _ = (1 - K).det := by rw [Matrix.det_mul, hg.det, one_mul]
      _ = _ := by rw [h3, h4]
  linarith

/-- Helper: orthogonal expansion in a $B_A$-orthogonal triple of nonzero vectors. -/
theorem orth_expand (hA : Def A) {v0 v1 v2 : Fin 3 → ℚ}
    (h01 : bil A v0 v1 = 0) (h02 : bil A v0 v2 = 0) (h12 : bil A v1 v2 = 0)
    (n0 : v0 ≠ 0) (n1 : v1 ≠ 0) (n2 : v2 ≠ 0) (y : Fin 3 → ℚ) :
    y = (bil A v0 y / bil A v0 v0) • v0 + (bil A v1 y / bil A v1 v1) • v1 +
      (bil A v2 y / bil A v2 v2) • v2 := by
  have h10 : bil A v1 v0 = 0 := by rw [bil_comm hA]; exact h01
  have h20 : bil A v2 v0 = 0 := by rw [bil_comm hA]; exact h02
  have h21 : bil A v2 v1 = 0 := by rw [bil_comm hA]; exact h12
  have hdet : (colMat v0 v1 v2).det ≠ 0 := by
    apply det_ne_of_forall
    intro w hw
    rw [colMat_mulVec] at hw
    have p0 := congrArg (bil A v0) hw
    have p1 := congrArg (bil A v1) hw
    have p2 := congrArg (bil A v2) hw
    simp only [bil_add_right, bil_smul_right, h01, h02, h10, h12, h20, h21, bil_zero_right] at p0 p1 p2
    have w0 : w 0 = 0 := by
      have : w 0 * bil A v0 v0 = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right (hA.ne_zero_of_pos n0)
    have w1 : w 1 = 0 := by
      have : w 1 * bil A v1 v1 = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right (hA.ne_zero_of_pos n1)
    have w2 : w 2 = 0 := by
      have : w 2 * bil A v2 v2 = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right (hA.ne_zero_of_pos n2)
    ext i; fin_cases i <;> simp [w0, w1, w2]
  have hsurj : colMat v0 v1 v2 *ᵥ ((colMat v0 v1 v2)⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]
  obtain ⟨c, hc⟩ : ∃ c : Fin 3 → ℚ, y = c 0 • v0 + c 1 • v1 + c 2 • v2 :=
    ⟨_, by rw [← colMat_mulVec, hsurj]⟩
  have b0 : bil A v0 y = c 0 * bil A v0 v0 := by
    rw [hc]; simp [bil_add_right, bil_smul_right, h01, h02]
  have b1 : bil A v1 y = c 1 * bil A v1 v1 := by
    rw [hc]; simp [bil_add_right, bil_smul_right, h10, h12]
  have b2 : bil A v2 y = c 2 * bil A v2 v2 := by
    rw [hc]; simp [bil_add_right, bil_smul_right, h20, h21]
  rw [b0, b1, b2, mul_div_cancel_right₀ _ (hA.ne_zero_of_pos n0),
    mul_div_cancel_right₀ _ (hA.ne_zero_of_pos n1), mul_div_cancel_right₀ _ (hA.ne_zero_of_pos n2)]
  exact hc

/-- Helper: orthogonal nonzero vectors have nonzero cross product. -/
theorem cross_ne_zero_of_orth (hA : Def A) {e x : Fin 3 → ℚ} (he : e ≠ 0) (hx : x ≠ 0)
    (h : bil A e x = 0) : e ⨯₃ x ≠ 0 := by
  intro hc
  have hnli : ¬ LinearIndependent ℚ ![e, x] := by
    rw [← crossProduct_ne_zero_iff_linearIndependent]; exact not_not.2 hc
  rw [LinearIndependent.pair_iff] at hnli
  push Not at hnli
  obtain ⟨s, t, hst, hne⟩ := hnli
  have p := congrArg (bil A e) hst
  rw [bil_add_right, bil_smul_right, bil_smul_right, h, bil_zero_right] at p
  have hs : s = 0 := by
    have : s * bil A e e = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right (hA.ne_zero_of_pos he)
  rw [hs, zero_smul, zero_add] at hst
  have ht : t = 0 := (smul_eq_zero.1 hst).resolve_right hx
  exact hne hs ht

/-- Helper: a rotation `g` (`hg`) of a definite matrix `A` (`hA`) fixes a nonzero rational vector. -/
theorem IsRot.exists_fixed (hA : Def A) {g : Matrix (Fin 3) (Fin 3) ℚ} (hg : IsRot A g) :
    ∃ v : Fin 3 → ℚ, v ≠ 0 ∧ g *ᵥ v = v := by
  obtain ⟨v, hv, h⟩ := Matrix.exists_mulVec_eq_zero_iff.2 (hg.det_sub_one hA)
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h
  exact sub_eq_zero.1 h

/-- Helper: **the rotations fixing a vector `e` form a cyclic group.** A finite group `H` of rotations
of a definite form, all fixing the nonzero vector `e`, is cyclic (it embeds in the circle group
$\{z \in \mathbb C : |z| = 1\}$ through its action on the plane orthogonal to `e`). -/
theorem stab_cyclic (hA : Def A) {H : Type*} [Group H] [Finite H]
    (ρ : H →* Matrix (Fin 3) (Fin 3) ℚ) (hρ : Function.Injective ρ)
    (hrot : ∀ h, IsRot A (ρ h)) {e : Fin 3 → ℚ} (he : e ≠ 0) (hfix : ∀ h, ρ h *ᵥ e = e) :
    IsCyclic H := by
  obtain ⟨E, hEdef⟩ : ∃ E : (Fin 3 → ℚ) → (Fin 3 → ℚ), ∀ y, E y = A⁻¹ *ᵥ (e ⨯₃ y) := ⟨_, fun _ => rfl⟩
  have hAE : ∀ y, A *ᵥ E y = e ⨯₃ y := fun y => by rw [hEdef]; exact hA.mulVec_inv _
  have hEadd : ∀ y z, E (y + z) = E y + E z := by
    intro y z; simp [hEdef, map_add, Matrix.mulVec_add]
  have hEsmul : ∀ (c : ℚ) y, E (c • y) = c • E y := by
    intro c y; simp [hEdef, map_smul, Matrix.mulVec_smul]
  have hEcomm : ∀ h y, ρ h *ᵥ E y = E (ρ h *ᵥ y) := by
    intro h y
    rw [hEdef, hEdef, (hrot h).equivariant hA, hfix h]
  have hBE : ∀ z y, bil A z (E y) = z ⬝ᵥ (e ⨯₃ y) := by
    intro z y; simp [bil, hAE]
  -- a vector orthogonal to e
  obtain ⟨u, hu⟩ : ∃ u : Fin 3 → ℚ, e ⨯₃ u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply he
    have h0 := hcon (Pi.single 0 1)
    have h1 := hcon (Pi.single 1 1)
    have h00 := congrFun h0 1
    have h01 := congrFun h0 2
    have h12 := congrFun h1 2
    simp [cross_apply] at h00 h01 h12
    ext i; fin_cases i <;> simp [h00, h01, h12]
  obtain ⟨x, hxdef⟩ : ∃ x, x = E u := ⟨_, rfl⟩
  have hAx : A *ᵥ x = e ⨯₃ u := by rw [hxdef, hAE]
  have hx0 : x ≠ 0 := by
    intro h; rw [h, Matrix.mulVec_zero] at hAx; exact hu hAx.symm
  have hex : bil A e x = 0 := by rw [hxdef, hBE]; simp
  obtain ⟨y1, hy1def⟩ : ∃ y1, y1 = E x := ⟨_, rfl⟩
  have hAy1 : A *ᵥ y1 = e ⨯₃ x := by rw [hy1def, hAE]
  have hexne : e ⨯₃ x ≠ 0 := cross_ne_zero_of_orth hA he hx0 hex
  have hy10 : y1 ≠ 0 := by
    intro h; rw [h, Matrix.mulVec_zero] at hAy1; exact hexne hAy1.symm
  have hey1 : bil A e y1 = 0 := by rw [hy1def, hBE]; simp
  have hxy1 : bil A x y1 = 0 := by rw [hy1def, hBE]; simp
  have hxy1' : bil A y1 x = 0 := by rw [bil_comm hA]; exact hxy1
  have hxe : bil A x e = 0 := by rw [bil_comm hA]; exact hex
  have hy1e : bil A y1 e = 0 := by rw [bil_comm hA]; exact hey1
  have hexp : ∀ y, y = (bil A e y / bil A e e) • e + (bil A x y / bil A x x) • x +
      (bil A y1 y / bil A y1 y1) • y1 := fun y => orth_expand hA hex hey1 hxy1 he hx0 hy10 y
  have hpx := hA.pos x hx0
  have hpy := hA.pos y1 hy10
  -- E (E x) = - lam x
  obtain ⟨lam, hlam⟩ : ∃ lam : ℚ, lam = bil A y1 y1 / bil A x x := ⟨_, rfl⟩
  have hlampos : 0 < lam := by rw [hlam]; exact div_pos hpy hpx
  have hEE : E y1 = (-lam) • x := by
    have h1 := hexp (E y1)
    have c0 : bil A e (E y1) = 0 := by rw [hBE]; simp
    have c2 : bil A y1 (E y1) = 0 := by rw [hBE]; simp
    have c1 : bil A x (E y1) = - bil A y1 y1 := by
      rw [hBE]
      have : x ⬝ᵥ e ⨯₃ y1 = -(y1 ⬝ᵥ e ⨯₃ x) := by
        simp [cross_apply, dotProduct, Fin.sum_univ_three]; ring
      rw [this, ← hAy1]
      rfl
    rw [c0, c1, c2] at h1
    rw [h1, hlam]
    simp
    ext i
    simp
    ring
  -- coordinates
  have huniq : ∀ a b a' b' : ℚ, a • x + b • y1 = a' • x + b' • y1 → a = a' ∧ b = b' := by
    intro a b a' b' h
    have p := congrArg (bil A x) h
    have q := congrArg (bil A y1) h
    simp only [bil_add_right, bil_smul_right, hxy1, hxy1', mul_zero, add_zero, zero_add] at p q
    exact ⟨mul_right_cancel₀ (hA.ne_zero_of_pos hx0) p, mul_right_cancel₀ (hA.ne_zero_of_pos hy10) q⟩
  obtain ⟨a, ha⟩ : ∃ a : H → ℚ, ∀ h, a h = bil A x (ρ h *ᵥ x) / bil A x x := ⟨_, fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : H → ℚ, ∀ h, b h = bil A y1 (ρ h *ᵥ x) / bil A y1 y1 := ⟨_, fun _ => rfl⟩
  have hgx : ∀ h, ρ h *ᵥ x = a h • x + b h • y1 := by
    intro h
    have h1 := hexp (ρ h *ᵥ x)
    have c0 : bil A e (ρ h *ᵥ x) = 0 := by
      have := (hrot h).bil_eq e x
      rw [hfix h] at this; rw [this]; exact hex
    rw [c0, ← ha, ← hb] at h1
    simpa using h1
  have hgy : ∀ h, ρ h *ᵥ y1 = a h • y1 - (b h * lam) • x := by
    intro h
    rw [hy1def, hEcomm, hgx, hEadd, hEsmul, hEsmul, ← hy1def, hEE]
    ext i; simp; ring
  have hmul : ∀ h k, a (h * k) = a h * a k - lam * (b h * b k) ∧
      b (h * k) = a h * b k + a k * b h := by
    intro h k
    apply huniq
    rw [← hgx, map_mul, ← Matrix.mulVec_mulVec, hgx k, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, hgx h, hgy h]
    ext i; simp; ring
  have hone : a 1 = 1 ∧ b 1 = 0 := by
    apply huniq
    rw [← hgx, map_one, Matrix.one_mulVec]; simp
  obtain ⟨μ, hμdef⟩ : ∃ μ : ℝ, μ = Real.sqrt (lam : ℝ) := ⟨_, rfl⟩
  have hμsq : μ ^ 2 = (lam : ℝ) := by
    rw [hμdef]; exact Real.sq_sqrt (by exact_mod_cast hlampos.le)
  have hμpos : 0 < μ := by
    rw [hμdef]; exact Real.sqrt_pos.2 (by exact_mod_cast hlampos)
  have hμC : ((μ : ℂ)) ^ 2 = (lam : ℂ) := by
    have := congrArg (fun r : ℝ => (r : ℂ)) hμsq
    simpa using this
  let ψ : H →* ℂ :=
    { toFun := fun h => (a h : ℂ) + (b h : ℂ) * (Complex.I * μ)
      map_one' := by simp [hone.1, hone.2]
      map_mul' := by
        intro h k
        obtain ⟨m1, m2⟩ := hmul h k
        rw [m1, m2]
        push_cast
        linear_combination (-((b h : ℂ) * b k) * Complex.I ^ 2) * hμC +
          (-((b h : ℂ) * b k * lam)) * Complex.I_sq }
  refine isCyclic_of_injective_ringHom ψ ?_
  intro h k hhk
  have hre := congrArg Complex.re hhk
  have him := congrArg Complex.im hhk
  simp [ψ] at hre him
  have hab : a h = a k := by exact_mod_cast hre
  have hbb : b h = b k := by
    rcases him with h' | h'
    · exact h'
    · exact absurd h' hμpos.ne'
  apply hρ
  have hall : ∀ y, ρ h *ᵥ y = ρ k *ᵥ y := by
    intro y
    rw [hexp y]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hfix h, hfix k, hgx h, hgx k, hgy h, hgy k, hab, hbb]
  ext i j
  have := congrFun (hall (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

end

section Counting

open MulAction

/-- Helper: the Diophantine analysis of the class equation. -/
theorem diophantine (N k : ℕ) (n : Fin k → ℕ) (hN : 0 < N)
    (hn : ∀ i, n i = 2 ∨ n i = 3 ∨ n i = 4 ∨ n i = 6) (hd : ∀ i, n i ∣ N)
    (hs : ∑ i, N / n i + 2 * N = k * N + 2) :
    N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 ∨ N = 6 ∨ N = 8 ∨ N = 12 ∨ N = 24 := by
  have hle : ∑ i, N / n i ≤ k * (N / 2) := by
    calc ∑ i, N / n i ≤ ∑ _i : Fin k, N / 2 := by
          apply Finset.sum_le_sum
          intro i _
          apply Nat.div_le_div_left _ (by norm_num)
          rcases hn i with h | h | h | h <;> omega
      _ = k * (N / 2) := by simp
  have hk : k ≤ 3 := by
    by_contra hk
    push Not at hk
    have h1 : 2 * (N / 2) ≤ N := Nat.mul_div_le N 2
    have h2 : k * (2 * (N / 2)) ≤ k * N := Nat.mul_le_mul_left k h1
    have h3 : 4 * N ≤ k * N := Nat.mul_le_mul_right N hk
    nlinarith
  interval_cases k
  · simp at hs; omega
  · simp at hs
    have := hd 0
    rcases hn 0 with h | h | h | h <;> rw [h] at hs this <;> omega
  · simp [Fin.sum_univ_succ] at hs
    have d0 := hd 0
    have d1 := hd 1
    rcases hn 0 with h | h | h | h <;> rcases hn 1 with h' | h' | h' | h' <;>
      rw [h] at hs d0 <;> rw [h'] at hs d1 <;> omega
  · simp [Fin.sum_univ_succ] at hs
    have d0 := hd 0
    have d1 := hd 1
    have d2 := hd 2
    rcases hn 0 with h | h | h | h <;> rcases hn 1 with h' | h' | h' | h' <;>
      rcases hn 2 with h'' | h'' | h'' | h'' <;>
      rw [h] at hs d0 <;> rw [h'] at hs d1 <;> rw [h''] at hs d2 <;> omega

/-- Helper: **the class equation for a finite group `G` acting on a finite set `X`** such that every nonidentity
element fixes exactly two points (`hfix`) and every point has a stabiliser of order $2, 3, 4$ or $6$ (`hstab`):
then $|G| \in \{1, 2, 3, 4, 6, 8, 12, 24\}$. (Burnside's lemma and the orbit-stabiliser formula give
$\sum_{\text{orbits}} |G|/n_\omega + 2|G| = (\#\text{orbits})|G| + 2$, solved by `diophantine`.) -/
theorem count_classify {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    (hfix : ∀ g : G, g ≠ 1 → Nat.card (fixedBy X g) = 2)
    (hstab : ∀ x : X, Nat.card (stabilizer G x) = 2 ∨ Nat.card (stabilizer G x) = 3 ∨
      Nat.card (stabilizer G x) = 4 ∨ Nat.card (stabilizer G x) = 6) :
    Nat.card G = 1 ∨ Nat.card G = 2 ∨ Nat.card G = 3 ∨ Nat.card G = 4 ∨ Nat.card G = 6 ∨
      Nat.card G = 8 ∨ Nat.card G = 12 ∨ Nat.card G = 24 := by
  classical
  have := Fintype.ofFinite G
  have := Fintype.ofFinite X
  have : Fintype (MulAction.orbitRel.Quotient G X) := Fintype.ofFinite _
  have burn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X
  have orb := MulAction.card_eq_sum_card_group_div_card_stabilizer G X
  have hfix' : ∀ g : G, g ≠ 1 → Fintype.card (fixedBy X g) = 2 := by
    intro g hg; rw [← Nat.card_eq_fintype_card]; exact hfix g hg
  have hN : 0 < Fintype.card G := Fintype.card_pos
  have hsplit : ∑ g : G, Fintype.card (fixedBy X g) = Fintype.card X + 2 * (Fintype.card G - 1) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G))]
    have h1 : Fintype.card (fixedBy X (1 : G)) = Fintype.card X := by
      apply Fintype.card_congr
      exact Equiv.subtypeUnivEquiv (fun x => by simp)
    rw [h1, Finset.sum_congr rfl (fun g hg => hfix' g (Finset.ne_of_mem_erase hg)), Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    simp [mul_comm]
  set Ω := MulAction.orbitRel.Quotient G X
  let e : Ω ≃ Fin (Fintype.card Ω) := Fintype.equivFin Ω
  have hs : ∑ i : Fin (Fintype.card Ω),
      Fintype.card G / Fintype.card (stabilizer G (e.symm i).out) + 2 * Fintype.card G =
      Fintype.card Ω * Fintype.card G + 2 := by
    have hse : ∑ i : Fin (Fintype.card Ω),
        Fintype.card G / Fintype.card (stabilizer G (e.symm i).out) =
        ∑ ω : Ω, Fintype.card G / Fintype.card (stabilizer G ω.out) :=
      Fintype.sum_equiv e.symm _ _ (fun i => rfl)
    have burn' : ∑ g : G, Fintype.card (fixedBy X g) = Fintype.card Ω * Fintype.card G := by
      convert burn
    have orb' : Fintype.card X = ∑ ω : Ω, Fintype.card G / Fintype.card (stabilizer G ω.out) := by
      convert orb
    rw [hse, ← orb']
    rw [hsplit] at burn'
    omega
  have hn : ∀ i : Fin (Fintype.card Ω), Fintype.card (stabilizer G (e.symm i).out) = 2 ∨
      Fintype.card (stabilizer G (e.symm i).out) = 3 ∨ Fintype.card (stabilizer G (e.symm i).out) = 4 ∨
      Fintype.card (stabilizer G (e.symm i).out) = 6 := by
    intro i
    have := hstab (e.symm i).out
    simpa [Nat.card_eq_fintype_card] using this
  have hd : ∀ i : Fin (Fintype.card Ω), Fintype.card (stabilizer G (e.symm i).out) ∣ Fintype.card G :=
    fun i => by
      have := Subgroup.card_subgroup_dvd_card (stabilizer G (e.symm i).out)
      simpa [Nat.card_eq_fintype_card] using this
  have := diophantine (Fintype.card G) (Fintype.card Ω)
    (fun i => Fintype.card (stabilizer G (e.symm i).out)) hN hn hd hs
  simpa [Nat.card_eq_fintype_card] using this

end Counting

section Concrete

open QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.Cassels.Ch9Ex6

/-- Helper: $(g x) \cdot w = x \cdot (g^{\mathsf T} w)$ over any commutative semiring `R`. -/
theorem mulVec_dot_gen {R : Type*} [CommSemiring R] (g : Matrix (Fin 3) (Fin 3) R) (x w : Fin 3 → R) :
    (g *ᵥ x) ⬝ᵥ w = x ⬝ᵥ (gᵀ *ᵥ w) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]

variable {f : QuadForm ℚ 3}

/-- Helper: the Gram matrix of a positive definite rational form is definite. -/
theorem def_gram (hf : Siegel.RatPosDef f) : Def (RatQF.gram f) :=
  ⟨gram_symm f, fun x hx => by
    unfold bil
    rw [← eval_eq_gram]
    exact hf x hx⟩

/-- Helper: an element of `RatAutPlus f` is a rotation for the Gram matrix of `f`. -/
theorem rot_of_mem (g : RatAutPlus f) : IsRot (RatQF.gram f) (Ch9Ex6.toQ g.1.val) := by
  obtain ⟨hd, haut⟩ := g.2
  refine ⟨(eval_comp_eq_iff f f (Ch9Ex6.toQ g.1.val)).1 haut, ?_⟩
  have := RingHom.map_det (Int.castRingHom ℚ) g.1.val
  simp only [hd] at this
  simpa [Ch9Ex6.toQ] using this.symm

/-- Helper: the rational representation $\mathrm{GL}_3(\mathbb Z) \to M_3(\mathbb Q)$. -/
def ratRep : GL (Fin 3) ℤ →* Matrix (Fin 3) (Fin 3) ℚ :=
  ((Int.castRingHom ℚ).mapMatrix : Matrix (Fin 3) (Fin 3) ℤ →+* Matrix (Fin 3) (Fin 3) ℚ).toMonoidHom.comp
    (Units.coeHom _)

/-- Helper: `ratRep g` is the entrywise cast `toQ` of the integer matrix of `g`. -/
theorem ratRep_apply (g : GL (Fin 3) ℤ) : ratRep g = Ch9Ex6.toQ g.val := rfl

/-- Helper: `ratRep` is injective. -/
theorem ratRep_injective : Function.Injective ratRep := by
  intro g h hgh
  apply Units.ext
  ext i j
  have := congrFun (congrFun hgh i) j
  simpa [ratRep_apply, Ch9Ex6.toQ] using this

/-- Helper: the group of proper integral automorphs of a positive definite rational ternary form is finite. -/
theorem finite_ratAutPlus (hf : Siegel.RatPosDef f) : Finite (RatAutPlus f) := by
  obtain ⟨N, hN, Q, hQ⟩ := Siegel.exists_intForm_smul f
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hQpos : IntQF.PosDef Q := by
    intro x hx
    have hx' : (fun i => (x i : ℚ)) ≠ 0 := by
      intro h
      apply hx
      funext i
      have := congrFun h i
      simpa using this
    have h1 := hQ (fun i => (x i : ℚ))
    rw [Siegel.evalIn_intCast] at h1
    have : (0 : ℚ) < (Q.eval x : ℚ) := by rw [h1]; exact mul_pos hNq (hf _ hx')
    exact_mod_cast this
  have hle : RatAutPlus f ≤ Siegel.Aut Q := by
    intro g hg
    obtain ⟨-, haut⟩ := hg
    show ∀ x : Fin 3 → ℤ, Q.eval (g.val *ᵥ x) = Q.eval x
    intro x
    have e : (fun i => ((g.val *ᵥ x) i : ℚ)) = (Ch9Ex6.toQ g.val) *ᵥ (fun i => (x i : ℚ)) := by
      funext i
      simp [Ch9Ex6.toQ, Matrix.mulVec, dotProduct]
    have h1 := hQ (fun i => ((g.val *ᵥ x) i : ℚ))
    have h2 := hQ (fun i => (x i : ℚ))
    rw [Siegel.evalIn_intCast] at h1 h2
    rw [e, haut, ← h2] at h1
    exact_mod_cast h1
  have := hQpos.finite_aut
  exact Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

/-- Helper: the order of a proper integral automorph is $1, 2, 3, 4$ or $6$ (Example 15 (i)). -/
theorem orderOf_mem_one_two_three_four_six (hf : Siegel.RatPosDef f) (g : RatAutPlus f) :
    orderOf g ∈ ({1, 2, 3, 4, 6} : Finset ℕ) := by
  have h := Siegel.orderOf_mem_of_proper_automorph hf g.2.1 g.2.2
  rwa [orderOf_units, Subgroup.orderOf_coe] at h

/-! ### Poles: primitive integer vectors fixed by a nonidentity automorph -/

/-- Helper: a vector $e \in \mathbb Z^3$ is *primitive* if some integer vector `y` has $y \cdot e = 1$
(equivalently the coordinates of `e` have greatest common divisor $1$). -/
def Prim (e : Fin 3 → ℤ) : Prop := ∃ y : Fin 3 → ℤ, y ⬝ᵥ e = 1

/-- Helper: a primitive vector is nonzero. -/
theorem Prim.ne_zero {e : Fin 3 → ℤ} (h : Prim e) : e ≠ 0 := by
  obtain ⟨y, hy⟩ := h
  rintro rfl
  simp at hy

/-- Helper: the negative of a primitive vector is primitive. -/
theorem Prim.neg {e : Fin 3 → ℤ} (h : Prim e) : Prim (-e) := by
  obtain ⟨y, hy⟩ := h
  exact ⟨-y, by simpa using hy⟩

/-- Helper: an element `g` of $\mathrm{GL}_3(\mathbb Z)$ maps primitive vectors to primitive vectors. -/
theorem Prim.mulVec {e : Fin 3 → ℤ} (h : Prim e) (g : GL (Fin 3) ℤ) : Prim (g.val *ᵥ e) := by
  obtain ⟨y, hy⟩ := h
  refine ⟨((g⁻¹ : GL (Fin 3) ℤ).val)ᵀ *ᵥ y, ?_⟩
  rw [mulVec_dot_gen, Matrix.transpose_transpose, Matrix.mulVec_mulVec, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  exact hy

/-- Helper: coordinates with greatest common divisor $1$ give a primitive vector (Bezout). -/
theorem prim_of_gcd (e : Fin 3 → ℤ) (h : Int.gcd (Int.gcd (e 0) (e 1)) (e 2) = 1) : Prim e := by
  have h1 := Int.gcd_eq_gcd_ab (e 0) (e 1)
  have h2 := Int.gcd_eq_gcd_ab ((Int.gcd (e 0) (e 1) : ℕ) : ℤ) (e 2)
  rw [h] at h2
  refine ⟨![Int.gcdA (e 0) (e 1) * Int.gcdA (Int.gcd (e 0) (e 1) : ℤ) (e 2),
    Int.gcdB (e 0) (e 1) * Int.gcdA (Int.gcd (e 0) (e 1) : ℤ) (e 2),
    Int.gcdB (Int.gcd (e 0) (e 1) : ℤ) (e 2)], ?_⟩
  simp only [dotProduct, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  push_cast at h2
  linear_combination (-(Int.gcdA (Int.gcd (e 0) (e 1) : ℤ) (e 2))) * h1 - h2

/-- Helper: if $e \cdot y = 1$ and $e \times e' = 0$ then $e' = (y \cdot e')\,e$. -/
theorem eq_smul_of_cross_zero {e e' y : Fin 3 → ℤ} (hy : y ⬝ᵥ e = 1) (h : e ⨯₃ e' = 0) :
    e' = (y ⬝ᵥ e') • e := by
  have c1 : e 1 * e' 2 = e 2 * e' 1 := by
    have := congrFun h 0; simp [cross_apply] at this; linarith
  have c2 : e 2 * e' 0 = e 0 * e' 2 := by
    have := congrFun h 1; simp [cross_apply] at this; linarith
  have c3 : e 0 * e' 1 = e 1 * e' 0 := by
    have := congrFun h 2; simp [cross_apply] at this; linarith
  simp only [dotProduct, Fin.sum_univ_three] at hy ⊢
  funext k
  fin_cases k
  · simp
    linear_combination (-(e' 0)) * hy - (y 1) * c3 + (y 2) * c2
  · simp
    linear_combination (-(e' 1)) * hy + (y 0) * c3 - (y 2) * c1
  · simp
    linear_combination (-(e' 2)) * hy - (y 0) * c2 + (y 1) * c1

/-- Helper: primitive vectors with zero cross product are equal up to sign. -/
theorem prim_eq_or_neg {e e' : Fin 3 → ℤ} (he : Prim e) (he' : Prim e') (h : e ⨯₃ e' = 0) :
    e' = e ∨ e' = -e := by
  obtain ⟨y, hy⟩ := he
  obtain ⟨y', hy'⟩ := he'
  have h' : e' ⨯₃ e = 0 := by
    rw [← cross_anticomm, h, neg_zero]
  have h1 := eq_smul_of_cross_zero hy h
  have h2 := eq_smul_of_cross_zero hy' h'
  have key : e = ((y' ⬝ᵥ e) * (y ⬝ᵥ e')) • e := by
    rw [mul_smul, ← h1, ← h2]
  have hne : e ≠ 0 := Prim.ne_zero ⟨y, hy⟩
  have hc : (y' ⬝ᵥ e) * (y ⬝ᵥ e') = 1 := by
    have : (1 - (y' ⬝ᵥ e) * (y ⬝ᵥ e')) • e = 0 := by
      rw [sub_smul, one_smul]; exact sub_eq_zero.2 key
    rcases smul_eq_zero.1 this with h0 | h0
    · linarith
    · exact absurd h0 hne
  have hc' : (y ⬝ᵥ e') * (y' ⬝ᵥ e) = 1 := by rw [mul_comm]; exact hc
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hc' with h3 | h3
  · left; rw [h1, h3, one_smul]
  · right; rw [h1, h3, neg_smul, one_smul]

/-- Helper: the integer vector with entries cast to $\mathbb Q$. -/
def castVec (e : Fin 3 → ℤ) : Fin 3 → ℚ := fun i => (e i : ℚ)

/-- Helper: casting commutes with the action of an integer matrix `M` on an integer vector `e`. -/
theorem toQ_mulVec_castVec (M : Matrix (Fin 3) (Fin 3) ℤ) (e : Fin 3 → ℤ) :
    Ch9Ex6.toQ M *ᵥ castVec e = castVec (M *ᵥ e) := by
  funext i; simp [Ch9Ex6.toQ, castVec, Matrix.mulVec, dotProduct]

/-- Helper: casting commutes with the cross product. -/
theorem castVec_cross (e e' : Fin 3 → ℤ) : castVec e ⨯₃ castVec e' = castVec (e ⨯₃ e') := by
  funext i; fin_cases i <;> simp [castVec, cross_apply]

/-- Helper: the cast of a nonzero integer vector is nonzero. -/
theorem castVec_ne_zero {e : Fin 3 → ℤ} (h : e ≠ 0) : castVec e ≠ 0 := by
  intro h0; apply h; funext i
  have := congrFun h0 i
  simpa [castVec] using this

/-- Helper: a nonidentity proper automorph fixes a primitive integer vector. -/
theorem exists_fixed_prim (hf : Siegel.RatPosDef f) (g : RatAutPlus f) :
    ∃ e : Fin 3 → ℤ, Prim e ∧ g.1.val *ᵥ e = e := by
  have hrot := rot_of_mem g
  have hdet : (g.1.val - 1).det = 0 := by
    have h1 := hrot.det_sub_one (def_gram hf)
    have h2 := RingHom.map_det (Int.castRingHom ℚ) (g.1.val - 1)
    have h3 : (Int.castRingHom ℚ).mapMatrix (g.1.val - 1) = Ch9Ex6.toQ g.1.val - 1 := by
      rw [map_sub, map_one]; rfl
    rw [h3, h1] at h2
    have h4 : (((g.1.val - 1).det : ℤ) : ℚ) = 0 := h2
    exact_mod_cast h4
  obtain ⟨e, he, hprim⟩ := Ch9Ex6.exists_primitive_fixed g.1.val hdet
  exact ⟨e, prim_of_gcd e hprim, he⟩

/-- Helper: a nonidentity proper automorph fixes exactly two primitive vectors, `e` and `-e`. -/
theorem prim_fixed_unique (hf : Siegel.RatPosDef f) (g : RatAutPlus f) (hg : g ≠ 1)
    {e e' : Fin 3 → ℤ} (he : Prim e) (he' : Prim e') (hfe : g.1.val *ᵥ e = e)
    (hfe' : g.1.val *ᵥ e' = e') : e' = e ∨ e' = -e := by
  apply prim_eq_or_neg he he'
  by_contra hne
  have hq : castVec e ⨯₃ castVec e' ≠ 0 := by
    rw [castVec_cross]; exact castVec_ne_zero hne
  have h1 := (rot_of_mem g).eq_one_of_fixed_two (def_gram hf)
    (by rw [toQ_mulVec_castVec, hfe]) (by rw [toQ_mulVec_castVec, hfe']) hq
  have hg1 : g.1.val = 1 := by
    ext i j
    have := congrFun (congrFun h1 i) j
    simp only [Ch9Ex6.toQ, Matrix.map_apply, Matrix.one_apply] at this
    simp only [Matrix.one_apply]
    split_ifs at this ⊢ <;> simpa using this
  exact hg (Subtype.ext (Units.ext hg1))

/-- Helper: a *pole* is a primitive integer vector fixed by some proper integral automorph $\ne 1$ of `f`. -/
def Pole (f : QuadForm ℚ 3) (e : Fin 3 → ℤ) : Prop :=
  Prim e ∧ ∃ g : RatAutPlus f, g ≠ 1 ∧ g.1.val *ᵥ e = e

/-- Helper: the type of poles. -/
abbrev PoleSet (f : QuadForm ℚ 3) : Type := {e : Fin 3 → ℤ // Pole f e}

/-- Helper: the group `RatAutPlus f` maps poles to poles (a conjugate of the fixing element fixes the image). -/
theorem Pole.smul {e : Fin 3 → ℤ} (h : Pole f e) (g : RatAutPlus f) : Pole f (g.1.val *ᵥ e) := by
  obtain ⟨hp, k, hk1, hk⟩ := h
  refine ⟨hp.mulVec g.1, g * k * g⁻¹, ?_, ?_⟩
  · intro h1
    apply hk1
    have := congrArg (fun z => g⁻¹ * z * g) h1
    simpa [mul_assoc] using this
  · have hinv : ((g.1⁻¹ : GL (Fin 3) ℤ).val) *ᵥ (g.1.val *ᵥ e) = e := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    show (g.1 * k.1 * g.1⁻¹).val *ᵥ (g.1.val *ᵥ e) = g.1.val *ᵥ e
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinv, hk]

/-- Helper: the action of `RatAutPlus f` on the poles of `f` by matrix multiplication. -/
instance : MulAction (RatAutPlus f) (PoleSet f) where
  smul g e := ⟨g.1.val *ᵥ e.1, e.2.smul g⟩
  one_smul e := by
    apply Subtype.ext
    show (1 : RatAutPlus f).1.val *ᵥ e.1 = e.1
    simp
  mul_smul g h e := by
    apply Subtype.ext
    show (g * h).1.val *ᵥ e.1 = g.1.val *ᵥ (h.1.val *ᵥ e.1)
    simp [Matrix.mulVec_mulVec]

/-- Helper: the underlying vector of $g \cdot e$ is $g e$. -/
theorem smul_val (g : RatAutPlus f) (e : PoleSet f) : (g • e).1 = g.1.val *ᵥ e.1 := rfl

/-- Helper: the set of poles is finite. -/
theorem finite_poleSet (hf : Siegel.RatPosDef f) : Finite (PoleSet f) := by
  have := finite_ratAutPlus hf
  have hfin : Set.Finite {e : Fin 3 → ℤ | Pole f e} := by
    have hsub : {e : Fin 3 → ℤ | Pole f e} ⊆
        ⋃ g : RatAutPlus f, {e | g ≠ 1 ∧ Prim e ∧ g.1.val *ᵥ e = e} := by
      rintro e ⟨hp, g, hg, hge⟩
      exact Set.mem_iUnion.2 ⟨g, hg, hp, hge⟩
    refine Set.Finite.subset ?_ hsub
    refine Set.finite_iUnion fun g => ?_
    by_cases hg : g = 1
    · simp [hg]
    · obtain ⟨e0, he0p, he0⟩ := exists_fixed_prim hf g
      refine (Set.toFinite {e0, -e0}).subset ?_
      rintro e ⟨-, hep, hee⟩
      rcases prim_fixed_unique hf g hg he0p hep he0 hee with h | h
      · exact Or.inl h
      · exact Or.inr h
  exact hfin.to_subtype

/-- Helper: a nonidentity proper automorph fixes exactly two poles. -/
theorem card_fixedBy (hf : Siegel.RatPosDef f) (g : RatAutPlus f) (hg : g ≠ 1) :
    Nat.card (MulAction.fixedBy (PoleSet f) g) = 2 := by
  obtain ⟨e0, he0p, he0⟩ := exists_fixed_prim hf g
  have P0 : Pole f e0 := ⟨he0p, g, hg, he0⟩
  have P1 : Pole f (-e0) := ⟨he0p.neg, g, hg, by rw [Matrix.mulVec_neg, he0]⟩
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨⟨e0, P0⟩, ?_⟩, ⟨⟨-e0, P1⟩, ?_⟩, ?_, ?_⟩
  · rw [MulAction.mem_fixedBy]; exact Subtype.ext he0
  · rw [MulAction.mem_fixedBy]; exact Subtype.ext (by rw [smul_val]; show g.1.val *ᵥ (-e0) = -e0; rw [Matrix.mulVec_neg, he0])
  · intro h
    have := congrArg (fun z => z.1.1) h
    simp only at this
    have h2 : e0 = 0 := by
      have : (2 : ℤ) • e0 = 0 := by rw [two_smul]; nth_rewrite 1 [this]; simp
      rcases smul_eq_zero.1 this with h | h
      · norm_num at h
      · exact h
    exact he0p.ne_zero h2
  · ext z
    obtain ⟨⟨e, hP⟩, hz⟩ := z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    have hfix : g.1.val *ᵥ e = e := congrArg Subtype.val (MulAction.mem_fixedBy.1 hz)
    rcases prim_fixed_unique hf g hg he0p hP.1 he0 hfix with h | h
    · left; exact Subtype.ext (Subtype.ext h)
    · right; exact Subtype.ext (Subtype.ext h)

/-- Helper: the stabiliser in `RatAutPlus f` of a pole has order $2, 3, 4$ or $6$ (it is cyclic by `stab_cyclic`,
nontrivial, and its elements have order $1, 2, 3, 4, 6$ by Example 15 (i)). -/
theorem stab_card (hf : Siegel.RatPosDef f) (x : PoleSet f) :
    Nat.card (MulAction.stabilizer (RatAutPlus f) x) = 2 ∨
      Nat.card (MulAction.stabilizer (RatAutPlus f) x) = 3 ∨
      Nat.card (MulAction.stabilizer (RatAutPlus f) x) = 4 ∨
      Nat.card (MulAction.stabilizer (RatAutPlus f) x) = 6 := by
  have := finite_ratAutPlus hf
  let ρ : MulAction.stabilizer (RatAutPlus f) x →* Matrix (Fin 3) (Fin 3) ℚ :=
    ratRep.comp ((RatAutPlus f).subtype.comp (MulAction.stabilizer (RatAutPlus f) x).subtype)
  have hρ : Function.Injective ρ := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact ratRep_injective hab
  have hrot : ∀ h, IsRot (RatQF.gram f) (ρ h) := fun h => rot_of_mem h.1
  have hxne : castVec x.1 ≠ 0 := castVec_ne_zero x.2.1.ne_zero
  have hfix : ∀ h, ρ h *ᵥ castVec x.1 = castVec x.1 := by
    intro h
    have h1 : h.1.1.val *ᵥ x.1 = x.1 := congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 h.2)
    show Ch9Ex6.toQ h.1.1.val *ᵥ castVec x.1 = castVec x.1
    rw [toQ_mulVec_castVec, h1]
  have hcyc : IsCyclic (MulAction.stabilizer (RatAutPlus f) x) :=
    stab_cyclic (def_gram hf) ρ hρ hrot hxne hfix
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.1 hcyc
  have hmem := orderOf_mem_one_two_three_four_six hf g.1
  rw [Subgroup.orderOf_coe, hg] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hne1 : Nat.card (MulAction.stabilizer (RatAutPlus f) x) ≠ 1 := by
    intro h1
    obtain ⟨k, hk1, hk⟩ := x.2.2
    have := Nat.card_eq_one_iff_unique.1 h1 |>.1
    apply hk1
    have : (⟨k, MulAction.mem_stabilizer_iff.2 (Subtype.ext hk)⟩ :
        MulAction.stabilizer (RatAutPlus f) x) = 1 := Subsingleton.elim _ _
    exact congrArg Subtype.val this
  omega

/-- Helper: for a positive definite rational ternary form the order of `RatAutPlus f` is one of
$1, 2, 4, 6, 8, 12, 24$. -/
theorem card_ratAutPlus_mem (hf : Siegel.RatPosDef f) :
    Nat.card (RatAutPlus f) ∈ ({1, 2, 4, 6, 8, 12, 24} : Finset ℕ) := by
  have := finite_ratAutPlus hf
  have := finite_poleSet hf
  have h := count_classify (G := RatAutPlus f) (X := PoleSet f) (card_fixedBy hf) (stab_card hf)
  have h3 : Nat.card (RatAutPlus f) ≠ 3 := by
    intro h3
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [h3])
    have hord : orderOf g.1.val = 3 := by rw [orderOf_units, Subgroup.orderOf_coe, hg]
    obtain ⟨-, S, hSdet, hS2, hSaut⟩ := Ch9Ex6.ex15_ii hf g.2.1 g.2.2 hord
    have hu : IsUnit S.det := by rw [hSdet]; exact isUnit_one
    have hs : Ch9Ex6.glOf S hu ∈ RatAutPlus f :=
      ⟨by simpa [Ch9Ex6.glOf_val] using hSdet, fun x => by simpa [Ch9Ex6.glOf_val] using hSaut x⟩
    have h2 : orderOf (⟨Ch9Ex6.glOf S hu, hs⟩ : RatAutPlus f) = 2 := by
      rw [← Subgroup.orderOf_coe]
      show orderOf (Ch9Ex6.glOf S hu) = 2
      rw [← orderOf_units]
      simpa [Ch9Ex6.glOf_val] using hS2
    have hdvd := orderOf_dvd_natCard (⟨Ch9Ex6.glOf S hu, hs⟩ : RatAutPlus f)
    rw [h2, h3] at hdvd
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-- **Cassels, Ch. 9, Example 15 (iv), the restriction on the order** (p. 166). For every positive definite
rational ternary form $f$ (`hf`) the order of the group `RatAutPlus f` of proper integral automorphs is one of
$1, 2, 4, 6, 8, 12, 24$; with `ex15_iv_occur` every one of these orders occurs. Unconditional.

*Proof* (classical pole counting, no assumed inputs). `RatAutPlus f` is finite (it lies in the automorph group of an
integral multiple of $f$). Let $A$ be the Gram matrix of $f$; an element $g$ satisfies $g^{\mathsf T}Ag = A$, $\det g = 1$,
so $\det(g - 1) = 0$ and `g` fixes a primitive vector $e \in \mathbb Z^3$; two fixed vectors with nonzero cross product
force $g = 1$ (the cross product $A^{-1}(e \times e')$ is a third fixed vector, `IsRot.eq_one_of_fixed_two`), so a
nonidentity $g$ fixes exactly the two primitive vectors $\pm e$ (`card_fixedBy`). The *poles* (primitive vectors fixed by
some $g \ne 1$) form a finite set on which the group acts. The stabiliser of a pole $e$ commutes with
$y \mapsto A^{-1}(e \times y)$ and so embeds in the circle group of $\mathbb C$, hence is cyclic (`stab_cyclic`), and by
(i) (`Siegel.orderOf_mem_of_proper_automorph`) has order $2, 3, 4$ or $6$ (`stab_card`). Burnside's lemma and the
orbit-stabiliser formula give $\sum_\omega N/n_\omega + 2N = kN + 2$ ($N$ the order, $k$ the number of orbits of poles,
$n_\omega$ the stabiliser orders), whose solutions are $N \in \{1, 2, 3, 4, 6, 8, 12, 24\}$ (`count_classify`).
Finally $N = 3$ is impossible: an element of order $3$ forces an element of order $2$ by (ii) (`Ch9Ex6.ex15_ii`),
and $2 \nmid 3$. -/
@[kb "cassels1978" "Ch. 9, Ex. 15 (iv), p. 166 (the possible orders)"]
theorem ex15ivOrders : Ch9Ex6.Ex15ivOrders := fun _ hf => card_ratAutPlus_mem hf

end Concrete

end QuadFormsKB.Cassels.Ch9Ex15Orders
