/-
# O'Meara §52: running-text claims on central simple algebras (pp. 118-129)

**Setting.** $F$ a field.  Algebras are Mathlib's `[Ring A] [Algebra F A]`; central simple algebras are the
bundled `CSA F`, similarity is `IsBrauerEquivalent`.

**Proves**
* `exists_submodule_eq_leftIdeal`, `exists_submodule_eq_twoSidedIdeal` (**52.r3**, p. 119): left ideals and
  two-sided ideals of an $F$-algebra are $F$-subspaces;
* `matrixUnit_mul`, `sum_matrixUnit_diag`, `stdBasis_eq_matrixUnit` (**52.r12**, p. 122): the matrix units
  $e_{ij}$ of $M_n(D)$ multiply by the rule $e_{ij}e_{kl} = \delta_{jk}e_{il}$, sum on the diagonal to $1$,
  and are the standard basis of $M_n(D)$ as a left $D$-module (Mathlib's `Matrix.stdBasis`);
* `nonempty_algEquiv_matrix_end` (**52.r13**, p. 125): $\operatorname{End}_D(V) \cong M_n(D)$ for a right
  $D$-space $V$ with a basis of $n$ elements;
* `isBrauerEquivalent_iff_nonempty_algEquiv_of_finrank_eq` (**52.r18**, p. 128): for central simple algebras
  of the same dimension, $A \sim A'$ iff $A \cong A'$.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.OMeara.Sec52F
import QuadFormsKB.Literature.OMeara.Sec52B

open scoped TensorProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.CSA52Text

/-! ### Ideals are subspaces (p. 119) -/

section Ideals

variable {F : Type*} [Field F] {A : Type*} [Ring A] [Algebra F A]

/-- **O'Meara §52, p. 119**: a left ideal $I$ of an $F$-algebra $A$ (a `Submodule A A`) is an
$F$-subspace of $A$: there is an $F$-subspace $W$ with the same elements (namely `I.restrictScalars F`). -/
@[kb "omeara1963" "§52, p. 119 (left ideals are F-subspaces)"]
theorem exists_submodule_eq_leftIdeal (I : Submodule A A) :
    ∃ W : Submodule F A, (W : Set A) = I :=
  ⟨I.restrictScalars F, rfl⟩

/-- **O'Meara §52, p. 119**: a two-sided ideal $I$ of an $F$-algebra $A$ (Mathlib `TwoSidedIdeal A`) is an
$F$-subspace of $A$, since $\alpha x = (\alpha 1_A) x$. -/
@[kb "omeara1963" "§52, p. 119 (two-sided ideals are F-subspaces)"]
theorem exists_submodule_eq_twoSidedIdeal (I : TwoSidedIdeal A) :
    ∃ W : Submodule F A, (W : Set A) = I :=
  ⟨{ carrier := I
     add_mem' := fun ha hb => add_mem ha hb
     zero_mem' := zero_mem I
     smul_mem' := fun c x hx => by
       rw [Algebra.smul_def]
       exact I.mul_mem_left _ _ hx }, rfl⟩

end Ideals

/-! ### Matrix units (p. 122) -/

section MatrixUnits

variable {D : Type*} [Ring D] {n : ℕ}

/-- **O'Meara §52, p. 122**: the matrix units $e_{ij}$ (entry $1$ in position $(i,j)$, $0$ elsewhere) of
$M_n(D)$ satisfy $e_{ij} e_{kl} = e_{il}$ if $j = k$ and $0$ otherwise.  Indices are 0-based
(`Fin n`). -/
@[kb "omeara1963" "§52, p. 122 (matrix units multiply as e_ij e_kl = δ_jk e_il)"]
theorem matrixUnit_mul (i j k l : Fin n) :
    (Matrix.single i j (1 : D)) * Matrix.single k l (1 : D) =
      if j = k then Matrix.single i l (1 : D) else 0 := by
  split_ifs with h
  · subst h; simp
  · simp [h]

/-- **O'Meara §52, p. 122**: $\sum_i e_{ii} = 1$ in $M_n(D)$. -/
@[kb "omeara1963" "§52, p. 122 (sum of diagonal matrix units is 1)"]
theorem sum_matrixUnit_diag :
    ∑ i : Fin n, Matrix.single i i (1 : D) = (1 : Matrix (Fin n) (Fin n) D) := by
  ext a b
  rw [Matrix.sum_apply]
  by_cases h : a = b
  · subst h
    rw [Finset.sum_eq_single a]
    · simp
    · intro i _ hi; simp [Matrix.single_apply]; tauto
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [h]
    · intro i _
      by_cases hi : i = a
      · subst hi; simp [Matrix.single_apply]; tauto
      · simp [Matrix.single_apply]; tauto

/-- **O'Meara §52, p. 122**: the $n^2$ matrix units $e_{ij}$ form a basis of $M_n(D)$ as a left
$D$-module: Mathlib's `Matrix.stdBasis D (Fin n) (Fin n)` (indexed by `Fin n × Fin n`) has
$(i,j) \mapsto e_{ij}$.  (Over $D = F$ this is the $F$-basis of $M_n(F)$.) -/
@[kb "omeara1963" "§52, p. 122 (matrix units form a basis)"]
theorem stdBasis_eq_matrixUnit (i j : Fin n) :
    Matrix.stdBasis D (Fin n) (Fin n) (i, j) = Matrix.single i j (1 : D) :=
  Matrix.stdBasis_eq_single D i j

end MatrixUnits

/-! ### Endomorphisms of a right vector space (p. 125) -/

section EndMatrix

variable {F : Type*} [Field F] {D : Type*} [DivisionRing D] [Algebra F D]
  {V : Type*} [AddCommGroup V] [Module Dᵐᵒᵖ V] [Module F V] [IsScalarTower F Dᵐᵒᵖ V]
  [SMulCommClass Dᵐᵒᵖ F V] {n : ℕ}

open MulOpposite in
/-- The matrix of an endomorphism $f$ of the right $D$-space $V$ in the basis $b$:
$f(b_j) = \sum_i b_i a_{ij}$ (the right action of $a \in D$ is the left action of `op a`). -/
def endMatrix (b : Module.Basis (Fin n) Dᵐᵒᵖ V) (f : Module.End Dᵐᵒᵖ V) :
    Matrix (Fin n) (Fin n) D :=
  fun i j => unop (b.repr (f (b j)) i)

open MulOpposite in
/-- The endomorphism with matrix $M$ in the basis $b$. -/
def matrixEnd (b : Module.Basis (Fin n) Dᵐᵒᵖ V) (M : Matrix (Fin n) (Fin n) D) :
    Module.End Dᵐᵒᵖ V :=
  b.constr ℕ (fun j => ∑ i, op (M i j) • b i)

open MulOpposite in
theorem endMatrix_mul (b : Module.Basis (Fin n) Dᵐᵒᵖ V) (f g : Module.End Dᵐᵒᵖ V) :
    endMatrix b (f * g) = endMatrix b f * endMatrix b g := by
  ext i j
  simp only [endMatrix, Matrix.mul_apply, Module.End.mul_apply]
  conv_lhs => rw [← b.sum_repr (g (b j)), map_sum]
  apply op_injective
  simp [Finset.sum_apply]

open MulOpposite in
theorem endMatrix_matrixEnd (b : Module.Basis (Fin n) Dᵐᵒᵖ V) (M : Matrix (Fin n) (Fin n) D) :
    endMatrix b (matrixEnd b M) = M := by
  ext i j
  simp [endMatrix, matrixEnd, Finsupp.single_apply]

open MulOpposite in
theorem matrixEnd_endMatrix (b : Module.Basis (Fin n) Dᵐᵒᵖ V) (f : Module.End Dᵐᵒᵖ V) :
    matrixEnd b (endMatrix b f) = f := by
  apply b.ext
  intro j
  simp only [matrixEnd, Module.Basis.constr_basis, endMatrix, op_unop]
  exact b.sum_repr (f (b j))

theorem endMatrix_add (b : Module.Basis (Fin n) Dᵐᵒᵖ V) (f g : Module.End Dᵐᵒᵖ V) :
    endMatrix b (f + g) = endMatrix b f + endMatrix b g := by
  ext i j
  simp [endMatrix]

open MulOpposite in
theorem endMatrix_algebraMap (b : Module.Basis (Fin n) Dᵐᵒᵖ V) (c : F) :
    endMatrix b (algebraMap F (Module.End Dᵐᵒᵖ V) c) = algebraMap F (Matrix (Fin n) (Fin n) D) c := by
  ext i j
  have h : ∀ v : V, algebraMap F (Module.End Dᵐᵒᵖ V) c v = (algebraMap F Dᵐᵒᵖ c) • v := by
    intro v
    rw [Module.algebraMap_end_apply, algebraMap_smul]
  simp only [endMatrix, h, map_smul, Finsupp.smul_apply, smul_eq_mul, Matrix.algebraMap_eq_diagonal]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Matrix.diagonal_apply_ne]

/-- **O'Meara §52, p. 125**: let $D$ be a division algebra over $F$ and $V$ a right $D$-space (Lean:
a module over `Dᵐᵒᵖ`, with the right action $v a$ being `op a • v`) having a basis $b_0,\dots,b_{n-1}$ of $n$
elements.  Then the $D$-linear endomorphisms of $V$ (written on the left, composed as functions) form an
$F$-algebra `Module.End Dᵐᵒᵖ V` isomorphic to the matrix algebra $M_n(D)$ (matrices over $D$, **not**
$D^{\mathrm{op}}$): $f$ corresponds to $(a_{ij})$ with $f(b_j) = \sum_i b_i a_{ij}$, and then $fg$
corresponds to the product of the matrices.  *Hypotheses needed for the $F$-algebra structure of the
endomorphism ring* (Mathlib's `Module.End.instAlgebra`): $V$ is also an $F$-space with $F$ acting
compatibly with $D$ (`IsScalarTower F Dᵐᵒᵖ V`) and commuting with it (`SMulCommClass Dᵐᵒᵖ F V`); this is
the situation in the book, where $V$ is an $F$-space on which $D \supseteq F$ acts. -/
@[kb "omeara1963" "§52, p. 125 (End_D(V) ≅ M_n(D))"]
theorem nonempty_algEquiv_matrix_end (b : Module.Basis (Fin n) Dᵐᵒᵖ V) :
    Nonempty (Module.End Dᵐᵒᵖ V ≃ₐ[F] Matrix (Fin n) (Fin n) D) :=
  ⟨{ toFun := endMatrix b
     invFun := matrixEnd b
     left_inv := matrixEnd_endMatrix b
     right_inv := endMatrix_matrixEnd b
     map_mul' := endMatrix_mul b
     map_add' := endMatrix_add b
     commutes' := endMatrix_algebraMap b }⟩

end EndMatrix

/-! ### Similarity and isomorphism of central simple algebras (p. 128) -/

section Similar

universe u

open CSA52 in
/-- **O'Meara §52, p. 128**: for central simple algebras $A$, $A'$ over $F$ of the same dimension,
$A \sim A'$ if and only if $A \cong A'$.  The backward direction is
`CSA52.isBrauerEquivalent_of_algEquiv` (isomorphic algebras are similar; the equal-dimension hypothesis is
only needed for the forward direction).  The forward direction is the argument of
`Hasse58.Rev.nonempty_algEquiv_of_isBrauerEquivalent_of_finrank_eq` (52:9 and a dimension count), repeated here
because that library lemma sits in a section with an unused hypothesis `[Invertible (2 : F)]`, whereas the
book (and this statement) has no restriction on the characteristic. -/
@[kb "omeara1963" "§52, p. 128 (similar algebras of equal dimension are isomorphic)"]
theorem isBrauerEquivalent_iff_nonempty_algEquiv_of_finrank_eq {F : Type u} [Field F]
    {A A' : CSA.{u, u} F} (h : Module.finrank F A = Module.finrank F A') :
    IsBrauerEquivalent A A' ↔ Nonempty (A ≃ₐ[F] A') :=
  ⟨fun hs => by
    have : IsArtinianRing A := IsArtinianRing.of_finite F A
    have : IsArtinianRing A' := IsArtinianRing.of_finite F A'
    obtain ⟨n, hn, D, _, _, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite F A
    obtain ⟨m, hm, D', _, _, _, ⟨e'⟩⟩ :=
      IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite F A'
    obtain ⟨ε⟩ := (isBrauerEquivalent_iff_nonempty_algEquiv (A := A) (A' := A') e e').1 hs
    have h1 : Module.finrank F A = n * n * Module.finrank F D := by
      rw [e.toLinearEquiv.finrank_eq, Module.finrank_matrix]; simp
    have h2 : Module.finrank F A' = m * m * Module.finrank F D' := by
      rw [e'.toLinearEquiv.finrank_eq, Module.finrank_matrix]; simp
    have h3 : Module.finrank F D = Module.finrank F D' := ε.toLinearEquiv.finrank_eq
    have hD : 0 < Module.finrank F D := Module.finrank_pos
    have h4 : n * n = m * m := by
      rw [h1, h2, h3] at h
      exact Nat.eq_of_mul_eq_mul_right (h3 ▸ hD) h
    have h5 : n = m := Nat.mul_self_inj.1 h4
    subst h5
    exact ⟨e.trans (ε.mapMatrix.trans e'.symm)⟩,
    fun ⟨e⟩ => isBrauerEquivalent_of_algEquiv e⟩

end Similar

end QuadFormsKB.OMeara.CSA52Text
