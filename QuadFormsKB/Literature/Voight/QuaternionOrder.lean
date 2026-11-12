/-
# The even Clifford algebra of a nondegenerate ternary form is a quaternion order (Voight, Cor. 22.3.22)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021, Corollary 22.3.22 (key `voight2021`);
see also Example 22.3.10 and Lemma 5.3.21.

**Statement** (`isQuaternionOrder_clf0`). Let $R$ be a domain with fraction field $F$ in which
$2 \ne 0$, and let $Q$ be a ternary quadratic form over $R$ with half-discriminant
$N = 4abc + uvw - au^2 - bv^2 - cw^2 \ne 0$ (`ternaryDisc`). Then
$\operatorname{Clf}^0(Q)$ is a quaternion $R$-order: it is a free $R$-module of rank $4$ (so finitely
generated and torsion-free) and $F \otimes_R \operatorname{Clf}^0(Q) \cong \operatorname{Clf}^0(Q_F)$ is a
quaternion algebra over $F$. This is the first clause (`EvenCliffordCorrespondence.isQuaternionOrder`) of
Main Theorem 22.4.1, proved here under the extra hypothesis $\operatorname{char} F \ne 2$ (Voight's
statement has no such hypothesis).

**Proof.**
* Over a field $F$ with $2 \ne 0$ (`isQuaternionAlgebra_clf0_field`): $N \ne 0$ makes $Q$ nondegenerate,
  so $Q \simeq \langle w_0, w_1, w_2\rangle$ with $w_p \in F^\times$ (Mathlib's
  `equivalent_weightedSumSquares_units_of_nondegenerate'`); an isometry induces an isomorphism of even
  Clifford algebras (`evenEquivOfIsometry`); and the even Clifford algebra of a diagonal form is a
  quaternion algebra: $\operatorname{Clf}^0\langle w_0, w_1, w_2\rangle \cong (-w_1w_2, -w_0w_2 \mid F)$, with
  $i \mapsto i$, $j \mapsto j$, $k \mapsto -ij/w_2$ (`EvenClf.diagQuatEquiv`, the case $c \ne 1$ of
  Example 22.3.10).
* Base change (`EvenClf.baseChangeEquiv`): $F \otimes_R \operatorname{Clf}^0(Q) \cong \operatorname{Clf}^0(Q_F)$,
  since both have the basis $1, i, j, k$ with the same multiplication table.

Indices are 0-based (Voight's $e_1, e_2, e_3$ are $e_0, e_1, e_2$).
-/
import QuadFormsKB.Literature.Voight.Functoriality
import QuadFormsKB.Witt.Bridge
import Mathlib.RingTheory.TensorProduct.Free

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

open scoped TensorProduct Quaternion

namespace QuadFormsKB.Voight

namespace EvenClf

/-! ## Algebra structure over a base of the coefficient ring -/

section Scalars

variable {S R : Type*} [CommRing S] [CommRing R] [Algebra S R] {a b c u v w : R}

/-- `EvenClf R a b c u v w` is an $S$-algebra for every commutative ring $S$ such that $R$ is an
$S$-algebra (scalars act coordinatewise; $s \mapsto s \cdot 1$). Low priority, so that for
$S = R$ the instance `EvenClf.instAlgebra` is used. -/
instance (priority := 50) instAlgebraOver : Algebra S (EvenClf R a b c u v w) where
  algebraMap :=
  { toFun s := ⟨algebraMap S R s, 0, 0, 0⟩
    map_one' := by ext <;> simp
    map_zero' := by ext <;> simp
    map_mul' x y := by ext <;> simp
    map_add' x y := by ext <;> simp }
  smul_def' s x := by ext <;> simp [Algebra.smul_def]
  commutes' s x := by ext <;> simp <;> ring

@[simp] theorem algebraMapOver_re (s : S) :
    (algebraMap S (EvenClf R a b c u v w) s).re = algebraMap S R s := rfl
@[simp] theorem algebraMapOver_i (s : S) : (algebraMap S (EvenClf R a b c u v w) s).i = 0 := rfl
@[simp] theorem algebraMapOver_j (s : S) : (algebraMap S (EvenClf R a b c u v w) s).j = 0 := rfl
@[simp] theorem algebraMapOver_k (s : S) : (algebraMap S (EvenClf R a b c u v w) s).k = 0 := rfl

instance instIsScalarTower : IsScalarTower S R (EvenClf R a b c u v w) :=
  ⟨fun s r x => by ext <;> simp [smul_mul_assoc]⟩

end Scalars

/-! ## Base change -/

section BaseChange

variable {R F : Type*} [CommRing R] [Field F] [Algebra R F] {a b c u v w : R}

/-- The coefficientwise map $\operatorname{Clf}^0$ over $R$ $\to$ $\operatorname{Clf}^0$ over $F$. -/
def mapAlgHom (a b c u v w : R) :
    EvenClf R a b c u v w →ₐ[R] EvenClf F (algebraMap R F a) (algebraMap R F b) (algebraMap R F c)
      (algebraMap R F u) (algebraMap R F v) (algebraMap R F w) where
  toFun x := ⟨algebraMap R F x.re, algebraMap R F x.i, algebraMap R F x.j, algebraMap R F x.k⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_mul' x y := by ext <;> simp
  map_add' x y := by ext <;> simp
  commutes' r := by ext <;> simp

/-- The $F$-algebra map $F \otimes_R \operatorname{Clf}^0(Q) \to \operatorname{Clf}^0(Q_F)$,
$t \otimes x \mapsto t \cdot x$. -/
noncomputable def baseChangeHom (a b c u v w : R) :
    F ⊗[R] EvenClf R a b c u v w →ₐ[F] EvenClf F (algebraMap R F a) (algebraMap R F b)
      (algebraMap R F c) (algebraMap R F u) (algebraMap R F v) (algebraMap R F w) :=
  Algebra.TensorProduct.lift (Algebra.ofId F _) (mapAlgHom a b c u v w)
    (fun x y => by rw [Algebra.ofId_apply]; exact Algebra.commute_algebraMap_left _ _)

theorem basisOneIJK_apply' {S : Type*} [CommRing S] {a b c u v w : S} (n : Fin 4) :
    (basisOneIJK n : EvenClf S a b c u v w) =
      ⟨(Pi.single n (1 : S) : Fin 4 → S) 0, (Pi.single n (1 : S) : Fin 4 → S) 1,
        (Pi.single n (1 : S) : Fin 4 → S) 2, (Pi.single n (1 : S) : Fin 4 → S) 3⟩ := by
  rw [basisOneIJK, Module.Basis.coe_ofEquivFun]; rfl

theorem baseChangeHom_basis (a b c u v w : R) (n : Fin 4) :
    baseChangeHom (F := F) a b c u v w (Algebra.TensorProduct.basis F basisOneIJK n) =
      basisOneIJK n := by
  rw [Algebra.TensorProduct.basis_apply, baseChangeHom]
  erw [Algebra.TensorProduct.lift_tmul]
  rw [map_one, one_mul]
  rw [basisOneIJK_apply', basisOneIJK_apply']
  fin_cases n <;> ext <;> simp [mapAlgHom, Pi.single_apply]

/-- **Base change of the even Clifford algebra** (Voight 22.2.11, compatibility with base change):
for any commutative ring $R$ and field $F$ that is an $R$-algebra,
$F \otimes_R \operatorname{Clf}^0(a,b,c,u,v,w) \cong \operatorname{Clf}^0$ of the images of the coefficients
in $F$, as $F$-algebras. -/
noncomputable def baseChangeEquiv (a b c u v w : R) :
    F ⊗[R] EvenClf R a b c u v w ≃ₐ[F] EvenClf F (algebraMap R F a) (algebraMap R F b)
      (algebraMap R F c) (algebraMap R F u) (algebraMap R F v) (algebraMap R F w) := by
  refine AlgEquiv.ofBijective (baseChangeHom a b c u v w) ?_
  let e : F ⊗[R] EvenClf R a b c u v w ≃ₗ[F] EvenClf F (algebraMap R F a) (algebraMap R F b)
      (algebraMap R F c) (algebraMap R F u) (algebraMap R F v) (algebraMap R F w) :=
    (Algebra.TensorProduct.basis F basisOneIJK).equiv basisOneIJK (Equiv.refl _)
  have : (baseChangeHom (F := F) a b c u v w).toLinearMap = e.toLinearMap := by
    apply (Algebra.TensorProduct.basis F basisOneIJK).ext
    intro n
    simp only [AlgHom.toLinearMap_apply, LinearEquiv.coe_coe, e, Module.Basis.equiv_apply,
      Equiv.refl_apply]
    exact baseChangeHom_basis a b c u v w n
  have h : ⇑(baseChangeHom (F := F) a b c u v w) = ⇑e := by
    rw [← AlgHom.coe_toLinearMap, this]; rfl
  rw [h]
  exact e.bijective

end BaseChange

/-! ## The diagonal case over a field -/

section Diag

variable {F : Type*} [Field F]

/-- **The even Clifford algebra of a diagonal form is a quaternion algebra** (Voight 5.3.23 and
Example 22.3.10, general diagonal case): for $a, b, c \in F$ with $c \ne 0$,
$\operatorname{Clf}^0\langle a, b, c\rangle \cong (-bc, -ac \mid F)$ (Mathlib's `ℍ[F,-bc,-ac]`).
In $\operatorname{Clf}^0\langle a,b,c\rangle$ (so $u = v = w = 0$) the table reads $i^2 = -bc$, $j^2 = -ac$,
$ij = -ck = -ji$; the isomorphism sends $i, j, ij$ to $i, j, -ck$. -/
@[kb "voight2021" "5.3.23, p. 73; Example 22.3.10, p. 361"]
def diagQuatEquiv (a b c : F) (hc : c ≠ 0) :
    ℍ[F, -(b * c), -(a * c)] ≃ₐ[F] EvenClf F a b c 0 0 0 where
  toFun x := ⟨x.re, x.imI, x.imJ, -c * x.imK⟩
  invFun y := ⟨y.re, y.i, y.j, -y.k / c⟩
  left_inv x := by ext <;> simp; field_simp
  right_inv y := by ext <;> simp; field_simp
  map_mul' x y := by ext <;> simp <;> ring
  map_add' x y := by ext <;> simp; ring
  commutes' r := by ext <;> simp

end Diag

end EvenClf

/-! ## Quaternion algebras -/

/-- `IsQuaternionAlgebra` is invariant under algebra isomorphism. -/
theorem IsQuaternionAlgebra.of_algEquiv {F B B' : Type*} [Field F] [Ring B] [Algebra F B] [Ring B']
    [Algebra F B'] (e : B ≃ₐ[F] B') (h : IsQuaternionAlgebra F B') : IsQuaternionAlgebra F B := by
  obtain ⟨c₁, c₂, c₃, h1, h3, ⟨f⟩⟩ := h
  exact ⟨c₁, c₂, c₃, h1, h3, ⟨e.trans f⟩⟩

/-- **$\operatorname{Clf}^0(Q)$ is a quaternion algebra for nondegenerate $Q$ over a field**
(Voight 2021, 22.1 and Corollary 22.3.22 over a field; char $\ne 2$): if $F$ is a field with
$2 \ne 0$ and $Q$ is a ternary form over $F$ with half-discriminant $N \ne 0$, then the even
Clifford algebra $\operatorname{Clf}^0(Q)$ is a quaternion algebra over $F$. -/
@[kb "voight2021" "Corollary 22.3.22, p. 362"]
theorem isQuaternionAlgebra_clf0_field {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (Q : QuadForm F 3)
    (hN : ternaryDisc Q ≠ 0) : IsQuaternionAlgebra F (Clf0 Q) := by
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hnd : Q.Nondegenerate := by
    unfold QuadForm.Nondegenerate
    rw [← two_mul_ternaryDisc]
    exact mul_ne_zero h2 hN
  set Q' := Q.toQuadraticFormIn F with hQ'
  have hpol := (QuadForm.nondegenerate_polarBilin_toQuadraticFormIn (K := F) hnd).1
  have hsep : (QuadraticMap.associated (R := F) Q').SeparatingLeft := by
    intro x hx
    refine hpol x fun y => ?_
    have := hx y
    rw [QuadraticMap.associated_apply] at this
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
    have h' : ⅟(2 : F) * (Q' (x + y) - Q' x - Q' y) = 0 := this
    rcases mul_eq_zero.1 h' with h | h
    · exact absurd h (by rw [invOf_eq_inv]; exact inv_ne_zero h2)
    · exact h
  have key : ∀ k, Module.finrank F (Fin 3 → F) = k →
      ∃ w : Fin k → Fˣ, Q'.Equivalent (QuadraticMap.weightedSumSquares F w) := by
    intro k hk
    subst hk
    exact QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate' Q' hsep
  obtain ⟨w, ⟨e⟩⟩ := key 3 (by simp)
  have hQf : EvenClf.IsTernaryFormula Q' (Q.coeff 0 0) (Q.coeff 1 1) (Q.coeff 2 2) (Q.coeff 1 2)
      (Q.coeff 0 2) (Q.coeff 0 1) := fun x => by
    rw [hQ', QuadForm.toQuadraticFormIn_apply]
    exact eval_ternary Q x
  have hWf : EvenClf.IsTernaryFormula (QuadraticMap.weightedSumSquares F w) (w 0 : F) (w 1) (w 2)
      0 0 0 := fun x => by
    simp [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_three, Units.smul_def, pow_two]
  have hc : ((w 2 : Fˣ) : F) ≠ 0 := (w 2).ne_zero
  refine ⟨-((w 1 : F) * w 2), 0, -((w 0 : F) * w 2), ?_, ?_, ⟨?_⟩⟩
  · have h4 : (4 : F) ≠ 0 := by
      rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add, mul_neg,
      neg_eq_zero, mul_eq_zero, not_or]
    exact ⟨h4, (w 1).ne_zero, hc⟩
  · simp only [ne_eq, neg_eq_zero, mul_eq_zero, not_or]
    exact ⟨(w 0).ne_zero, hc⟩
  · exact (EvenClf.equivEven hQf).trans ((evenEquivOfIsometry e).trans
      ((EvenClf.equivEven hWf).symm.trans (EvenClf.diagQuatEquiv _ _ _ hc).symm))

/-- **Corollary 22.3.22 (Voight 2021): $\operatorname{Clf}^0(Q)$ is a quaternion order**, for a domain
$R$ whose fraction field $F$ has $2 \ne 0$: if the ternary form $Q$ over $R$ has half-discriminant
$N = 4abc + uvw - au^2 - bv^2 - cw^2 \ne 0$, then $\operatorname{Clf}^0(Q)$ is a quaternion $R$-order
(`IsQuaternionOrder`: finitely generated and torsion-free over $R$, and $F \otimes_R \operatorname{Clf}^0(Q)$
a quaternion algebra over $F$). This is the clause `EvenCliffordCorrespondence.isQuaternionOrder` of
Main Theorem 22.4.1 when $\operatorname{char} F \ne 2$. -/
@[kb "voight2021" "Corollary 22.3.22, p. 362"]
theorem isQuaternionOrder_clf0 {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] (h2 : (2 : F) ≠ 0) (Q : QuadForm R 3) (hN : ternaryDisc Q ≠ 0) :
    IsQuaternionOrder R F (Clf0 Q) where
  finite := inferInstance
  torsionFree := (EvenClf.equivProd _ _ _ _ _ _).injective.moduleIsTorsionFree _ fun _ _ => rfl
  quaternion := by
    have hN' : ternaryDisc (Q.map (algebraMap R F)) ≠ 0 := by
      have : ternaryDisc (Q.map (algebraMap R F)) = algebraMap R F (ternaryDisc Q) := by
        simp only [ternaryDisc, EvenClf.halfDisc, QuadForm.map, Matrix.map_apply, map_sub, map_add,
          map_mul, map_pow, map_ofNat]
      rw [this]
      exact (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hN
    exact IsQuaternionAlgebra.of_algEquiv (EvenClf.baseChangeEquiv _ _ _ _ _ _)
      (isQuaternionAlgebra_clf0_field h2 (Q.map (algebraMap R F)) hN')

end QuadFormsKB.Voight
