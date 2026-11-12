/-
# The explicit even Clifford algebra is Mathlib's even Clifford algebra (Voight, 22.3.4)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021, Chapter 22 (bibliography key
`voight2021`).

For a ternary quadratic form
$$Q = a x_0^2 + b x_1^2 + c x_2^2 + u x_1 x_2 + v x_0 x_2 + w x_0 x_1$$
over a commutative ring $R$, `QuadFormsKB.Voight.EvenClf` is the algebra defined by Voight's
multiplication table (basis $1, i, j, k$, with $i = e_1 e_2$, $j = e_2 e_0$, $k = e_0 e_1$ in 0-based
indices). We prove, **over every commutative ring $R$** (no hypothesis on the characteristic), that
it is isomorphic as an $R$-algebra to Mathlib's even Clifford algebra `CliffordAlgebra.even` of the
corresponding Mathlib quadratic form (`clf0EquivEven`). In particular $\operatorname{Clf}^0(Q)$ is
free of rank $4$ with basis $1, i, j, k$ (Voight 22.2.9 / 22.3.4).

The proof builds both directions:
* `CliffordAlgebra.even.lift` applied to the bilinear map $(x, y) \mapsto \sum x_p y_q [e_p e_q]$,
  where $[e_1e_2] = i$, $[e_2 e_1] = u - i$, $[e_2 e_0] = j$, $[e_0 e_2] = v - j$, $[e_0 e_1] = k$,
  $[e_1 e_0] = w - k$ and $[e_p e_p] = Q(e_p)$ (`toEvenClf`);
* the algebra map sending $i, j, k$ to $\iota e_1 \iota e_2$, $\iota e_2 \iota e_0$,
  $\iota e_0 \iota e_1$ (`ofEvenClf`), well defined because the nine products of these satisfy
  Voight's table, which follows from $\iota(e_p)^2 = Q(e_p)$ and the anticommutation relations
  alone (`table_of_clifford`).

The general statement is `EvenClf.equivEven`, for any Mathlib form `Q'` on `Fin 3 → R` satisfying the
coordinate formula (`EvenClf.IsTernaryFormula`); `clf0EquivEven` specializes it to
`QuadForm.toQuadraticForm Q` for `Q : QuadForm R 3`.

Indices are 0-based (Voight's $e_1, e_2, e_3$ are $e_0, e_1, e_2$ here).
-/
import QuadFormsKB.Literature.Voight.EvenClifford
import QuadFormsKB.Equiv.Mathlib
import Mathlib.LinearAlgebra.CliffordAlgebra.Even

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace QuadFormsKB.Voight
namespace EvenClf

variable {R : Type*} [CommRing R] {a b c u v w : R}

section Generic

variable {A : Type*} [Ring A] [Algebra R A] (x0 x1 x2 : A)

/-- **Voight's table from the Clifford relations.** In any $R$-algebra $A$, if $x_0, x_1, x_2$
satisfy $x_0^2 = a$, $x_1^2 = b$, $x_2^2 = c$, $x_1x_2 + x_2x_1 = u$, $x_0x_2 + x_2x_0 = v$,
$x_0x_1 + x_1x_0 = w$, then $i = x_1x_2$, $j = x_2x_0$, $k = x_0x_1$ satisfy the nine products of
Voight (22.3.7), (22.3.8): $i^2 = ui - bc$, $j^2 = vj - ac$, $k^2 = wk - ab$, $jk = a(u - i)$,
$ki = b(v - j)$, $ij = c(w - k)$, $kj = -vw + ai + wj + vk$, $ik = -uw + wi + bj + uk$,
$ji = -uv + vi + uj + ck$. -/
theorem table_of_clifford
    (h0 : x0 * x0 = a • 1) (h1 : x1 * x1 = b • 1) (h2 : x2 * x2 = c • 1)
    (h12 : x1 * x2 + x2 * x1 = u • 1) (h02 : x0 * x2 + x2 * x0 = v • 1)
    (h01 : x0 * x1 + x1 * x0 = w • 1) :
    (x1 * x2) * (x1 * x2) = u • (x1 * x2) - (b * c) • 1 ∧
    (x2 * x0) * (x2 * x0) = v • (x2 * x0) - (a * c) • 1 ∧
    (x0 * x1) * (x0 * x1) = w • (x0 * x1) - (a * b) • 1 ∧
    (x2 * x0) * (x0 * x1) = a • (u • 1 - x1 * x2) ∧
    (x0 * x1) * (x1 * x2) = b • (v • 1 - x2 * x0) ∧
    (x1 * x2) * (x2 * x0) = c • (w • 1 - x0 * x1) ∧
    (x0 * x1) * (x2 * x0) = (-(v * w)) • 1 + a • (x1 * x2) + w • (x2 * x0) + v • (x0 * x1) ∧
    (x1 * x2) * (x0 * x1) = (-(u * w)) • 1 + w • (x1 * x2) + b • (x2 * x0) + u • (x0 * x1) ∧
    (x2 * x0) * (x1 * x2) = (-(u * v)) • 1 + v • (x1 * x2) + u • (x2 * x0) + c • (x0 * x1) := by
  have s10 : x1 * x0 = w • 1 - x0 * x1 := eq_sub_of_add_eq' h01
  have s20 : x2 * x0 = v • 1 - x0 * x2 := eq_sub_of_add_eq' h02
  have s21 : x2 * x1 = u • 1 - x1 * x2 := eq_sub_of_add_eq' h12
  have t0 : ∀ y : A, x0 * (x0 * y) = a • y := fun y => by
    rw [← mul_assoc, h0, smul_mul_assoc, one_mul]
  have t1 : ∀ y : A, x1 * (x1 * y) = b • y := fun y => by
    rw [← mul_assoc, h1, smul_mul_assoc, one_mul]
  have t2 : ∀ y : A, x2 * (x2 * y) = c • y := fun y => by
    rw [← mul_assoc, h2, smul_mul_assoc, one_mul]
  have s10' : ∀ y : A, x1 * (x0 * y) = w • y - x0 * (x1 * y) := fun y => by
    rw [← mul_assoc, s10, sub_mul, smul_mul_assoc, one_mul, mul_assoc]
  have s20' : ∀ y : A, x2 * (x0 * y) = v • y - x0 * (x2 * y) := fun y => by
    rw [← mul_assoc, s20, sub_mul, smul_mul_assoc, one_mul, mul_assoc]
  have s21' : ∀ y : A, x2 * (x1 * y) = u • y - x1 * (x2 * y) := fun y => by
    rw [← mul_assoc, s21, sub_mul, smul_mul_assoc, one_mul, mul_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [mul_assoc, s10', s20', s21', s10, s20, s21, t0, t1, t2, h0, h1, h2, mul_sub, sub_mul,
      smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_sub, smul_smul, smul_add]
    module

/-- **The algebra map out of `EvenClf`**: given $x_0, x_1, x_2$ in an $R$-algebra $A$ satisfying the
Clifford relations for $(a, b, c, u, v, w)$, the map
$t + x i + y j + z k \mapsto t + x\, x_1x_2 + y\, x_2x_0 + z\, x_0x_1$ is an $R$-algebra
homomorphism (multiplicativity is `table_of_clifford`). -/
def toAlg (h0 : x0 * x0 = a • 1) (h1 : x1 * x1 = b • 1) (h2 : x2 * x2 = c • 1)
    (h12 : x1 * x2 + x2 * x1 = u • 1) (h02 : x0 * x2 + x2 * x0 = v • 1)
    (h01 : x0 * x1 + x1 * x0 = w • 1) : EvenClf R a b c u v w →ₐ[R] A where
  toFun x := x.re • (1 : A) + x.i • (x1 * x2) + x.j • (x2 * x0) + x.k • (x0 * x1)
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by
    simp only [add_re, add_i, add_j, add_k]
    module
  map_mul' x y := by
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ :=
      table_of_clifford x0 x1 x2 h0 h1 h2 h12 h02 h01
    simp only [mul_re, mul_i, mul_j, mul_k, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      smul_smul, one_mul, mul_one, r1, r2, r3, r4, r5, r6, r7, r8, r9]
    module
  commutes' r := by
    simp [Algebra.algebraMap_eq_smul_one]

theorem toAlg_apply (h0 : x0 * x0 = a • 1) (h1 : x1 * x1 = b • 1) (h2 : x2 * x2 = c • 1)
    (h12 : x1 * x2 + x2 * x1 = u • 1) (h02 : x0 * x2 + x2 * x0 = v • 1)
    (h01 : x0 * x1 + x1 * x0 = w • 1) (x : EvenClf R a b c u v w) :
    toAlg x0 x1 x2 h0 h1 h2 h12 h02 h01 x =
      x.re • (1 : A) + x.i • (x1 * x2) + x.j • (x2 * x0) + x.k • (x0 * x1) := rfl

end Generic

section Mathlib

open CliffordAlgebra

variable {Q' : QuadraticForm R (Fin 3 → R)}

/-- **The coordinate formula** for a Mathlib quadratic form on $R^3$:
$Q'(x) = a x_0^2 + b x_1^2 + c x_2^2 + u x_1 x_2 + v x_0 x_2 + w x_0 x_1$ (Voight (22.3.5),
0-based). For `Q'` $=$ `QuadForm.toQuadraticForm Q` this holds with Voight's coefficients of `Q`
(`isTernaryFormula_toQuadraticForm`). -/
def IsTernaryFormula (Q' : QuadraticForm R (Fin 3 → R)) (a b c u v w : R) : Prop :=
  ∀ x : Fin 3 → R, Q' x = a * x 0 ^ 2 + b * x 1 ^ 2 + c * x 2 ^ 2 + u * x 1 * x 2
    + v * x 0 * x 2 + w * x 0 * x 1

/-- **The Clifford relations** for the standard basis vectors $e_0, e_1, e_2$ of $R^3$ in
`CliffordAlgebra Q'`: $\iota(e_p)^2 = Q'(e_p)$ and $\iota(e_p)\iota(e_q) + \iota(e_q)\iota(e_p) =
B(e_p, e_q)$, which are $a, b, c$ and $u, v, w$ respectively. -/
theorem clifford_relations (hQ : IsTernaryFormula Q' a b c u v w) :
    ι Q' (Pi.single 0 1) * ι Q' (Pi.single 0 1) = a • (1 : CliffordAlgebra Q') ∧
    ι Q' (Pi.single 1 1) * ι Q' (Pi.single 1 1) = b • (1 : CliffordAlgebra Q') ∧
    ι Q' (Pi.single 2 1) * ι Q' (Pi.single 2 1) = c • (1 : CliffordAlgebra Q') ∧
    ι Q' (Pi.single 1 1) * ι Q' (Pi.single 2 1) + ι Q' (Pi.single 2 1) * ι Q' (Pi.single 1 1)
      = u • (1 : CliffordAlgebra Q') ∧
    ι Q' (Pi.single 0 1) * ι Q' (Pi.single 2 1) + ι Q' (Pi.single 2 1) * ι Q' (Pi.single 0 1)
      = v • (1 : CliffordAlgebra Q') ∧
    ι Q' (Pi.single 0 1) * ι Q' (Pi.single 1 1) + ι Q' (Pi.single 1 1) * ι Q' (Pi.single 0 1)
      = w • (1 : CliffordAlgebra Q') := by
  have sq : ∀ m, ι Q' m * ι Q' m = Q' m • (1 : CliffordAlgebra Q') := fun m => by
    rw [ι_sq_scalar, Algebra.algebraMap_eq_smul_one]
  have pol : ∀ m n, ι Q' m * ι Q' n + ι Q' n * ι Q' m
      = QuadraticMap.polar Q' m n • (1 : CliffordAlgebra Q') :=
    fun m n => by rw [ι_mul_ι_add_swap, Algebra.algebraMap_eq_smul_one]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sq, hQ]; simp
  · rw [sq, hQ]; simp
  · rw [sq, hQ]; simp
  · rw [pol, QuadraticMap.polar, hQ, hQ, hQ]; simp; congr 1; ring
  · rw [pol, QuadraticMap.polar, hQ, hQ, hQ]; simp; congr 1; ring
  · rw [pol, QuadraticMap.polar, hQ, hQ, hQ]; simp; congr 1; ring

theorem ι_mul_mem_even (m n : Fin 3 → R) : ι Q' m * ι Q' n ∈ CliffordAlgebra.even Q' := by
  rw [← Subalgebra.mem_toSubmodule, CliffordAlgebra.even_toSubmodule]
  exact ι_mul_ι_mem_evenOdd_zero Q' m n

/-- The algebra map `EvenClf → CliffordAlgebra Q'`, $i \mapsto \iota e_1 \iota e_2$,
$j \mapsto \iota e_2 \iota e_0$, $k \mapsto \iota e_0 \iota e_1$. -/
noncomputable def toCliff (hQ : IsTernaryFormula Q' a b c u v w) :
    EvenClf R a b c u v w →ₐ[R] CliffordAlgebra Q' :=
  toAlg (ι Q' (Pi.single 0 1)) (ι Q' (Pi.single 1 1)) (ι Q' (Pi.single 2 1))
    (clifford_relations hQ).1 (clifford_relations hQ).2.1 (clifford_relations hQ).2.2.1
    (clifford_relations hQ).2.2.2.1 (clifford_relations hQ).2.2.2.2.1
    (clifford_relations hQ).2.2.2.2.2

theorem toCliff_apply (hQ : IsTernaryFormula Q' a b c u v w) (x : EvenClf R a b c u v w) :
    toCliff hQ x = x.re • (1 : CliffordAlgebra Q')
      + x.i • (ι Q' (Pi.single 1 1) * ι Q' (Pi.single 2 1))
      + x.j • (ι Q' (Pi.single 2 1) * ι Q' (Pi.single 0 1))
      + x.k • (ι Q' (Pi.single 0 1) * ι Q' (Pi.single 1 1)) := rfl

/-- The algebra map `EvenClf → CliffordAlgebra.even Q'` (`toCliff`, landing in the even
subalgebra). -/
noncomputable def ofEvenClf (hQ : IsTernaryFormula Q' a b c u v w) :
    EvenClf R a b c u v w →ₐ[R] CliffordAlgebra.even Q' :=
  (toCliff hQ).codRestrict (CliffordAlgebra.even Q') (fun x => by
    rw [toCliff_apply]
    exact add_mem (add_mem (add_mem (Subalgebra.smul_mem _ (one_mem _) _)
      (Subalgebra.smul_mem _ (ι_mul_mem_even _ _) _))
      (Subalgebra.smul_mem _ (ι_mul_mem_even _ _) _))
      (Subalgebra.smul_mem _ (ι_mul_mem_even _ _) _))

/-- The bilinear map $(x, y) \mapsto \sum_{p,q} x_p y_q [e_p e_q]$ into `EvenClf`, where
$[e_pe_p] = (a, b, c)_p$, $[e_1e_2] = i$, $[e_2e_1] = u - i$, $[e_2e_0] = j$, $[e_0e_2] = v - j$,
$[e_0e_1] = k$, $[e_1e_0] = w - k$. -/
def bilinEvenClf (a b c u v w : R) :
    (Fin 3 → R) →ₗ[R] (Fin 3 → R) →ₗ[R] EvenClf R a b c u v w :=
  LinearMap.mk₂ R (fun x y => ⟨a * x 0 * y 0 + b * x 1 * y 1 + c * x 2 * y 2 + u * x 2 * y 1
      + v * x 0 * y 2 + w * x 1 * y 0, x 1 * y 2 - x 2 * y 1, x 2 * y 0 - x 0 * y 2,
      x 0 * y 1 - x 1 * y 0⟩)
    (fun x x' y => by ext <;> simp <;> ring)
    (fun r x y => by ext <;> simp <;> ring)
    (fun x y y' => by ext <;> simp <;> ring)
    (fun r x y => by ext <;> simp <;> ring)

/-- The `CliffordAlgebra.EvenHom` defining `toEvenClf`: `contract` and `contract_mid` are polynomial
identities. -/
def evenHomEvenClf (hQ : IsTernaryFormula Q' a b c u v w) :
    CliffordAlgebra.EvenHom Q' (EvenClf R a b c u v w) where
  bilin := bilinEvenClf a b c u v w
  contract m := by
    ext <;> simp only [bilinEvenClf, LinearMap.mk₂_apply, hQ m, algebraMap_re, algebraMap_i,
      algebraMap_j, algebraMap_k] <;> ring
  contract_mid m₁ m₂ m₃ := by
    ext <;> simp only [bilinEvenClf, LinearMap.mk₂_apply, mul_re, mul_i, mul_j, mul_k, smul_re,
      smul_i, smul_j, smul_k, smul_eq_mul, hQ m₂] <;> ring

/-- The algebra map `CliffordAlgebra.even Q' → EvenClf`, from `CliffordAlgebra.even.lift`. -/
noncomputable def toEvenClf (hQ : IsTernaryFormula Q' a b c u v w) :
    CliffordAlgebra.even Q' →ₐ[R] EvenClf R a b c u v w :=
  CliffordAlgebra.even.lift Q' (evenHomEvenClf hQ)

theorem toEvenClf_ι (hQ : IsTernaryFormula Q' a b c u v w) (m n : Fin 3 → R) :
    toEvenClf hQ ((CliffordAlgebra.even.ι Q').bilin m n) = bilinEvenClf a b c u v w m n :=
  CliffordAlgebra.even.lift_ι Q' (evenHomEvenClf hQ) m n

theorem coe_ofEvenClf (hQ : IsTernaryFormula Q' a b c u v w) (x : EvenClf R a b c u v w) :
    (ofEvenClf hQ x : CliffordAlgebra Q') = toCliff hQ x := rfl

theorem toEvenClf_ofEvenClf (hQ : IsTernaryFormula Q' a b c u v w) (x : EvenClf R a b c u v w) :
    toEvenClf hQ (ofEvenClf hQ x) = x := by
  have h1 : ofEvenClf hQ ei = (CliffordAlgebra.even.ι Q').bilin (Pi.single 1 1) (Pi.single 2 1) := by
    apply Subtype.ext
    rw [coe_ofEvenClf, toCliff_apply]
    simp [CliffordAlgebra.even.ι]
  have h2 : ofEvenClf hQ ej = (CliffordAlgebra.even.ι Q').bilin (Pi.single 2 1) (Pi.single 0 1) := by
    apply Subtype.ext
    rw [coe_ofEvenClf, toCliff_apply]
    simp [CliffordAlgebra.even.ι]
  have h3 : ofEvenClf hQ ek = (CliffordAlgebra.even.ι Q').bilin (Pi.single 0 1) (Pi.single 1 1) := by
    apply Subtype.ext
    rw [coe_ofEvenClf, toCliff_apply]
    simp [CliffordAlgebra.even.ι]
  conv_lhs => rw [eq_sum x]
  simp only [map_add, map_smul, AlgHom.commutes, h1, h2, h3, toEvenClf_ι]
  ext <;> simp [bilinEvenClf, Pi.single_apply]

theorem ofEvenClf_toEvenClf (hQ : IsTernaryFormula Q' a b c u v w) (x : CliffordAlgebra.even Q') :
    ofEvenClf hQ (toEvenClf hQ x) = x := by
  have key : (ofEvenClf hQ).comp (toEvenClf hQ) = AlgHom.id R _ := by
    apply CliffordAlgebra.even.algHom_ext
    apply CliffordAlgebra.EvenHom.ext
    ext p q
    show (ofEvenClf hQ (toEvenClf hQ ((CliffordAlgebra.even.ι Q').bilin (Pi.single p 1)
      (Pi.single q 1))) : CliffordAlgebra Q') = ι Q' (Pi.single p 1) * ι Q' (Pi.single q 1)
    rw [toEvenClf_ι, coe_ofEvenClf, toCliff_apply]
    obtain ⟨r0, r1, r2, r12, r02, r01⟩ := clifford_relations hQ
    have s10 := eq_sub_of_add_eq' r01
    have s20 := eq_sub_of_add_eq' r02
    have s21 := eq_sub_of_add_eq' r12
    fin_cases p <;> fin_cases q <;> simp [bilinEvenClf, -CliffordAlgebra.ι_sq_scalar]
    all_goals first
      | exact r0.symm
      | exact r1.symm
      | exact r2.symm
      | (rw [s10]; abel)
      | (rw [s20]; abel)
      | (rw [s21]; abel)
  exact DFunLike.congr_fun key x

/-- **The explicit table algebra is the even Clifford algebra**, for a Mathlib quadratic form `Q'`
on $R^3$ with the coordinate formula `IsTernaryFormula Q' a b c u v w`: over every commutative
ring $R$, `EvenClf R a b c u v w` $\cong$ `CliffordAlgebra.even Q'` as $R$-algebras. -/
noncomputable def equivEven (hQ : IsTernaryFormula Q' a b c u v w) :
    EvenClf R a b c u v w ≃ₐ[R] CliffordAlgebra.even Q' :=
  AlgEquiv.ofAlgHom (ofEvenClf hQ) (toEvenClf hQ)
    (AlgHom.ext (ofEvenClf_toEvenClf hQ)) (AlgHom.ext (toEvenClf_ofEvenClf hQ))

@[simp] theorem coe_equivEven_ei (hQ : IsTernaryFormula Q' a b c u v w) :
    (equivEven hQ (ei : EvenClf R a b c u v w) : CliffordAlgebra Q') =
      ι Q' (Pi.single 1 1) * ι Q' (Pi.single 2 1) := by
  show toCliff hQ _ = _
  simp [toCliff_apply]

@[simp] theorem coe_equivEven_ej (hQ : IsTernaryFormula Q' a b c u v w) :
    (equivEven hQ (ej : EvenClf R a b c u v w) : CliffordAlgebra Q') =
      ι Q' (Pi.single 2 1) * ι Q' (Pi.single 0 1) := by
  show toCliff hQ _ = _
  simp [toCliff_apply]

@[simp] theorem coe_equivEven_ek (hQ : IsTernaryFormula Q' a b c u v w) :
    (equivEven hQ (ek : EvenClf R a b c u v w) : CliffordAlgebra Q') =
      ι Q' (Pi.single 0 1) * ι Q' (Pi.single 1 1) := by
  show toCliff hQ _ = _
  simp [toCliff_apply]

end Mathlib

end EvenClf

/-! ## The identification for a `QuadForm R 3` -/

section Final

variable {R : Type*} [CommRing R]

/-- The Mathlib form attached to `Q : QuadForm R 3` has Voight's coordinate formula, with
$a = c_{00}$, $b = c_{11}$, $c = c_{22}$, $u = c_{12}$, $v = c_{02}$, $w = c_{01}$. -/
theorem isTernaryFormula_toQuadraticForm (Q : QuadForm R 3) :
    EvenClf.IsTernaryFormula Q.toQuadraticForm (Q.coeff 0 0) (Q.coeff 1 1) (Q.coeff 2 2)
      (Q.coeff 1 2) (Q.coeff 0 2) (Q.coeff 0 1) := fun x => by
  rw [QuadForm.toQuadraticForm_apply, eval_ternary]

/-- **$\operatorname{Clf}^0(Q)$ is Mathlib's even Clifford algebra** (Voight 2021, 22.3.4 and
Example 22.2.5; see also 22.2.9). For a ternary form $Q$ over any commutative ring $R$, the algebra
`Clf0 Q` given by Voight's explicit multiplication table
($i^2 = ui - bc$, $jk = a\bar i$, etc.; basis $1, i, j, k$) is isomorphic, as an $R$-algebra, to
`CliffordAlgebra.even (QuadForm.toQuadraticForm Q)`, the even subalgebra of Mathlib's Clifford
algebra of $Q$. The isomorphism sends $i \mapsto \iota(e_1)\iota(e_2)$,
$j \mapsto \iota(e_2)\iota(e_0)$, $k \mapsto \iota(e_0)\iota(e_1)$ (`coe_clf0EquivEven_ei`, `_ej`,
`_ek`). Consequently $\operatorname{Clf}^0(Q)$ is a free $R$-module with basis $1, i, j, k$
(`EvenClf.basisOneIJK`), Voight 22.2.9 / 22.3.4. No hypothesis on $R$ (any characteristic).

Indices are 0-based: Voight's $e_1, e_2, e_3$ are $e_0, e_1, e_2$ here. -/
@[kb "voight2021" "22.3.4, p. 360; Example 22.2.5, p. 356"]
noncomputable def clf0EquivEven (Q : QuadForm R 3) :
    Clf0 Q ≃ₐ[R] CliffordAlgebra.even (QuadForm.toQuadraticForm Q) :=
  EvenClf.equivEven (isTernaryFormula_toQuadraticForm Q)

/-- `clf0EquivEven` sends $i$ to $\iota(e_1)\iota(e_2)$. -/
@[simp] theorem coe_clf0EquivEven_ei (Q : QuadForm R 3) :
    (clf0EquivEven Q EvenClf.ei : CliffordAlgebra (QuadForm.toQuadraticForm Q)) =
      CliffordAlgebra.ι _ (Pi.single 1 1) * CliffordAlgebra.ι _ (Pi.single 2 1) :=
  EvenClf.coe_equivEven_ei _

/-- `clf0EquivEven` sends $j$ to $\iota(e_2)\iota(e_0)$. -/
@[simp] theorem coe_clf0EquivEven_ej (Q : QuadForm R 3) :
    (clf0EquivEven Q EvenClf.ej : CliffordAlgebra (QuadForm.toQuadraticForm Q)) =
      CliffordAlgebra.ι _ (Pi.single 2 1) * CliffordAlgebra.ι _ (Pi.single 0 1) :=
  EvenClf.coe_equivEven_ej _

/-- `clf0EquivEven` sends $k$ to $\iota(e_0)\iota(e_1)$. -/
@[simp] theorem coe_clf0EquivEven_ek (Q : QuadForm R 3) :
    (clf0EquivEven Q EvenClf.ek : CliffordAlgebra (QuadForm.toQuadraticForm Q)) =
      CliffordAlgebra.ι _ (Pi.single 0 1) * CliffordAlgebra.ι _ (Pi.single 1 1) :=
  EvenClf.coe_equivEven_ek _

end Final

end QuadFormsKB.Voight
