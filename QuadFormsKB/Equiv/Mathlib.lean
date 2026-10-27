/-
# Converting between our `QuadForm R n` and Mathlib's `QuadraticForm R (Fin n → R)`

**Two definitions of the same objects.**

* *Ours* (`Defs/QuadForm.lean`): a quadratic form in $n$ variables over a commutative ring $R$
  is the polynomial $Q(\vec{x}) = \sum_{0 \le i \le j < n} c_{ij}\, x_i x_j$, stored as its
  upper-triangular coefficient matrix $C$.
* *Mathlib's* (`Mathlib.LinearAlgebra.QuadraticForm.Basic`): a `QuadraticForm R M` is a
  function $Q' : M \to R$ with $Q'(a \vec{x}) = a^2 Q'(\vec{x})$ whose polar form
  $B(\vec{x}, \vec{y}) = Q'(\vec{x} + \vec{y}) - Q'(\vec{x}) - Q'(\vec{y})$ is bilinear. It is
  coordinate-free; here $M = R^n$ (`Fin n → R`).

**The conversions** (this file):

* `toQuadraticForm` (ours $\to$ Mathlib): $Q \mapsto \big(\vec{x} \mapsto \vec{x}^{\mathsf T} C \vec{x}\big)$;
* `ofQuadraticForm` (Mathlib $\to$ ours): $Q' \mapsto$ the polynomial with $c_{ii} = Q'(\vec{e}_i)$
  and $c_{ij} = B(\vec{e}_i, \vec{e}_j)$ for $i < j$,

where $\vec{e}_i$ is the $i$-th standard basis vector (`Pi.single i 1`).

**What is proved.** They are mutually inverse (`ofQuadraticForm_toQuadraticForm`,
`toQuadraticForm_ofQuadraticForm`) and preserve values (`toQuadraticForm_apply`,
`eval_ofQuadraticForm`). So the two definitions are equivalent **for every commutative ring
`R`**, including `ℤ` and characteristic 2: neither direction divides by 2.

**When to use which.** State literature results with ours (explicit coefficients, no
factors of 2). Convert to Mathlib's to use its library: isometries, base change,
`Anisotropic`, Sylvester's law, and so on.
-/
import QuadFormsKB.Defs.QuadForm

open Matrix

namespace QuadFormsKB.QuadForm

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **Conversion from our definition to Mathlib's.** Sends the polynomial
$Q(\vec{x}) = \sum_{i \le j} c_{ij}\, x_i x_j$ to the Mathlib `QuadraticForm`
$\vec{x} \mapsto \vec{x}^{\mathsf T} C \vec{x}$ on $R^n$.

Construction: `Matrix.toLinearMap₂' R C` is the bilinear map
$(\vec{x}, \vec{y}) \mapsto \vec{x}^{\mathsf T} C \vec{y}$ (not symmetric, since $C$ is upper
triangular), and `LinearMap.BilinMap.toQuadraticMap` takes its diagonal
$\vec{x} \mapsto \vec{x}^{\mathsf T} C \vec{x}$, which is exactly $Q(\vec{x})$.

See also: `toQuadraticForm_apply` (values agree) and `ofQuadraticForm_toQuadraticForm`
(converting back recovers `Q`). -/
def toQuadraticForm (Q : QuadForm R n) : QuadraticForm R (Fin n → R) :=
  LinearMap.BilinMap.toQuadraticMap (Matrix.toLinearMap₂' R Q.coeff)

/-- **Conversion from Mathlib's definition to ours.** Reads off the coefficients of a Mathlib
`QuadraticForm` on `Rⁿ` from its values on the standard basis vectors $\vec{e}_i$ (`Pi.single i 1`):
$$c_{ii} = Q'(\vec{e}_i), \qquad c_{ij} = B(\vec{e}_i, \vec{e}_j) =
Q'(\vec{e}_i + \vec{e}_j) - Q'(\vec{e}_i) - Q'(\vec{e}_j) \quad (i < j),$$
and $0$ below the diagonal. No division by 2, so it works over any commutative ring.

See also: `eval_ofQuadraticForm` (values agree) and `toQuadraticForm_ofQuadraticForm`
(converting back recovers `Q'`). -/
def ofQuadraticForm (Q' : QuadraticForm R (Fin n → R)) : QuadForm R n :=
  ofUpper fun i j =>
    if i = j then Q' (Pi.single i 1) else QuadraticMap.polar Q' (Pi.single i 1) (Pi.single j 1)

/-- **The conversion ours $\to$ Mathlib preserves values:**
$(\texttt{toQuadraticForm}\ Q)(\vec{x}) = Q(\vec{x})$ for all $\vec{x} \in R^n$. -/
@[kb "omeara1963" "§41"]
theorem toQuadraticForm_apply (Q : QuadForm R n) (x : Fin n → R) :
    Q.toQuadraticForm x = Q.eval x := by
  rw [eval, evalIn_eq_dotProduct]
  simp [toQuadraticForm, Matrix.toLinearMap₂'_apply', dotProduct, mulVec,
    Finset.mul_sum, mul_comm]

/-- **The conversion Mathlib $\to$ ours preserves values:**
$(\texttt{ofQuadraticForm}\ Q')(\vec{x}) = Q'(\vec{x})$ for all $\vec{x} \in R^n$. -/
@[kb "omeara1963" "§41"]
theorem eval_ofQuadraticForm (Q' : QuadraticForm R (Fin n → R)) (x : Fin n → R) :
    (ofQuadraticForm Q').eval x = Q' x := by
  conv_rhs => rw [← QuadraticMap.toQuadraticMap_toBilin Q' (Pi.basisFun R (Fin n))]
  rw [LinearMap.BilinMap.toQuadraticMap_apply]
  have hx : x = ∑ i, x i • Pi.single i (1:R) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  rw [hx]
  have h := QuadraticMap.toBilin_apply Q' (Pi.basisFun R (Fin n))
  simp only [Pi.basisFun_apply] at h
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, h, eval, evalIn,
    ofQuadraticForm, ofUpper, Matrix.of_apply, smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> first | (exfalso; order) | ring1

/-- Round trip ours → Mathlib → ours is the identity: `ofQuadraticForm (toQuadraticForm Q) = Q`.
(Together with `toQuadraticForm_ofQuadraticForm`: the two definitions correspond
one-to-one.) -/
@[kb "omeara1963" "§41"]
theorem ofQuadraticForm_toQuadraticForm (Q : QuadForm R n) :
    ofQuadraticForm Q.toQuadraticForm = Q := by
  obtain ⟨c, hc⟩ := Q
  simp only [ofQuadraticForm, ofUpper, QuadForm.mk.injEq]
  ext i j
  simp only [of_apply, toQuadraticForm]
  split_ifs with h1 h2
  · subst h2
    simp [LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']
  · simp [QuadraticMap.polar, LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']
    have : c j i = 0 := hc (lt_of_le_of_ne h1 h2)
    simp only [Matrix.mulVec_add, Pi.add_apply, Matrix.mulVec_single_one]
    simp [Matrix.col_apply, this]
    ring
  · exact (hc (lt_of_not_ge h1)).symm

/-- Round trip Mathlib → ours → Mathlib is the identity:
`toQuadraticForm (ofQuadraticForm Q') = Q'`. -/
@[kb "omeara1963" "§41"]
theorem toQuadraticForm_ofQuadraticForm (Q' : QuadraticForm R (Fin n → R)) :
    (ofQuadraticForm Q').toQuadraticForm = Q' := by
  conv_rhs => rw [← QuadraticMap.toQuadraticMap_toBilin Q' (Pi.basisFun R (Fin n))]
  unfold toQuadraticForm
  congr 1
  refine LinearMap.ext_basis (Pi.basisFun R (Fin n)) (Pi.basisFun R (Fin n)) fun i j => ?_
  rw [QuadraticMap.toBilin_apply]
  simp only [Pi.basisFun_apply, ofQuadraticForm, ofUpper, Matrix.toLinearMap₂'_apply']
  simp
  split_ifs with h1 h2 h3 <;> try first | rfl | (exfalso; omega)

end QuadFormsKB.QuadForm
