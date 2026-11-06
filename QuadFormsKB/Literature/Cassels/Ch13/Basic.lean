/-
# Cassels, Chapter 13: the real matrix of a form

Shared notation for the formalization of Cassels, *Rational Quadratic Forms* (1978), Chapter 13, *Automorphs of
integral forms*. As in Chapter 12 (`Literature/Cassels/Ch12/Basic.lean`) a real form is given by its symmetric matrix
$F$; for a form $Q$ with integral or rational coefficients this matrix is `realMat Q` $= \tfrac12 H$, $H$ the Hessian.
-/
import QuadFormsKB.Literature.Cassels.Ch12.Bridge
import QuadFormsKB.Literature.Cassels.Ch12.Sec3
import QuadFormsKB.Literature.Cassels.Ch9Sec1

open Matrix

namespace QuadFormsKB.Reduction

variable {n : ℕ}

/-- **The real matrix $F = \tfrac12 H$ of a form** over a commutative ring $R$ with $R \to \mathbb{R}$ (for $R = \mathbb{Z}$ or
$\mathbb{Q}$): $Q(\vec{x}) = \vec{x}^{\mathsf T}F\vec{x}$ for real $\vec{x}$ (`QuadForm.evalIn_real_eq_val`), $F$ symmetric,
$f_{ii} = c_{ii}$ and $f_{ij} = c_{ij}/2$ ($i < j$). Cassels' $F = (f_{ij})$ (Ch. 1, (2.7), p. 6). -/
noncomputable abbrev realMat {R : Type*} [CommRing R] [Algebra R ℝ] (Q : QuadForm R n) :
    Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • Q.hessian.map (algebraMap R ℝ)

/-! ### Real automorphs -/

/-- **The group $O_{\mathbb{R}}(f)$ of real automorphs** of the real form with matrix $F$: the $S \in \mathrm{GL}_n(\mathbb{R})$
with $f(S\vec{x}) = f(\vec{x})$, i.e. $S^{\mathsf T}FS = F$ (Cassels, Ch. 13, §1, p. 284: "the group $O_{\mathbb{R}}(f)$ of
real automorphs"). For the form of an integral `QuadForm` over $\mathbb{R}$ this is `Siegel.aut` of the base change;
the matrix description is used here as in Chapter 12. The variables are indexed by a finite type $\iota$ (usually
`Fin n`; §10 uses `Fin m ⊕ Fin l`). -/
@[kb "cassels1978" "Ch. 13, §1, p. 284 (the group O_ℝ(f) of real automorphs)"]
def realAut {ι : Type*} [Fintype ι] [DecidableEq ι] (F : Matrix ι ι ℝ) : Subgroup (GL ι ℝ) where
  carrier := {S | S.valᵀ * F * S.val = F}
  mul_mem' := by
    intro S T hS hT
    simp only [Set.mem_ofPred_eq, Units.val_mul, Matrix.transpose_mul] at *
    calc T.valᵀ * S.valᵀ * F * (S.val * T.val) = T.valᵀ * (S.valᵀ * F * S.val) * T.val := by
          simp only [Matrix.mul_assoc]
      _ = F := by rw [hS, hT]
  one_mem' := by simp
  inv_mem' := by
    intro S hS
    simp only [Set.mem_ofPred_eq] at *
    have h1 : (S⁻¹).valᵀ * S.valᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
    have h2 : S.val * (S⁻¹).val = 1 := Units.mul_inv S
    calc (S⁻¹).valᵀ * F * (S⁻¹).val = (S⁻¹).valᵀ * (S.valᵀ * F * S.val) * (S⁻¹).val := by rw [hS]
      _ = ((S⁻¹).valᵀ * S.valᵀ) * F * (S.val * (S⁻¹).val) := by simp only [Matrix.mul_assoc]
      _ = F := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

/-- **The proper real automorphs** $O^+_{\mathbb{R}}(f)$: the real automorphs of determinant $1$. -/
def realAutPlus {ι : Type*} [Fintype ι] [DecidableEq ι] (F : Matrix ι ι ℝ) : Subgroup (GL ι ℝ) :=
  realAut F ⊓ (Matrix.GeneralLinearGroup.det).ker

end QuadFormsKB.Reduction
