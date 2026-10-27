/-
# Cassels, Chapter 12: bridge to the library's quadratic forms and integral forms

The formalization of Chapter 12 describes a real form by its symmetric matrix $F$ (`val`, `Basic.lean`). This file
relates it to the library's primary definition `QuadForm` (upper-triangular coefficients $c_{ij}$): over $\mathbb{R}$ the
form $Q$ has matrix $F = \tfrac12 H$, $H = C + C^{\mathsf T}$ the Hessian (`QuadForm.evalIn_real_eq_val`), substitution
$Q \circ T$ (`QuadForm.compMat`) corresponds to $T^{\mathsf T}FT$ (`halfHessian_compMat`), and a positive definite
integral form (`IntQF.PosDef`) has a strictly positive definite matrix (`IntQF.PosDef.posDef_halfHessian`).

Consequence (Theorem 1.1 for integral forms): every positive definite integral form is integrally equivalent
(`Siegel.IntEquiv`) to one whose matrix is Minkowski-reduced, and to only finitely many such forms.
-/
import QuadFormsKB.Literature.Cassels.Ch12.Sec1
import QuadFormsKB.LocalDensity.FormDensity
import QuadFormsKB.LocalDensity.FormDensitySelf
import QuadFormsKB.Siegel.Genus

open Matrix

namespace QuadFormsKB.Reduction

variable {n : ℕ}

/-- **The matrix of a form over $\mathbb{R}$**: for a form $Q$ over a commutative ring $R$ with an algebra map
$R \to \mathbb{R}$, $Q(\vec{x}) = \vec{x}^{\mathsf T}F\vec{x}$ for real $\vec{x}$, with $F = \tfrac12 H$ the halved Hessian
(Cassels' $F = (f_{ij})$, $f_{ii} = c_{ii}$, $f_{ij} = c_{ij}/2$ for $i < j$). -/
theorem _root_.QuadFormsKB.QuadForm.evalIn_real_eq_val {R : Type*} [CommRing R] [Algebra R ℝ] (Q : QuadForm R n)
    (x : Fin n → ℝ) : Q.evalIn ℝ x = val ((1 / 2 : ℝ) • Q.hessian.map (algebraMap R ℝ)) x := by
  rw [QuadForm.evalIn_eq_dotProduct]
  have h : x ⬝ᵥ ((Q.coeff.map (algebraMap R ℝ))ᵀ *ᵥ x) = x ⬝ᵥ (Q.coeff.map (algebraMap R ℝ) *ᵥ x) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  unfold val
  rw [QuadForm.hessian, Matrix.map_add _ (map_add _), Matrix.transpose_map]
  simp only [Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_smul, h, smul_eq_mul]
  ring

/-- **Substitution:** the halved Hessian of $Q \circ T$ ($T \in M_n(\mathbb{Z})$, `QuadForm.compMat`) is
$T^{\mathsf T}FT$ (`act`), $F$ the halved Hessian of $Q$. -/
theorem halfHessian_compMat (Q : QuadForm ℤ n) (T : Matrix (Fin n) (Fin n) ℤ) :
    (1 / 2 : ℝ) • (Q.compMat T).hessian.map (algebraMap ℤ ℝ) =
      act T ((1 / 2 : ℝ) • Q.hessian.map (algebraMap ℤ ℝ)) := by
  rw [QuadForm.hessian_compMat]
  unfold act castM
  simp only [Matrix.map_mul, ← Matrix.transpose_map, Matrix.mul_smul, Matrix.smul_mul]
  rfl

/-- **A positive definite integral form has a strictly positive definite matrix** (`IntQF.PosDef` is positivity on
$\mathbb{Z}^n \setminus 0$; with `IntQF.PosDef.evalIn_real_pos` it is positivity on $\mathbb{R}^n \setminus 0$). -/
theorem _root_.QuadFormsKB.IntQF.PosDef.posDef_halfHessian {Q : IntQF n} (hQ : Q.PosDef) :
    ((1 / 2 : ℝ) • Q.hessian.map (algebraMap ℤ ℝ)).PosDef := by
  rw [posDef_iff]
  refine ⟨?_, fun x hx => ?_⟩
  · have hs : Q.hessian.transpose = Q.hessian := by
      simp [QuadForm.hessian, Matrix.transpose_add, add_comm]
    show ((1 / 2 : ℝ) • Q.hessian.map (algebraMap ℤ ℝ))ᵀ = _
    rw [Matrix.transpose_smul, ← Matrix.transpose_map, hs]
  · rw [← QuadForm.evalIn_real_eq_val]
    exact hQ.evalIn_real_pos x hx

/-- **Theorem 1.1 for integral forms, existence** (Cassels, Ch. 12, Thm. 1.1, p. 256): every positive definite integral
form $Q$ is integrally equivalent ($\mathrm{GL}_n(\mathbb{Z})$, `Siegel.IntEquiv`) to an integral form $Q'$ whose matrix
$\tfrac12 H_{Q'}$ is Minkowski-reduced. -/
@[kb "cassels1978" "Ch. 12, §1, Thm. 1.1, p. 256 (existence, for integral forms)"]
theorem exists_intEquiv_isMinkowskiReduced {Q : IntQF n} (hQ : Q.PosDef) :
    ∃ Q' : IntQF n, Siegel.IntEquiv Q Q' ∧
      IsMinkowskiReduced ((1 / 2 : ℝ) • Q'.hessian.map (algebraMap ℤ ℝ)) := by
  have hF := hQ.posDef_halfHessian
  obtain ⟨T, hT⟩ := exists_isMinkowskiReduced hF
  refine ⟨Q.compMat T.val, ⟨T, fun x => (QuadForm.eval_compMat Q T.val x).symm⟩, ?_⟩
  rw [halfHessian_compMat]
  exact hT

/-- **Theorem 1.1 for integral forms, finiteness** (Cassels, Ch. 12, Thm. 1.1, p. 256): a positive definite integral
form is integrally equivalent to only finitely many integral forms with Minkowski-reduced matrix. -/
@[kb "cassels1978" "Ch. 12, §1, Thm. 1.1, p. 256 (finiteness, for integral forms)"]
theorem finite_intEquiv_isMinkowskiReduced {Q : IntQF n} (hQ : Q.PosDef) :
    {Q' : IntQF n | Siegel.IntEquiv Q Q' ∧
      IsMinkowskiReduced ((1 / 2 : ℝ) • Q'.hessian.map (algebraMap ℤ ℝ))}.Finite := by
  have hF := hQ.posDef_halfHessian
  refine ((finite_gl_isMinkowskiReduced hF).image (fun T : GL (Fin n) ℤ => Q.compMat T.val)).subset ?_
  rintro Q' ⟨⟨g, hg⟩, hred⟩
  have e : Q.compMat g.val = Q' :=
    QuadForm.eq_of_eval_eq fun y => by rw [QuadForm.eval_compMat, hg]
  refine ⟨g, ?_, e⟩
  have := halfHessian_compMat Q g.val
  rw [e] at this
  show IsMinkowskiReduced (act g.val _)
  rw [← this]
  exact hred

end QuadFormsKB.Reduction
