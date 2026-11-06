import QuadFormsKB.Literature.Hanke2005.Cor52Field
import QuadFormsKB.Defs.QuadForm

/-!
# The ternary form of the counterexample to Hanke's Corollary 5.2(ii): algebra and real places

Over $k=\mathbb Q(\alpha)$ (`Cor52.K`): $s=\alpha+2$ and $1+\alpha$ are units, and $d=-s$.
The quadratic space is $V=\langle1,1,s\rangle$ ($Q=x^2+y^2+sz^2$). The lattice $\mathcal O_k^3$ with this form is
**not** $\mathcal O_k$-maximal (at $2$); a maximal lattice is $M=\mathcal O_k^3+\mathcal O_k\cdot\frac12(0,\alpha^2,1+\alpha)$,
with basis $e_0,\ e_1,\ w=\frac12(\alpha^2e_1+(1+\alpha)e_2)$, on which
$$Q_0'(x,y,z)=x^2+y^2+\alpha^2yz+4(\alpha+1)^2z^2,\qquad 4Q_0'=4x^2+(2y+\alpha^2z)^2+s(1+\alpha)^2z^2 .$$
This file: the form `Q₀` over $\mathcal O_k$, the identities, the Hessian determinant $2\cdot s(1+\alpha)^2$, and the
signs at real embeddings.
-/

open Polynomial NumberField

noncomputable section

namespace QuadFormsKB.Hanke2005.Cor52

open QuadFormsKB

theorem isIntegral_α : IsIntegral ℤ α := by
  refine ⟨polyZ, ?_, ?_⟩
  · exact polyZ_monic
  · have := α_cube
    simp only [polyZ, eval₂_sub, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C]
    simp
    linear_combination this

/-- $\alpha$ as an algebraic integer. -/
def αI : 𝓞 K := ⟨α, isIntegral_α⟩

@[simp] theorem coe_αI : ((αI : 𝓞 K) : K) = α := rfl

/-- The inverse of $s=\alpha+2$ is $4+3\alpha-\alpha^2$. -/
theorem s_mul_inv : (α + 2) * (4 + 3 * α - α ^ 2) = 1 := by
  have := α_cube
  linear_combination (-1 : K) * this

/-- $(1+\alpha)(8+2\alpha-\alpha^2)=1$. -/
theorem a1_mul_inv : (1 + α) * (8 + 2 * α - α ^ 2) = 1 := by
  have := α_cube
  linear_combination (-1 : K) * this

/-- The key identity $4\cdot4(\alpha+1)^2-(\alpha^2)^2=s\,(1+\alpha)^2$. -/
theorem key_identity : 4 * (4 * (α + 1) ^ 2) - (α ^ 2) ^ 2 = (α + 2) * (1 + α) ^ 2 := by
  have := α_cube
  have h4 : α ^ 4 = 11 * α ^ 2 + 17 * α + 7 := by
    linear_combination (α + 1) * this
  linear_combination (-1 : K) * h4 + (-1 : K) * this

/-- **The form $Q_0'$ over $\mathcal O_k$:** $Q_0'(x_0,x_1,x_2)=x_0^2+x_1^2+\alpha^2x_1x_2+4(\alpha+1)^2x_2^2$
(0-based variables). -/
def Q₀ : QuadForm (𝓞 K) 3 :=
  QuadForm.ofUpper ![![1, 0, 0], ![0, 1, αI ^ 2], ![0, 0, 4 * (αI + 1) ^ 2]]

/-- The form over $k$. -/
abbrev QF : QuadForm K 3 := Q₀.map (algebraMap (𝓞 K) K)

/-- **Value of the form** over any $k$-algebra $L$. -/
theorem evalIn_QF (L : Type*) [CommRing L] [Algebra K L] (x : Fin 3 → L) :
    QF.evalIn L x = x 0 ^ 2 + x 1 ^ 2 + algebraMap K L (α ^ 2) * x 1 * x 2 +
      algebraMap K L (4 * (α + 1) ^ 2) * x 2 ^ 2 := by
  simp [QuadForm.evalIn, Fin.sum_univ_three, QuadForm.map, Q₀, QuadForm.ofUpper]
  simp only [map_ofNat]
  ring

/-- $s=\alpha+2$ as an algebraic integer; a unit. -/
def sI : 𝓞 K := αI + 2

/-- $1+\alpha$ as an algebraic integer. -/
def tI : 𝓞 K := 1 + αI

theorem isUnit_sI : IsUnit sI :=
  IsUnit.of_mul_eq_one (4 + 3 * αI - αI ^ 2) (Subtype.ext (by push_cast [sI, αI]; exact s_mul_inv))

theorem isUnit_tI : IsUnit tI :=
  IsUnit.of_mul_eq_one (8 + 2 * αI - αI ^ 2) (Subtype.ext (by push_cast [tI, αI]; exact a1_mul_inv))

/-- **The determinant of the Hessian is $2\,s\,(1+\alpha)^2$** (a unit times $2$): for odd rank the smallest
possible, which makes the standard lattice maximal. -/
theorem hessian_det : Q₀.hessian.det = 2 * (sI * tI ^ 2) := by
  have h := key_identity
  have hα : algebraMap (𝓞 K) K αI = α := rfl
  simp only [Matrix.det_fin_three, QuadForm.hessian, Q₀, QuadForm.ofUpper]
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  have h4 : algebraMap (𝓞 K) K 4 = 4 := map_ofNat _ 4
  have h2 : algebraMap (𝓞 K) K 2 = 2 := map_ofNat _ 2
  simp [sI, tI, hα, h4, h2]
  linear_combination 2 * h

end QuadFormsKB.Hanke2005.Cor52
