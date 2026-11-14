/-
# Shimura 2004, §15.14: formulas (15.16) and (15.17) for the twisted matrix model

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Chapter IV, §15.14
(printed p. 153), formulas (15.16), (15.17). Page numbers in the tags are printed pages.

**Setting and dictionary.** As in `Wave4/Xi.lean`: $F$ a field of characteristic $\ne 2$, $V = U + Fe + Ff$ with
`Q e = 0`, `Q f = 0`, `QuadraticMap.polar Q e f = 1`, $A(U)$ = `AU Q e f`, a fixed $g \in U$ with
$\varphi[g] \ne 0$ (`g : uSpace Q e f`, `hg : Q (g : V) ≠ 0`), $\varepsilon = g$, and
$\Xi$ = `xi`. The canonical involution $a \mapsto a^*$ of $A(U)$ is `reverse`; $J$ = `matJ`.

**Defines**
* $a^\sigma = \varepsilon^{-1}a^*\varepsilon$ for $a \in A(U)$ (`sigmaU`);
* for $X$ with rows $(a, b)$ and $(c, d)$ over $A(U)$, ${}^tX^\sigma$ = the matrix with rows $(a^\sigma, c^\sigma)$
  and $(b^\sigma, d^\sigma)$ (`matStarSigma`).

**Proves** (all unconditional; standard axioms only)
* (15.16) $\Xi(\alpha^*) = J\,{}^t\Xi(\alpha')^\sigma J^{-1}$ for every $\alpha \in A(V)$, with $J^{-1} = -J$
  (`formula_15_16`);
* (15.17) for $\alpha \in G^+(V)$ and nondegenerate $\varphi$: $\Xi(\alpha)\,J\,{}^t\Xi(\alpha)^\sigma = \nu(\alpha)J$
  (`formula_15_17`), all entries of $\Xi(\alpha)$ lie in $A^+(U)$ (`formula_15_17_mem`), and $\Xi(\alpha)$ is
  invertible (`formula_15_17_isUnit`).
-/
import QuadFormsKB.Literature.Shimura2004.Wave4.Xi
import QuadFormsKB.Literature.Shimura2004.CliffordGroups
import QuadFormsKB.Citation

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Cassels QuadFormsKB.OMeara

namespace MatrixModel

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V} {e f : V}

/-- **$a^\sigma$** (§15.14, p. 153): for $a \in A(U)$ and $\varepsilon = g \in U$, $a^\sigma = \varepsilon^{-1}a^*\varepsilon$,
with $\varepsilon^{-1}$ = `ginv g` and $\varepsilon$ meaning $\iota(g) \in A(U)$. -/
def sigmaU (g : uSpace Q e f) (a : AU Q e f) : AU Q e f :=
  ginv g * reverse a * ι (QU Q e f) g

/-- **${}^tX^\sigma$** (§15.14, p. 153): for $X$ with rows $(a, b)$ and $(c, d)$ over $A(U)$, the matrix with rows
$(a^\sigma, c^\sigma)$ and $(b^\sigma, d^\sigma)$ (transpose, then `sigmaU` on every entry). -/
def matStarSigma (g : uSpace Q e f) (X : Matrix (Fin 2) (Fin 2) (AU Q e f)) :
    Matrix (Fin 2) (Fin 2) (AU Q e f) :=
  !![sigmaU g (X 0 0), sigmaU g (X 1 0); sigmaU g (X 0 1), sigmaU g (X 1 1)]

theorem matJ_mul_neg_matJ_apply {R : Type*} [Ring R] (Z : Matrix (Fin 2) (Fin 2) R) :
    matJ * Z * -matJ = !![Z 1 1, -Z 1 0; -Z 0 1, Z 0 0] := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply, matJ]
  fin_cases i <;> fin_cases j <;> simp

section Hyp

variable (he : Q e = 0) (hf : Q f = 0) (hef : QuadraticMap.polar Q e f = 1)
variable {g : uSpace Q e f}

theorem reverse_ι_AU (u : uSpace Q e f) : reverse (ι (QU Q e f) u) = ι (QU Q e f) u := reverse_ι _

theorem reverse_ginv : reverse (ginv (Q := Q) (e := e) (f := f) g) = ginv g := by
  rw [ginv, reverse.map_mul, reverse.commutes, reverse_ι_AU, Algebra.commutes]

include he hf hef

/-- **(15.16)**, p. 153: $\Xi(\alpha^*) = J\,{}^t\Xi(\alpha')^\sigma J^{-1}$ for every $\alpha \in A(V)$, with
$J^{-1} = -J$ and $\sigma$ built from $\varepsilon = g$. -/
@[kb "shimura2004" "(15.16), p. 153 (Ξ(α*) = J · ᵗΞ(α')^σ · J⁻¹)"]
theorem formula_15_16 (hg : Q (g : V) ≠ 0) (α : CliffordAlgebra Q) :
    xi he hf hef hg (reverse α) =
      matJ * matStarSigma g (xi he hf hef hg (involute α)) * -matJ := by
  set X := xi he hf hef hg (involute α) with hX
  have h11 : psi he hf hef (involute α) 1 1 = X 1 1 := (xi_apply_one_one he hf hef hg _).symm
  have h01 : psi he hf hef (involute α) 0 1 = ι (QU Q e f) g * X 0 1 := by
    rw [hX, xi_apply_zero_one, ← mul_assoc, mul_ginv hg, one_mul]
  have h10 : psi he hf hef (involute α) 1 0 = X 1 0 * ginv g := by
    rw [hX, xi_apply_one_zero, mul_assoc, mul_ginv hg, mul_one]
  have h00 : psi he hf hef (involute α) 0 0 = ι (QU Q e f) g * X 0 0 * ginv g := by
    rw [hX, xi_apply_zero_zero]
    simp only [mul_assoc, mul_ginv hg, mul_one]
    rw [← mul_assoc, mul_ginv hg, one_mul]
  have hgg := ginv_mul (Q := Q) (e := e) (f := f) (g := g) hg
  have hgg' := mul_ginv (Q := Q) (e := e) (f := f) (g := g) hg
  rw [xi_apply, psi_reverse, matJ_matStar_neg_matJ, matJ_mul_neg_matJ_apply, h00, h01, h10, h11]
  simp only [deltaInv, delta, matStarSigma, sigmaU]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, reverse.map_mul, reverse_ginv, mul_assoc]

variable (hQ : (QuadraticMap.associated Q).Nondegenerate)

/-- **(15.17)**, p. 153, the identity: for $\alpha \in G^+(V)$ and nondegenerate $\varphi$,
$\Xi(\alpha)\,J\,{}^t\Xi(\alpha)^\sigma = \nu(\alpha)J$, where $\nu(\alpha) = \alpha\alpha^*$ is the multiplier
(`multiplier`), viewed in $F$ and acting by scalar multiplication. -/
@[kb "shimura2004" "(15.17), p. 153 (Ξ(G⁺(V)) ⊆ {ξ : ξJᵗξ^σ = μ_ξ J}, μ_ξ = ν(α))"]
theorem formula_15_17 (hg : Q (g : V) ≠ 0) (a : M0 Q) :
    xi he hf hef hg ((a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * matJ *
        matStarSigma g (xi he hf hef hg ((a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) =
      (multiplier hQ ⟨a, M0_le_homogeneous a.2⟩ : F) • (matJ : Matrix (Fin 2) (Fin 2) (AU Q e f)) := by
  have hev : ((a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ evenOdd Q 0 := a.2.1
  have h1 := formula_15_16 he hf hef hg ((a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
  rw [involute_eq_of_mem_even hev] at h1
  have h2 : xi he hf hef hg ((a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
      (matJ * matStarSigma g (xi he hf hef hg ((a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) * -matJ) =
      algebraMap F (Matrix (Fin 2) (Fin 2) (AU Q e f)) (multiplier hQ ⟨a, M0_le_homogeneous a.2⟩ : F) := by
    rw [← h1, ← map_mul, ← algebraMap_multiplier_M0 hQ a, AlgHom.commutes]
  have h3 : (-matJ : Matrix (Fin 2) (Fin 2) (AU Q e f)) * matJ = 1 := neg_matJ_mul_matJ
  calc _ = xi he hf hef hg ((a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
        (matJ * matStarSigma g (xi he hf hef hg ((a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) * -matJ) *
        matJ := by
        simp only [mul_assoc]
        rw [h3, mul_one]
    _ = _ := by
        rw [h2, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

omit hQ in
/-- **(15.17)**, p. 153, entries: for $\alpha \in G^+(V)$ every entry of $\Xi(\alpha)$ lies in $A^+(U)$ (so
$\Xi(\alpha) \in M_2(A^+(U))$). -/
@[kb "shimura2004" "(15.17), p. 153 (Ξ(G⁺(V)) ⊆ GL₂(A⁺(U)): entries lie in A⁺(U))"]
theorem formula_15_17_mem (hg : Q (g : V) ≠ 0) (a : M0 Q) (i j : Fin 2) :
    xi he hf hef hg ((a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) i j ∈ evenOdd (QU Q e f) 0 :=
  (xi_mem_evenOdd_zero_iff he hf hef hg _).1 a.2.1 i j

omit hQ in
/-- **(15.17)**, p. 153, invertibility: for $\alpha \in G^+(V)$, $\Xi(\alpha)$ is a unit of $M_2(A(U))$, being the
image of a unit of $A(V)$ under the algebra homomorphism $\Xi$. -/
@[kb "shimura2004" "(15.17), p. 153 (Ξ(α) is invertible for α ∈ G⁺(V))"]
theorem formula_15_17_isUnit (hg : Q (g : V) ≠ 0) (a : M0 Q) :
    IsUnit (xi he hf hef hg ((a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) :=
  (a : (CliffordAlgebra Q)ˣ).isUnit.map (xi he hf hef hg)

end Hyp

end MatrixModel

end QuadFormsKB.Shimura2004
