/-
# Shimura 2004, Proposition 4.3, (4.10a): the matrix of $\tau(\alpha)$ for $\alpha \in P'_1$

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Chapter I, §4.2,
Proposition 4.3, (4.10a) (printed p. 30). Page numbers in the tags are printed pages.

**Setting and dictionary.** As in `Wave6/Prop43.lean`: a weak Witt decomposition $V = U + Fe + Ff$ (`Q e = 0`,
`Q f = 0`, `polar Q e f = 1`), $U$ = `uSpace Q e f`, $\Psi : A(V) \cong M_2(A(U))$ = `psi`, and for
$\alpha \in P'_1$ Proposition 4.3 gives $\Psi(\alpha) = \begin{pmatrix} rd & yd \\ 0 & d\end{pmatrix}$ with
$d \in G'(U)$, $r \in F^\times$, $y \in U$ (`Prop43.prop_4_3_shape`). Shimura's $\varphi[y] = y^2$ is `Q y`, and his
$2\omega\cdot{}^ty$ (the column vector of $u \mapsto 2\varphi(u, y)$) is `QuadraticMap.polar Q · y`.

**(4.10a)** says that $\tau(\alpha)$ ($x \mapsto \alpha^{-1}x\alpha$, acting on row vectors from the right) is
represented by
$$\begin{pmatrix} 1 & -y & -\varphi[y] \\ 0 & 1 & 2\omega\cdot{}^ty \\ 0 & 0 & 1\end{pmatrix}
\begin{pmatrix} r & 0 & 0 \\ 0 & \tau(d) & 0 \\ 0 & 0 & r^{-1}\end{pmatrix},$$
the coordinates of $V$ taken in the order $(f, U, e)$ (this is the order forced by $e\tau(\alpha) = r^{-1}e$, which
follows from (4.10)). Multiplied out, this is the coordinate-free formula proved here (`formula_4_10a`):
$$(af + u + be)\,\tau(\alpha) = (ra)f + (u - ay)\tau(d) + r^{-1}\bigl(b + 2\varphi(u, y) - a\varphi[y]\bigr)e$$
for $a, b \in F$ and $u \in U$. Unconditional; standard axioms only.
-/
import QuadFormsKB.Literature.Shimura2004.Wave6.Prop43
import QuadFormsKB.Citation

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Cassels QuadFormsKB.OMeara

namespace Formula410a

open MatrixModel

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V} {e f : V}

local notation "A" => CliffordAlgebra Q

section Hyp

variable (he : Q e = 0) (hf : Q f = 0) (hef : QuadraticMap.polar Q e f = 1)
include he hf hef

theorem proj_comb (a b : F) (u : uSpace Q e f) :
    proj he hf hef (a • f + (u : V) + b • e) = u := by
  apply Subtype.ext
  rw [map_add, map_add, map_smul, map_smul]
  simp only [Submodule.coe_add, Submodule.coe_smul, proj_e he hf hef, proj_f he hf hef,
    proj_of_mem he hf hef u.2, smul_zero, zero_add, add_zero]

theorem polar_comb_f (a b : F) (u : uSpace Q e f) :
    QuadraticMap.polar Q (a • f + (u : V) + b • e) f = b := by
  simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, polar_f_f he hf hef,
    (mem_uSpace.1 u.2).2, hef, smul_eq_mul]
  ring

theorem polar_comb_e (a b : F) (u : uSpace Q e f) :
    QuadraticMap.polar Q (a • f + (u : V) + b • e) e = a := by
  simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, polar_f_e he hf hef,
    (mem_uSpace.1 u.2).1, polar_e_e he hf hef, smul_eq_mul]
  ring

/-- **(4.10a)** (Shimura 2004, Proposition 4.3, p. 30): if $\Psi(\alpha) = \begin{pmatrix} rd & yd \\ 0 & d
\end{pmatrix}$ with $r \in F^\times$, $y \in U$, $d \in G'(U)$ (the shape (4.10) of every $\alpha \in P'_1$), then
for $a, b \in F$, $u \in U$:
$(af + u + be)\tau(\alpha) = (ra)f + (u - ay)\tau(d) + r^{-1}(b + 2\varphi(u, y) - a\varphi[y])e$, i.e. $\tau(\alpha)$
is represented on $(f, U, e)$-coordinates by the product of matrices (4.10a). Here $\tau(\alpha) : x \mapsto
\alpha^{-1}x\alpha$ (`tau`), $\tau(d) : u \mapsto d^{-1}ud$ on $U$, $2\varphi(u, y)$ = `polar Q u y` and
$\varphi[y]$ = `Q y`. -/
@[kb "shimura2004" "Prop. 4.3, (4.10a), p. 30 (τ(α) is represented by [[1, −y, −φ[y]], [0, 1, 2ω·ᵗy], [0, 0, 1]]·diag[r, τ(d), r⁻¹])"]
theorem formula_4_10a (α : homogeneousCliffordGroup Q) {r : F} (hr : r ≠ 0) (y : uSpace Q e f)
    (d : (AU Q e f)ˣ) (hd : d ∈ homogeneousCliffordGroup (QU Q e f))
    (hΨ : psi he hf hef ((α : Aˣ) : A) = !![r • (d : AU Q e f), ι (QU Q e f) y * d; 0, d])
    (a b : F) (u : uSpace Q e f) :
    tau ⟨(α : Aˣ), homogeneous_le_cliffordGroup α.2⟩ (a • f + (u : V) + b • e) =
      (r * a) • f + ((tau ⟨d, homogeneous_le_cliffordGroup hd⟩ (u - a • y) : uSpace Q e f) : V) +
        (r⁻¹ * (b + QuadraticMap.polar Q u y - a * Q y)) • e := by
  set w : uSpace Q e f := tau ⟨d, homogeneous_le_cliffordGroup hd⟩ (u - a • y)
  set c : F := r⁻¹ * (b + QuadraticMap.polar Q u y - a * Q y)
  have hw : ι (QU Q e f) w = ((d⁻¹ : (AU Q e f)ˣ) : AU Q e f) * ι (QU Q e f) (u - a • y) * d := tau_spec _ _
  apply cliffordι_injective Q
  rw [tau_spec]
  suffices h : ((α : Aˣ) : A) * ι Q ((r * a) • f + (w : V) + c • e) =
      ι Q (a • f + (u : V) + b • e) * ((α : Aˣ) : A) by
    change (((α : Aˣ)⁻¹ : Aˣ) : A) * ι Q _ * ((α : Aˣ) : A) = _
    rw [mul_assoc, ← h, ← mul_assoc, Units.inv_mul, one_mul]
  apply (psi_bijective he hf hef).1
  rw [map_mul, map_mul, hΨ, psi_ι, psi_ι, psiVec_apply, psiVec_apply, proj_comb he hf hef,
    proj_comb he hf hef, polar_comb_f he hf hef, polar_comb_f he hf hef, polar_comb_e he hf hef,
    polar_comb_e he hf hef, hw]
  have hyy (z : AU Q e f) : ι (QU Q e f) y * (ι (QU Q e f) y * z) = Q y • z := by
    rw [← mul_assoc, ι_sq_scalar, Algebra.smul_def]; rfl
  have huy (z : AU Q e f) : ι (QU Q e f) y * (ι (QU Q e f) u * z) =
      QuadraticMap.polar Q u y • z - ι (QU Q e f) u * (ι (QU Q e f) y * z) := by
    have h := ι_mul_ι_add_swap (Q := QU Q e f) u y
    rw [eq_sub_iff_add_eq, ← mul_assoc, ← mul_assoc, ← add_mul, add_comm, h, Algebra.smul_def]; rfl
  have hc' : r * c = b + QuadraticMap.polar Q u y - a * Q y := by
    simp only [c]; rw [← mul_assoc, mul_inv_cancel₀ hr, one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, map_sub, Algebra.smul_def, mul_assoc]
  all_goals simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_sub,
    sub_mul, hyy, huy, smul_smul]
  all_goals (match_scalars <;> first | linear_combination hc' | ring)

variable (hQ : (QuadraticMap.associated Q).Nondegenerate)

include hQ in
/-- **(4.10a)** for every $\alpha \in P'_1$ (Shimura 2004, Proposition 4.3, p. 30): there are $r \in F^\times$,
$y \in U$ and $d \in G'(U)$ with $\Psi(\alpha) = \begin{pmatrix} rd & yd \\ 0 & d\end{pmatrix}$ such that
$(af + u + be)\tau(\alpha) = (ra)f + (u - ay)\tau(d) + r^{-1}(b + 2\varphi(u, y) - a\varphi[y])e$ for all
$a, b \in F$, $u \in U$. -/
@[kb "shimura2004" "Prop. 4.3, (4.10a), p. 30 (τ(α) for α ∈ P'_1 is [[1, −y, −φ[y]], [0, 1, 2ω·ᵗy], [0, 0, 1]]·diag[r, τ(d), r⁻¹])"]
theorem exists_formula_4_10a (α : homogeneousCliffordGroup Q) (hα : (α : Aˣ) ∈ parabolicG' Q (F ∙ e)) :
    ∃ (r : F) (y : uSpace Q e f) (d : (AU Q e f)ˣ) (hd : d ∈ homogeneousCliffordGroup (QU Q e f)),
      r ≠ 0 ∧ psi he hf hef ((α : Aˣ) : A) = !![r • (d : AU Q e f), ι (QU Q e f) y * d; 0, d] ∧
      ∀ (a b : F) (u : uSpace Q e f),
        tau ⟨(α : Aˣ), homogeneous_le_cliffordGroup α.2⟩ (a • f + (u : V) + b • e) =
          (r * a) • f + ((tau ⟨d, homogeneous_le_cliffordGroup hd⟩ (u - a • y) : uSpace Q e f) : V) +
            (r⁻¹ * (b + QuadraticMap.polar Q u y - a * Q y)) • e := by
  obtain ⟨r, hdu, y, hr, hdm, hΨ⟩ := Prop43.prop_4_3_shape he hf hef hQ α hα
  rw [← hdu.unit_spec] at hΨ
  exact ⟨r, y, hdu.unit, hdm, hr, hΨ, formula_4_10a he hf hef α hr y hdu.unit hdm hΨ⟩

end Hyp

end Formula410a

end QuadFormsKB.Shimura2004
