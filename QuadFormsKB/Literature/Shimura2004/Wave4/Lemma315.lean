/-
# Shimura 2004, Lemma 3.15: the entries of $\Psi(\alpha)$ for $\alpha \in G'(V)$

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Chapter I, Lemma 3.15 (printed
p. 27). Page numbers in the tags are printed pages.

**Setting and dictionary.** As in `Wave4/MatrixModel.lean` and `Wave4/MatrixGroup.lean`: a weak Witt
decomposition $V = U + Fe + Ff$ (`Q e = 0`, `Q f = 0`, `polar Q e f = 1`), $\varphi$ nondegenerate, and
$\Psi : A(V) \cong M_2(A(U))$ (`psi`). For $\alpha \in G'(V)$ (`homogeneousCliffordGroup Q`) write $a, b, c, d$ for
the entries of $\Psi(\alpha)$ (rows $(a, b)$ and $(c, d)$; in Lean `ξ 0 0`, `ξ 0 1`, `ξ 1 0`, `ξ 1 1`). "$x \in U$"
for $x \in A(U)$ means $x = \iota(u)$ for a vector $u \in U$ (`IsVecU`), and "$x \in F$" means $x$ is a scalar
(`IsScalarU`). Lemma 3.15 is stated in the setting of §3.14 ($\dim V > 2$, $U \ne 0$), but its statement and proof
only use the weak Witt decomposition; no assumption on $\dim U$ is made here.

**Proves** (all unconditional; standard axioms only): **Lemma 3.15**,
* (i) $xy^* = yx^* \in U$ and $x^*y = y^*x \in U$ for $(x, y) = (a, b), (a, c), (d, b), (d, c)$
  (`lemma_3_15_i`, with the predicate `PairProp`);
* (ii) $xx^* = x^*x \in F$ and $xUx^* \subseteq U$ for $x = a, b, c, d$ (`lemma_3_15_ii`, predicate `EntryProp`);
* (iii) each of $a, b, c, d$ that is invertible lies in $G'(U)$ (`lemma_3_15_iii`).

The proof follows Shimura's: $\Psi(\alpha^{-1}e\alpha)$, $\Psi(\alpha^{-1}f\alpha)$, $\Psi(\alpha e\alpha^{-1})$,
$\Psi(\alpha f\alpha^{-1})$ lie in $\Psi(V)$, whose elements have the shape (2.8) (`VecShape`); with (3.9a) this
gives half of (i) and (ii) (`step_conj`); the identity $\pm\nu(\alpha) = ad^* - bc^*$ of (3.9) gives $cd^* \in U$
(`step_cd`), and replacing $\alpha$ by $\kappa\alpha$, $\alpha^{-1}$, $\kappa\alpha^{-1}$ ($\kappa = e + f$) gives the
rest; $xUx^* \subseteq U$ comes from $\alpha U \alpha^{-1} \subseteq V$ (`step_conj_U`).
-/
import QuadFormsKB.Literature.Shimura2004.Wave4.MatrixGroup
import QuadFormsKB.Citation

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Cassels QuadFormsKB.OMeara

namespace MatrixModel

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V} {e f : V}

/-! ### Vectors and scalars of $A(U)$ -/

variable (Q e f) in
/-- $x \in A(U)$ is a vector of $U$ (Shimura's "$x \in U$"). -/
def IsVecU (x : AU Q e f) : Prop := ∃ u : uSpace Q e f, x = ι (QU Q e f) u

variable (Q e f) in
/-- $x \in A(U)$ is a scalar (Shimura's "$x \in F$"). -/
def IsScalarU (x : AU Q e f) : Prop := ∃ r : F, x = algebraMap F _ r

theorem IsVecU.add {x y : AU Q e f} (hx : IsVecU Q e f x) (hy : IsVecU Q e f y) : IsVecU Q e f (x + y) := by
  obtain ⟨u, rfl⟩ := hx; obtain ⟨v, rfl⟩ := hy; exact ⟨u + v, by rw [map_add]⟩

theorem IsVecU.neg {x : AU Q e f} (hx : IsVecU Q e f x) : IsVecU Q e f (-x) := by
  obtain ⟨u, rfl⟩ := hx; exact ⟨-u, by rw [map_neg]⟩

theorem IsVecU.smul {x : AU Q e f} (hx : IsVecU Q e f x) (r : F) : IsVecU Q e f (r • x) := by
  obtain ⟨u, rfl⟩ := hx; exact ⟨r • u, by rw [map_smul]⟩

theorem IsVecU.algebraMap_mul {x : AU Q e f} (hx : IsVecU Q e f x) (r : F) :
    IsVecU Q e f (algebraMap F _ r * x) := by
  rw [← Algebra.smul_def]; exact hx.smul r

theorem IsVecU.mul_algebraMap {x : AU Q e f} (hx : IsVecU Q e f x) (r : F) :
    IsVecU Q e f (x * algebraMap F _ r) := by
  rw [← Algebra.commutes]; exact hx.algebraMap_mul r

theorem IsVecU.sub {x y : AU Q e f} (hx : IsVecU Q e f x) (hy : IsVecU Q e f y) : IsVecU Q e f (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem IsVecU.of_smul {x : AU Q e f} {r : F} (hr : r ≠ 0) (hx : IsVecU Q e f (r • x)) : IsVecU Q e f x := by
  have := hx.smul r⁻¹
  rwa [smul_smul, inv_mul_cancel₀ hr, one_smul] at this

theorem IsVecU.of_neg {x : AU Q e f} (hx : IsVecU Q e f (-x)) : IsVecU Q e f x := by
  simpa using hx.neg

theorem IsScalarU.neg {x : AU Q e f} (hx : IsScalarU Q e f x) : IsScalarU Q e f (-x) := by
  obtain ⟨r, rfl⟩ := hx; exact ⟨-r, by rw [map_neg]⟩

theorem IsScalarU.of_neg {x : AU Q e f} (hx : IsScalarU Q e f (-x)) : IsScalarU Q e f x := by
  simpa using hx.neg

theorem IsScalarU.mul_comm {x : AU Q e f} (hx : IsScalarU Q e f x) (y : AU Q e f) : x * y = y * x := by
  obtain ⟨r, rfl⟩ := hx; exact Algebra.commutes r y

theorem IsScalarU.of_smul {x : AU Q e f} {r : F} (hr : r ≠ 0) (hx : IsScalarU Q e f (r • x)) :
    IsScalarU Q e f x := by
  obtain ⟨s, hs⟩ := hx
  refine ⟨r⁻¹ * s, ?_⟩
  rw [map_mul, ← hs, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hr, one_smul]

variable (Q e f) in
/-- The shape (2.8) of $\Psi(x)$ for a vector $x = u + re + sf$: rows $(u, r)$ and $(s, -u)$. -/
def VecShape (M : Matrix (Fin 2) (Fin 2) (AU Q e f)) : Prop :=
  IsVecU Q e f (M 0 0) ∧ IsScalarU Q e f (M 0 1) ∧ IsScalarU Q e f (M 1 0) ∧ M 1 1 = -M 0 0

theorem VecShape.of_smul {M : Matrix (Fin 2) (Fin 2) (AU Q e f)} {r : F} (hr : r ≠ 0)
    (h : VecShape Q e f (r • M)) : VecShape Q e f M := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [Matrix.smul_apply] at h1 h2 h3 h4
  refine ⟨h1.of_smul hr, h2.of_smul hr, h3.of_smul hr, ?_⟩
  have := congrArg (fun x => r⁻¹ • x) h4
  simpa [smul_smul, inv_mul_cancel₀ hr, ← smul_neg] using this

/-- $xx^* = x^*x$ once both are scalars (end of the proof of Lemma 3.15). -/
theorem mul_reverse_comm_of_scalar {x : AU Q e f} (h1 : IsScalarU Q e f (x * reverse x))
    (h2 : IsScalarU Q e f (reverse x * x)) : x * reverse x = reverse x * x := by
  obtain ⟨c, hc⟩ := h1
  obtain ⟨c', hc'⟩ := h2
  have inj := (algebraMap F (AU Q e f)).injective
  -- $cx = xx^*x = xc'$
  have H : algebraMap F (AU Q e f) c * x = algebraMap F (AU Q e f) c' * x := by
    rw [← hc, mul_assoc, hc']
    exact (Algebra.commutes c' x).symm
  have H1 : c * c = c' * c := by
    apply inj
    have := congrArg (· * reverse x) H
    simp only [mul_assoc, hc] at this
    rw [map_mul, map_mul]; exact this
  have H2 : c * c' = c' * c' := by
    apply inj
    have := congrArg (reverse x * ·) H
    simp only [← mul_assoc, ← Algebra.commutes] at this
    simp only [mul_assoc, hc'] at this
    rw [map_mul, map_mul]; exact this
  have hcc : c = c' := by
    by_cases h0 : c = 0
    · subst h0
      have : c' * c' = 0 := by rw [← H2, zero_mul]
      exact (mul_self_eq_zero.1 this).symm
    · exact mul_right_cancel₀ h0 H1
  rw [hc, hc', hcc]

/-- An invertible homogeneous $x$ with $xx^* \in F$ and $xUx^* \subseteq U$ lies in $G'(U)$ (as in (3.5)). -/
theorem mem_homogeneous_of {x : AU Q e f} (hx : IsUnit x)
    (hpar : x ∈ evenOdd (QU Q e f) 0 ∨ x ∈ evenOdd (QU Q e f) 1) (hs : IsScalarU Q e f (x * reverse x))
    (hv : ∀ u : uSpace Q e f, IsVecU Q e f (x * ι (QU Q e f) u * reverse x)) :
    hx.unit ∈ homogeneousCliffordGroup (QU Q e f) := by
  obtain ⟨r, hr⟩ := hs
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero] at hr
    have h0 : reverse x = 0 := by
      have := congrArg (fun y => ((hx.unit⁻¹ : (AU Q e f)ˣ) : AU Q e f) * y) hr
      simpa [← mul_assoc] using this
    have : x = 0 := by simpa using congrArg reverse h0
    exact hx.ne_zero this
  have hinv : ((hx.unit⁻¹ : (AU Q e f)ˣ) : AU Q e f) = r⁻¹ • reverse x := by
    rw [Units.inv_eq_of_mul_eq_one_right]
    rw [IsUnit.unit_spec, mul_smul_comm, hr, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hr0, map_one]
  refine ⟨fun y => ?_, by simpa using hpar⟩
  obtain ⟨w, hw⟩ := hv y
  refine ⟨r⁻¹ • w, ?_⟩
  rw [hinv, IsUnit.unit_spec, mul_smul_comm, hw, map_smul]

section Hyp

variable (he : Q e = 0) (hf : Q f = 0) (hef : QuadraticMap.polar Q e f = 1)
  (hQ : (QuadraticMap.associated Q).Nondegenerate)
include he hf hef

/-- $\Psi(V)$ (by (2.8)): $\Psi(x)$ has the shape `VecShape` for every vector $x$. -/
theorem vecShape_psi (v : V) : VecShape Q e f (psi he hf hef (ι Q v)) := by
  rw [psi_ι, psiVec_apply]
  refine ⟨⟨proj he hf hef v, by simp⟩, ⟨QuadraticMap.polar Q v f, by simp⟩,
    ⟨QuadraticMap.polar Q v e, by simp⟩, by simp⟩

omit he hf hef in
/-- The matrix with rows $(d^*, -b^*)$, $(-c^*, a^*)$ of (3.9a). -/
def adjU (ξ : Matrix (Fin 2) (Fin 2) (AU Q e f)) : Matrix (Fin 2) (Fin 2) (AU Q e f) :=
  !![reverse (ξ 1 1), -reverse (ξ 0 1); -reverse (ξ 1 0), reverse (ξ 0 0)]

omit he hf hef in
theorem adjU_mul_e_mul (ξ : Matrix (Fin 2) (Fin 2) (AU Q e f)) :
    adjU ξ * !![0, 1; 0, 0] * ξ = !![reverse (ξ 1 1) * ξ 1 0, reverse (ξ 1 1) * ξ 1 1;
      -(reverse (ξ 1 0) * ξ 1 0), -(reverse (ξ 1 0) * ξ 1 1)] := by
  ext i j
  simp only [adjU, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp

omit he hf hef in
theorem adjU_mul_f_mul (ξ : Matrix (Fin 2) (Fin 2) (AU Q e f)) :
    adjU ξ * !![0, 0; 1, 0] * ξ = !![-(reverse (ξ 0 1) * ξ 0 0), -(reverse (ξ 0 1) * ξ 0 1);
      reverse (ξ 0 0) * ξ 0 0, reverse (ξ 0 0) * ξ 0 1] := by
  ext i j
  simp only [adjU, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp

omit he hf hef in
theorem mul_e_mul_adjU (ξ : Matrix (Fin 2) (Fin 2) (AU Q e f)) :
    ξ * !![0, 1; 0, 0] * adjU ξ = !![-(ξ 0 0 * reverse (ξ 1 0)), ξ 0 0 * reverse (ξ 0 0);
      -(ξ 1 0 * reverse (ξ 1 0)), ξ 1 0 * reverse (ξ 0 0)] := by
  ext i j
  simp only [adjU, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp

omit he hf hef in
theorem mul_f_mul_adjU (ξ : Matrix (Fin 2) (Fin 2) (AU Q e f)) :
    ξ * !![0, 0; 1, 0] * adjU ξ = !![ξ 0 1 * reverse (ξ 1 1), -(ξ 0 1 * reverse (ξ 0 1));
      ξ 1 1 * reverse (ξ 1 1), -(ξ 1 1 * reverse (ξ 0 1))] := by
  ext i j
  simp only [adjU, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp

include hQ in
/-- (3.9a) for $\Psi(\alpha)$: $\Psi(\alpha^{-1}) = \mu(\alpha)^{-1}$ `adjU` $\Psi(\alpha)$. -/
theorem psi_inv_eq (α : homogeneousCliffordGroup Q) :
    psi he hf hef (((α⁻¹ : homogeneousCliffordGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      (((muHom hQ α : Fˣ) : F))⁻¹ • adjU (psi he hf hef ((α : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) := by
  have h := formula_3_9a (⟨psiUnits he hf hef (α : (CliffordAlgebra Q)ˣ), psi_mem_matGroup he hf hef hQ α⟩ :
    matGroup (QU Q e f))
  rw [matMu_psi he hf hef hQ α] at h
  have h' : ((psiUnits he hf hef (α : (CliffordAlgebra Q)ˣ))⁻¹ : (Matrix (Fin 2) (Fin 2) (AU Q e f))ˣ) =
      psiUnits he hf hef ((α⁻¹ : homogeneousCliffordGroup Q) : (CliffordAlgebra Q)ˣ) := by
    rw [← map_inv]; rfl
  have h'' := congrArg (fun u : (Matrix (Fin 2) (Fin 2) (AU Q e f))ˣ => (u : Matrix (Fin 2) (Fin 2) (AU Q e f))) h'
  rw [← Units.val_inv_eq_inv_val]
  refine h''.symm.trans ?_
  exact h

include hQ in
/-- The facts obtained from $\alpha^{-1}e\alpha$, $\alpha^{-1}f\alpha$, $\alpha e\alpha^{-1}$, $\alpha f\alpha^{-1}$
being vectors (first part of the proof of Lemma 3.15). -/
theorem step_conj (α : homogeneousCliffordGroup Q) :
    let ξ := psi he hf hef ((α : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
    (IsVecU Q e f (reverse (ξ 1 1) * ξ 1 0) ∧ IsScalarU Q e f (reverse (ξ 1 1) * ξ 1 1) ∧
        IsScalarU Q e f (reverse (ξ 1 0) * ξ 1 0) ∧ reverse (ξ 1 0) * ξ 1 1 = reverse (ξ 1 1) * ξ 1 0) ∧
      (IsVecU Q e f (reverse (ξ 0 1) * ξ 0 0) ∧ IsScalarU Q e f (reverse (ξ 0 1) * ξ 0 1) ∧
        IsScalarU Q e f (reverse (ξ 0 0) * ξ 0 0) ∧ reverse (ξ 0 0) * ξ 0 1 = reverse (ξ 0 1) * ξ 0 0) ∧
      (IsVecU Q e f (ξ 0 0 * reverse (ξ 1 0)) ∧ IsScalarU Q e f (ξ 0 0 * reverse (ξ 0 0)) ∧
        IsScalarU Q e f (ξ 1 0 * reverse (ξ 1 0)) ∧ ξ 1 0 * reverse (ξ 0 0) = ξ 0 0 * reverse (ξ 1 0)) ∧
      (IsVecU Q e f (ξ 0 1 * reverse (ξ 1 1)) ∧ IsScalarU Q e f (ξ 0 1 * reverse (ξ 0 1)) ∧
        IsScalarU Q e f (ξ 1 1 * reverse (ξ 1 1)) ∧ ξ 1 1 * reverse (ξ 0 1) = ξ 0 1 * reverse (ξ 1 1)) := by
  intro ξ
  set m : F := ((muHom hQ α : Fˣ) : F)
  have hm : m⁻¹ ≠ 0 := inv_ne_zero (Units.ne_zero _)
  have hinv := psi_inv_eq he hf hef hQ α
  have hα : (α : (CliffordAlgebra Q)ˣ) ∈ cliffordGroup Q := α.2.1
  have e1 : (((α : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      (((α⁻¹ : homogeneousCliffordGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := rfl
  -- $\alpha^{-1} v \alpha$ and $\alpha v \alpha^{-1}$ are vectors
  have conj1 : ∀ v : V, VecShape Q e f (m⁻¹ • (adjU ξ * psi he hf hef (ι Q v) * ξ)) := by
    intro v
    obtain ⟨y, hy⟩ := (mem_cliffordGroup_iff (α : (CliffordAlgebra Q)ˣ)).1 hα v
    have := vecShape_psi he hf hef y
    rw [hy, map_mul, map_mul, e1, hinv, Matrix.smul_mul, Matrix.smul_mul] at this
    exact this
  have conj2 : ∀ v : V, VecShape Q e f (m⁻¹ • (ξ * psi he hf hef (ι Q v) * adjU ξ)) := by
    intro v
    obtain ⟨y, hy⟩ := hα v
    have := vecShape_psi he hf hef y
    rw [hy, map_mul, map_mul, e1, hinv, Matrix.mul_smul] at this
    exact this
  have A1 := VecShape.of_smul hm (conj1 e)
  have A2 := VecShape.of_smul hm (conj1 f)
  have A3 := VecShape.of_smul hm (conj2 e)
  have A4 := VecShape.of_smul hm (conj2 f)
  rw [psi_e, adjU_mul_e_mul] at A1
  rw [psi_f, adjU_mul_f_mul] at A2
  rw [psi_e, mul_e_mul_adjU] at A3
  rw [psi_f, mul_f_mul_adjU] at A4
  obtain ⟨a1, a2, a3, a4⟩ := A1
  obtain ⟨b1, b2, b3, b4⟩ := A2
  obtain ⟨c1, c2, c3, c4⟩ := A3
  obtain ⟨d1, d2, d3, d4⟩ := A4
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const, neg_neg, neg_inj] at a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4
  exact ⟨⟨a1, a2, a3.of_neg, a4⟩, ⟨b1.of_neg, b2.of_neg, b3, b4⟩, ⟨c1.of_neg, c2, c3.of_neg, c4⟩,
    ⟨d1, d2.of_neg, d3, d4⟩⟩

include hQ in
/-- $cd^* \in U$ (second part of the proof of Lemma 3.15): $\pm\nu(\alpha)cd^* = (ac^*)(dd^*) - (c^*c)(bd^*)$. -/
theorem step_cd (α : homogeneousCliffordGroup Q) :
    IsVecU Q e f (psi he hf hef ((α : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) 1 0 *
      reverse (psi he hf hef ((α : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) 1 1)) := by
  obtain ⟨⟨-, -, hcc, hdc⟩, -, ⟨hac, -, -, -⟩, ⟨hbd, -, hdd, -⟩⟩ := step_conj he hf hef hQ α
  have h39 := (formula_3_9 (⟨psiUnits he hf hef (α : (CliffordAlgebra Q)ˣ), psi_mem_matGroup he hf hef hQ α⟩ :
    matGroup (QU Q e f))).1
  rw [matMu_psi he hf hef hQ α] at h39
  set ξ := psi he hf hef ((α : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) with hξ
  change ξ 0 0 * reverse (ξ 1 1) - ξ 0 1 * reverse (ξ 1 0) = _ at h39
  set m : F := ((muHom hQ α : Fˣ) : F)
  have hm : m ≠ 0 := Units.ne_zero _
  obtain ⟨r, hr⟩ := hdd
  obtain ⟨r', hr'⟩ := hcc
  -- $m\,cd^* = (ad^* - bc^*)cd^* = a(d^*c)d^* - b(c^*c)d^* = (ac^*)(dd^*) - (c^*c)(bd^*)$
  have key : m • (ξ 1 0 * reverse (ξ 1 1)) =
      ξ 0 0 * reverse (ξ 1 0) * algebraMap F _ r - algebraMap F _ r' * (ξ 0 1 * reverse (ξ 1 1)) := by
    rw [Algebra.smul_def, ← h39, sub_mul, ← hr, ← hr']
    congr 1
    · calc ξ 0 0 * reverse (ξ 1 1) * (ξ 1 0 * reverse (ξ 1 1))
          = ξ 0 0 * (reverse (ξ 1 1) * ξ 1 0) * reverse (ξ 1 1) := by simp only [mul_assoc]
        _ = ξ 0 0 * (reverse (ξ 1 0) * ξ 1 1) * reverse (ξ 1 1) := by rw [hdc]
        _ = _ := by simp only [mul_assoc]
    · calc ξ 0 1 * reverse (ξ 1 0) * (ξ 1 0 * reverse (ξ 1 1))
          = ξ 0 1 * (reverse (ξ 1 0) * ξ 1 0) * reverse (ξ 1 1) := by simp only [mul_assoc]
        _ = _ := by rw [hr', ← Algebra.commutes, mul_assoc]
  apply IsVecU.of_smul hm
  rw [key]
  exact (hac.mul_algebraMap r).sub (hbd.algebraMap_mul r')

include hQ in
/-- $xUx^* \subseteq U$ for $x = a, b, c, d$ (first step of Shimura's proof): from $\alpha v = w\alpha$ with
$w \in V$. -/
theorem step_conj_U (α : homogeneousCliffordGroup Q) (v : uSpace Q e f) (i j : Fin 2) :
    IsVecU Q e f (psi he hf hef ((α : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) i j * ι (QU Q e f) v *
      reverse (psi he hf hef ((α : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) i j)) := by
  obtain ⟨⟨-, -, hcc, -⟩, ⟨-, hbb, haa, -⟩, ⟨hac, haa', hcc', hca⟩, ⟨hbd, hbb', hdd', hdb⟩⟩ :=
    step_conj he hf hef hQ α
  set ξ := psi he hf hef ((α : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) with hξ
  obtain ⟨w, hw⟩ := α.2.1 (v : V)
  -- $\alpha v = w \alpha$
  have hcomm : ξ * psi he hf hef (ι Q (v : V)) = psi he hf hef (ι Q w) * ξ := by
    rw [hξ, ← map_mul, ← map_mul, hw, mul_assoc, Units.inv_mul, mul_one]
  obtain ⟨⟨u', hu'⟩, ⟨r, hr⟩, ⟨s, hs⟩, h11⟩ := vecShape_psi he hf hef w
  rw [psi_ι_of_mem, (psi he hf hef (ι Q w)).eta_fin_two, hu', hr, hs, h11, hu'] at hcomm
  have E := fun i j => congrArg (fun M : Matrix (Fin 2) (Fin 2) (AU Q e f) => M i j) hcomm
  have E00 := E 0 0
  have E01 := E 0 1
  have E10 := E 1 0
  have E11 := E 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const,
    mul_zero, zero_mul, add_zero, zero_add, mul_neg] at E00 E01 E10 E11
  set x := ι (QU Q e f) v
  set y := ι (QU Q e f) u'
  have hy : IsVecU Q e f y := ⟨u', rfl⟩
  obtain ⟨ta, hta⟩ := haa'
  obtain ⟨tb, htb⟩ := hbb'
  obtain ⟨tc, htc⟩ := hcc'
  obtain ⟨td, htd⟩ := hdd'
  fin_cases i <;> fin_cases j
  · -- $ava^* = (ya + rc)a^* = y(aa^*) + r(ca^*)$
    show IsVecU Q e f (ξ 0 0 * x * reverse (ξ 0 0))
    rw [E00, add_mul, mul_assoc, hta, mul_assoc, hca]
    exact (hy.mul_algebraMap ta).add (hac.algebraMap_mul r)
  · -- $bvb^* = -(yb + rd)b^*$
    show IsVecU Q e f (ξ 0 1 * x * reverse (ξ 0 1))
    have : ξ 0 1 * x = -(y * ξ 0 1 + algebraMap F _ r * ξ 1 1) := by rw [← E01, neg_neg]
    rw [this, neg_mul, add_mul, mul_assoc, htb, mul_assoc, hdb]
    exact ((hy.mul_algebraMap tb).add (hbd.algebraMap_mul r)).neg
  · -- $cvc^* = (sa - yc)c^*$
    show IsVecU Q e f (ξ 1 0 * x * reverse (ξ 1 0))
    rw [E10, add_mul, mul_assoc, mul_assoc, htc, neg_mul]
    exact (hac.algebraMap_mul s).add (hy.mul_algebraMap tc).neg
  · -- $dvd^* = -(sb - yd)d^*$
    show IsVecU Q e f (ξ 1 1 * x * reverse (ξ 1 1))
    have : ξ 1 1 * x = -(algebraMap F _ s * ξ 0 1 + -y * ξ 1 1) := by rw [← E11, neg_neg]
    rw [this, neg_mul, add_mul, mul_assoc, mul_assoc, htd, neg_mul]
    exact ((hbd.algebraMap_mul s).add (hy.mul_algebraMap td).neg).neg

/-! ### The statements of Lemma 3.15 -/

omit he hf hef in
variable (Q e f) in
/-- The property of the pairs in Lemma 3.15 (i): $xy^* = yx^* \in U$ and $x^*y = y^*x \in U$. -/
def PairProp (x y : AU Q e f) : Prop :=
  x * reverse y = y * reverse x ∧ IsVecU Q e f (x * reverse y) ∧
    reverse x * y = reverse y * x ∧ IsVecU Q e f (reverse x * y)

omit he hf hef in
variable (Q e f) in
/-- The property of the entries in Lemma 3.15 (ii): $xx^* = x^*x \in F$ and $xUx^* \subseteq U$. -/
def EntryProp (x : AU Q e f) : Prop :=
  x * reverse x = reverse x * x ∧ IsScalarU Q e f (x * reverse x) ∧
    ∀ u : uSpace Q e f, IsVecU Q e f (x * ι (QU Q e f) u * reverse x)

/-- The element $\kappa = e + f$ of $G^-(V)$ ($\kappa^2 = 1$). -/
def kappaH : homogeneousCliffordGroup Q :=
  ⟨vecUnit (e + f) (by
      rw [QuadraticMap.map_add (⇑Q), he, hf, hef]; norm_num),
    cliffordGroupOdd_subset_homogeneous (vecUnit_mem_cliffordGroupOdd _ _)⟩

theorem psi_kappaH_mul (β : CliffordAlgebra Q) :
    psi he hf hef (((kappaH he hf hef : homogeneousCliffordGroup Q) : (CliffordAlgebra Q)ˣ) * β) =
      !![psi he hf hef β 1 0, psi he hf hef β 1 1; psi he hf hef β 0 0, psi he hf hef β 0 1] := by
  have hk : (((kappaH he hf hef : homogeneousCliffordGroup Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      ι Q e + ι Q f := by
    simp [kappaH, vecUnit]
  rw [map_mul, hk, map_add, psi_e, psi_f]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp

include hQ in
/-- **Lemma 3.15 (i)** (Shimura 2004, p. 27): for $\alpha \in G'(V)$ with $\Psi(\alpha)$ having rows $(a, b)$ and
$(c, d)$: $xy^* = yx^* \in U$ and $x^*y = y^*x \in U$ for $(x, y) = (a, b), (a, c), (d, b), (d, c)$. -/
@[kb "shimura2004" "Lemma 3.15 (i), p. 27 (xy* = yx* ∈ U and x*y = y*x ∈ U for (x, y) = (a, b), (a, c), (d, b), (d, c))"]
theorem lemma_3_15_i (α : homogeneousCliffordGroup Q) :
    let ξ := psi he hf hef ((α : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
    PairProp Q e f (ξ 0 0) (ξ 0 1) ∧ PairProp Q e f (ξ 0 0) (ξ 1 0) ∧ PairProp Q e f (ξ 1 1) (ξ 0 1) ∧
      PairProp Q e f (ξ 1 1) (ξ 1 0) := by
  intro ξ
  obtain ⟨⟨hdc, -, -, hcd⟩, ⟨hba, -, -, hab⟩, ⟨hac, -, -, hca⟩, ⟨hbd, -, -, hdb⟩⟩ := step_conj he hf hef hQ α
  have h39 := formula_3_9 (⟨psiUnits he hf hef (α : (CliffordAlgebra Q)ˣ), psi_mem_matGroup he hf hef hQ α⟩ :
    matGroup (QU Q e f))
  obtain ⟨-, -, h_ab, h_cd, h_ac, h_bd⟩ := h39
  change ξ 0 0 * reverse (ξ 0 1) = ξ 0 1 * reverse (ξ 0 0) at h_ab
  change ξ 1 0 * reverse (ξ 1 1) = ξ 1 1 * reverse (ξ 1 0) at h_cd
  change reverse (ξ 0 0) * ξ 1 0 = reverse (ξ 1 0) * ξ 0 0 at h_ac
  change reverse (ξ 0 1) * ξ 1 1 = reverse (ξ 1 1) * ξ 0 1 at h_bd
  set m : F := ((muHom hQ α : Fˣ) : F)
  have hm : m⁻¹ ≠ 0 := inv_ne_zero (Units.ne_zero _)
  have hinv := psi_inv_eq he hf hef hQ α
  -- $cd^* \in U$ for $\alpha$, $\kappa\alpha$, $\alpha^{-1}$, $\kappa\alpha^{-1}$
  have v1 : IsVecU Q e f (ξ 1 0 * reverse (ξ 1 1)) := step_cd he hf hef hQ α
  have v2 : IsVecU Q e f (ξ 0 0 * reverse (ξ 0 1)) := by
    have := step_cd he hf hef hQ (kappaH he hf hef * α)
    simpa [psi_kappaH_mul] using this
  have v3 : IsVecU Q e f (reverse (ξ 1 0) * ξ 0 0) := by
    have := step_cd he hf hef hQ α⁻¹
    rw [hinv] at this
    simp only [adjU, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const,
      map_smul, map_neg, reverse_reverse, smul_mul_smul_comm, neg_mul] at this
    exact (IsVecU.of_smul (mul_ne_zero hm hm) this).of_neg
  have v4 : IsVecU Q e f (reverse (ξ 1 1) * ξ 0 1) := by
    have := step_cd he hf hef hQ (kappaH he hf hef * α⁻¹)
    rw [Subgroup.coe_mul, Units.val_mul, psi_kappaH_mul, hinv] at this
    simp only [adjU, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const,
      map_smul, map_neg, reverse_reverse, smul_mul_smul_comm, mul_neg] at this
    exact (IsVecU.of_smul (mul_ne_zero hm hm) this).of_neg
  refine ⟨⟨h_ab, v2, hab, ?_⟩, ⟨hca.symm, hac, h_ac, ?_⟩, ⟨hdb, ?_, h_bd.symm, ?_⟩, ⟨h_cd.symm, ?_, hcd.symm, hdc⟩⟩
  · rw [hab]; exact hba
  · rw [h_ac]; exact v3
  · rw [hdb]; exact hbd
  · exact v4
  · rw [← h_cd]; exact v1

include hQ in
/-- **Lemma 3.15 (ii)** (Shimura 2004, p. 27): for $\alpha \in G'(V)$, every entry $x$ of $\Psi(\alpha)$ satisfies
$xx^* = x^*x \in F$ and $xUx^* \subseteq U$. -/
@[kb "shimura2004" "Lemma 3.15 (ii), p. 27 (xx* = x*x ∈ F and xUx* ⊂ U for x = a, b, c, d)"]
theorem lemma_3_15_ii (α : homogeneousCliffordGroup Q) (i j : Fin 2) :
    EntryProp Q e f (psi he hf hef ((α : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) i j) := by
  obtain ⟨⟨-, hdd, hcc, -⟩, ⟨-, hbb, haa, -⟩, ⟨-, haa', hcc', -⟩, ⟨-, hbb', hdd', -⟩⟩ :=
    step_conj he hf hef hQ α
  refine ⟨?_, ?_, fun u => step_conj_U he hf hef hQ α u i j⟩ <;> fin_cases i <;> fin_cases j
  · exact mul_reverse_comm_of_scalar haa' haa
  · exact mul_reverse_comm_of_scalar hbb' hbb
  · exact mul_reverse_comm_of_scalar hcc' hcc
  · exact mul_reverse_comm_of_scalar hdd' hdd
  · exact haa'
  · exact hbb'
  · exact hcc'
  · exact hdd'

include hQ in
/-- **Lemma 3.15 (iii)** (Shimura 2004, p. 27): an entry of $\Psi(\alpha)$, $\alpha \in G'(V)$, that is
invertible lies in $G'(U)$. -/
@[kb "shimura2004" "Lemma 3.15 (iii), p. 27 (any one of a, b, c, d, if invertible, belongs to G'(U))"]
theorem lemma_3_15_iii (α : homogeneousCliffordGroup Q) (i j : Fin 2)
    (hx : IsUnit (psi he hf hef ((α : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) i j)) :
    hx.unit ∈ homogeneousCliffordGroup (QU Q e f) := by
  obtain ⟨-, hs, hv⟩ := lemma_3_15_ii he hf hef hQ α i j
  refine mem_homogeneous_of hx ?_ hs hv
  rcases α.2.2 with h | h
  · obtain ⟨h00, h01, h10, h11⟩ := (psi_mem_evenOdd_zero_iff he hf hef _).1 h
    fin_cases i <;> fin_cases j
    · exact Or.inl h00
    · exact Or.inr h01
    · exact Or.inr h10
    · exact Or.inl h11
  · obtain ⟨h00, h01, h10, h11⟩ := (psi_mem_evenOdd_one_iff he hf hef _).1 h
    fin_cases i <;> fin_cases j
    · exact Or.inr h00
    · exact Or.inl h01
    · exact Or.inl h10
    · exact Or.inr h11

end Hyp

end MatrixModel

end QuadFormsKB.Shimura2004
