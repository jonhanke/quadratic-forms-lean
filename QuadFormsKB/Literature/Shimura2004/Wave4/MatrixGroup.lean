/-
# Shimura 2004, §3.9: the group $\mathcal G(V)$ of $2\times2$ matrices and $\Psi(G'(V)) \subseteq \mathcal G(U)$

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Chapter I, §3.9, formulas
(3.8)–(3.10) (printed pp. 24–25). Page numbers in the tags are printed pages.

**Setting and dictionary.** As in `Wave4/MatrixModel.lean`. For a quadratic space $(W, \psi)$ over $F$ (here any
`Q' : QuadraticForm F W`) and $\xi \in M_2(A(W))$, $\xi^*$ is the transpose with the canonical involution applied to
every entry (`matStar`) and $J = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$ (`matJ`). Shimura's group (3.8) is
$$\mathcal G(W) = \{\xi \in GL_2(A(W)) : \xi^*J\xi = \mu_\xi J \text{ with } \mu_\xi \in F^\times\},$$
here `matGroup Q'`, a subgroup of the units of `Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q')`, with
$\xi \mapsto \mu_\xi$ the homomorphism `matMu Q'`. Write $\xi = \begin{pmatrix} a & b \\ c & d\end{pmatrix}$, i.e.
$a, b, c, d$ = `ξ 0 0`, `ξ 0 1`, `ξ 1 0`, `ξ 1 1`.

**Defines**
* (3.8) $\mathcal G(W)$ (`matGroup`), and $\mu_\xi$ (`matMu`, a homomorphism to $F^\times$).

**Proves** (all unconditional; standard axioms only)
* (3.8), remark: the same group is defined with $\xi J\xi^*$ in place of $\xi^*J\xi$ (`mem_matGroup_iff'`,
  `mul_matJ_matStar_of_mem`);
* (3.9): for $\xi \in \mathcal G$, $ad^* - bc^* = d^*a - b^*c = \mu_\xi$, $ab^* = ba^*$, $cd^* = dc^*$,
  $a^*c = c^*a$, $b^*d = d^*b$ (`formula_3_9`);
* (3.9a): $\xi^{-1} = \mu_\xi^{-1}\begin{pmatrix} d^* & -b^* \\ -c^* & a^*\end{pmatrix}$ (`formula_3_9a`);
* (3.10): for a weak Witt decomposition $V = U + Fe + Ff$ and $a \in G'(V)$, $\Psi(a) \in \mathcal G(U)$ with
  $\mu_{\Psi(a)} = \mu(a)$, which is $\pm\nu(a)$ for $a \in G^\pm(V)$ (`psi_mem_matGroup`, `matMu_psi`,
  `matMu_psi_of_mem_M0`, `matMu_psi_of_mem_odd`); here $\mu$ is the homomorphism of (3.21), `muHom`.
-/
import QuadFormsKB.Literature.Shimura2004.Wave4.MatrixModel
import QuadFormsKB.Citation

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Cassels QuadFormsKB.OMeara

namespace MatrixModel

variable {F : Type*} [Field F] [Invertible (2 : F)]

section General

variable {W : Type*} [AddCommGroup W] [Module F W] (Q' : QuadraticForm F W)

local notation "M₂" => Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q')

variable {Q'}

theorem matStar_one : matStar (1 : M₂) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matStar]

theorem matStar_neg (X : M₂) : matStar (-X) = -matStar X := by
  ext i j; simp [matStar]

theorem matStar_smul (c : F) (X : M₂) : matStar (c • X) = c • matStar X := by
  ext i j; simp [matStar]

/-- $\xi^*$ of a unit is a unit, with inverse $(\xi^{-1})^*$. -/
def unitStar (ξ : M₂ˣ) : M₂ˣ where
  val := matStar (ξ : M₂)
  inv := matStar ((ξ⁻¹ : M₂ˣ) : M₂)
  val_inv := by rw [← matStar_mul, ξ.inv_mul, matStar_one]
  inv_val := by rw [← matStar_mul, ξ.mul_inv, matStar_one]

theorem matJ_mul_matJ {R : Type*} [Ring R] : (matJ : Matrix (Fin 2) (Fin 2) R) * matJ = -1 := by
  have h := (matJ_mul_neg_matJ : (matJ : Matrix (Fin 2) (Fin 2) R) * -matJ = 1)
  rw [mul_neg, neg_eq_iff_eq_neg] at h
  exact h

/-- If $\xi$ is invertible and $\xi^*J\xi = cJ$, then $\xi J \xi^* = cJ$ (Shimura's remark after (3.8)). -/
theorem mul_matJ_matStar_of (ξ : M₂ˣ) (c : F) (h : matStar (ξ : M₂) * matJ * (ξ : M₂) = c • matJ) :
    (ξ : M₂) * matJ * matStar (ξ : M₂) = c • matJ := by
  set X : M₂ := -matJ * matStar (ξ : M₂) * matJ with hX
  have h1 : X * ξ = c • (1 : M₂) := by
    have : -matJ * matStar (ξ : M₂) * matJ * (ξ : M₂) = -matJ * (matStar (ξ : M₂) * matJ * (ξ : M₂)) := by
      simp only [mul_assoc]
    rw [hX, this, h, Matrix.mul_smul, neg_matJ_mul_matJ]
  have h2 : X = c • ((ξ⁻¹ : M₂ˣ) : M₂) := by
    calc X = X * ξ * ((ξ⁻¹ : M₂ˣ) : M₂) := by rw [mul_assoc, ξ.mul_inv, mul_one]
      _ = c • ((ξ⁻¹ : M₂ˣ) : M₂) := by rw [h1, Matrix.smul_mul, one_mul]
  have h3 : (ξ : M₂) * X = c • (1 : M₂) := by rw [h2, Matrix.mul_smul, ξ.mul_inv]
  -- $\xi (-J \xi^* J) = c$, so $\xi J \xi^* = \xi J \xi^* J (-J) = -c(-J)$
  calc (ξ : M₂) * matJ * matStar (ξ : M₂)
      = -((ξ : M₂) * X) * -matJ := by
        rw [hX]
        simp only [neg_mul, mul_neg, neg_neg, mul_assoc, matJ_mul_matJ, mul_one]
    _ = c • matJ := by rw [h3, neg_mul_neg, Matrix.smul_mul, one_mul]

/-- The converse of `mul_matJ_matStar_of`: if $\xi J\xi^* = cJ$ then $\xi^*J\xi = cJ$. -/
theorem matStar_mul_matJ_of (ξ : M₂ˣ) (c : F) (h : (ξ : M₂) * matJ * matStar (ξ : M₂) = c • matJ) :
    matStar (ξ : M₂) * matJ * (ξ : M₂) = c • matJ := by
  have := mul_matJ_matStar_of (unitStar ξ) c (by simpa [unitStar, matStar_matStar] using h)
  simpa [unitStar, matStar_matStar] using this

/-- $\mu J = \mu' J$ forces $\mu = \mu'$. -/
theorem smul_matJ_injective : Function.Injective (fun c : F => c • (matJ : M₂)) := by
  intro c c' h
  have := congrArg (fun M : M₂ => M 1 0) h
  simp only [matJ, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one] at this
  rw [Algebra.smul_def, Algebra.smul_def, mul_one, mul_one] at this
  exact (algebraMap F (CliffordAlgebra Q')).injective this

variable (Q') in
/-- **Shimura's group $\mathcal G(W)$** (3.8), p. 24: the invertible $\xi \in GL_2(A(W))$ with
$\xi^*J\xi = \mu_\xi J$ for some $\mu_\xi \in F^\times$. -/
@[kb "shimura2004" "(3.8), p. 24 (𝒢(V) = {ξ ∈ GL₂(A(V)) | ξ*Jξ = μ_ξ J, μ_ξ ∈ F^×})"]
def matGroup : Subgroup M₂ˣ where
  carrier := {ξ | ∃ μ : Fˣ, matStar (ξ : M₂) * matJ * (ξ : M₂) = (μ : F) • matJ}
  one_mem' := ⟨1, by rw [Units.val_one, matStar_one, one_mul, mul_one, Units.val_one, one_smul]⟩
  mul_mem' := by
    rintro ξ η ⟨μ, hμ⟩ ⟨μ', hμ'⟩
    refine ⟨μ * μ', ?_⟩
    simp only [Units.val_mul, matStar_mul]
    calc matStar (η : M₂) * matStar (ξ : M₂) * matJ * ((ξ : M₂) * (η : M₂))
        = matStar (η : M₂) * (matStar (ξ : M₂) * matJ * (ξ : M₂)) * (η : M₂) := by simp only [mul_assoc]
      _ = (μ : F) • (matStar (η : M₂) * matJ * (η : M₂)) := by
        rw [hμ, Matrix.mul_smul, Matrix.smul_mul]
      _ = ((μ : F) * μ') • matJ := by rw [hμ', smul_smul]
  inv_mem' := by
    rintro ξ ⟨μ, hμ⟩
    refine ⟨μ⁻¹, ?_⟩
    have hs : matStar ((ξ⁻¹ : M₂ˣ) : M₂) * matStar (ξ : M₂) = 1 := by
      rw [← matStar_mul, ξ.mul_inv, matStar_one]
    calc matStar ((ξ⁻¹ : M₂ˣ) : M₂) * matJ * ((ξ⁻¹ : M₂ˣ) : M₂)
        = matStar ((ξ⁻¹ : M₂ˣ) : M₂) * (((μ⁻¹ : Fˣ) : F) • (matStar (ξ : M₂) * matJ * (ξ : M₂))) *
            ((ξ⁻¹ : M₂ˣ) : M₂) := by
          rw [hμ, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
      _ = ((μ⁻¹ : Fˣ) : F) • ((matStar ((ξ⁻¹ : M₂ˣ) : M₂) * matStar (ξ : M₂)) * matJ *
            ((ξ : M₂) * ((ξ⁻¹ : M₂ˣ) : M₂))) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]; simp only [mul_assoc]
      _ = ((μ⁻¹ : Fˣ) : F) • matJ := by rw [hs, ξ.mul_inv, one_mul, mul_one]

theorem mem_matGroup_iff (ξ : M₂ˣ) :
    ξ ∈ matGroup Q' ↔ ∃ μ : Fˣ, matStar (ξ : M₂) * matJ * (ξ : M₂) = (μ : F) • matJ := Iff.rfl

/-- (3.8), p. 24, remark: "the same group can be defined with $\xi J\xi^*$ in place of $\xi^*J\xi$". -/
@[kb "shimura2004" "(3.8), p. 24 (the same group can be defined with ξJξ* in place of ξ*Jξ)"]
theorem mem_matGroup_iff' (ξ : M₂ˣ) :
    ξ ∈ matGroup Q' ↔ ∃ μ : Fˣ, (ξ : M₂) * matJ * matStar (ξ : M₂) = (μ : F) • matJ :=
  ⟨fun ⟨μ, h⟩ => ⟨μ, mul_matJ_matStar_of ξ μ h⟩, fun ⟨μ, h⟩ => ⟨μ, matStar_mul_matJ_of ξ μ h⟩⟩

theorem exists_unique_mu (ξ : matGroup Q') :
    ∃! μ : Fˣ, matStar ((ξ : M₂ˣ) : M₂) * matJ * ((ξ : M₂ˣ) : M₂) = (μ : F) • matJ := by
  obtain ⟨μ, hμ⟩ := ξ.2
  refine ⟨μ, hμ, fun μ' hμ' => Units.ext (smul_matJ_injective (Q' := Q') ?_)⟩
  simp only
  rw [← hμ', hμ]

theorem mu_mul_aux (ξ η : matGroup Q') (a b : Fˣ)
    (ha : matStar ((ξ : M₂ˣ) : M₂) * matJ * ((ξ : M₂ˣ) : M₂) = (a : F) • matJ)
    (hb : matStar ((η : M₂ˣ) : M₂) * matJ * ((η : M₂ˣ) : M₂) = (b : F) • matJ) :
    matStar (((ξ * η : matGroup Q') : M₂ˣ) : M₂) * matJ * (((ξ * η : matGroup Q') : M₂ˣ) : M₂) =
      ((a * b : Fˣ) : F) • matJ := by
  simp only [Subgroup.coe_mul, Units.val_mul, matStar_mul]
  calc matStar ((η : M₂ˣ) : M₂) * matStar ((ξ : M₂ˣ) : M₂) * matJ * (((ξ : M₂ˣ) : M₂) * ((η : M₂ˣ) : M₂))
      = matStar ((η : M₂ˣ) : M₂) * (matStar ((ξ : M₂ˣ) : M₂) * matJ * ((ξ : M₂ˣ) : M₂)) * ((η : M₂ˣ) : M₂) := by
        simp only [mul_assoc]
    _ = _ := by
      rw [ha, Matrix.mul_smul, Matrix.smul_mul, hb, smul_smul]

variable (Q') in
/-- **$\mu_\xi$** (3.8), p. 24: the scalar with $\xi^*J\xi = \mu_\xi J$, as a homomorphism
$\mathcal G(W) \to F^\times$. -/
@[kb "shimura2004" "(3.8), p. 24 (μ_ξ ∈ F^× with ξ*Jξ = μ_ξ J)"]
def matMu : matGroup Q' →* Fˣ where
  toFun ξ := (exists_unique_mu ξ).choose
  map_one' := by
    have h := (exists_unique_mu (1 : matGroup Q')).choose_spec
    exact ((exists_unique_mu (1 : matGroup Q')).unique h.1 (by simp [matStar_one])).trans rfl
  map_mul' ξ η := (exists_unique_mu (ξ * η)).unique (exists_unique_mu (ξ * η)).choose_spec.1
    (mu_mul_aux ξ η _ _ (exists_unique_mu ξ).choose_spec.1 (exists_unique_mu η).choose_spec.1)

theorem matMu_spec (ξ : matGroup Q') :
    matStar ((ξ : M₂ˣ) : M₂) * matJ * ((ξ : M₂ˣ) : M₂) = ((matMu Q' ξ : Fˣ) : F) • matJ :=
  (exists_unique_mu ξ).choose_spec.1

theorem matMu_eq_of (ξ : matGroup Q') (μ : Fˣ)
    (h : matStar ((ξ : M₂ˣ) : M₂) * matJ * ((ξ : M₂ˣ) : M₂) = (μ : F) • matJ) : matMu Q' ξ = μ :=
  ((exists_unique_mu ξ).unique (matMu_spec ξ) h)

/-- The entries of $\xi^*J\eta$. -/
theorem matStar_matJ_mul (X Y : M₂) : matStar X * matJ * Y =
    !![reverse (X 1 0) * Y 0 0 - reverse (X 0 0) * Y 1 0, reverse (X 1 0) * Y 0 1 - reverse (X 0 0) * Y 1 1;
      reverse (X 1 1) * Y 0 0 - reverse (X 0 1) * Y 1 0, reverse (X 1 1) * Y 0 1 - reverse (X 0 1) * Y 1 1] := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, matJ, matStar, Matrix.map_apply, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp [sub_eq_add_neg]

/-- The entries of $\xi J\eta^*$. -/
theorem mul_matJ_matStar (X Y : M₂) : X * matJ * matStar Y =
    !![X 0 1 * reverse (Y 0 0) - X 0 0 * reverse (Y 0 1), X 0 1 * reverse (Y 1 0) - X 0 0 * reverse (Y 1 1);
      X 1 1 * reverse (Y 0 0) - X 1 0 * reverse (Y 0 1), X 1 1 * reverse (Y 1 0) - X 1 0 * reverse (Y 1 1)] := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, matJ, matStar, Matrix.map_apply, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp [sub_eq_add_neg]

/-- **(3.9)**, p. 24: for $\xi = \begin{pmatrix} a & b \\ c & d\end{pmatrix} \in \mathcal G$:
$ad^* - bc^* = d^*a - b^*c = \mu_\xi$, $ab^* = ba^*$, $cd^* = dc^*$, $a^*c = c^*a$, $b^*d = d^*b$. -/
@[kb "shimura2004" "(3.9), p. 24 (ad* − bc* = d*a − b*c = μ_ξ, ab* = ba*, cd* = dc*, a*c = c*a, b*d = d*b)"]
theorem formula_3_9 (ξ : matGroup Q') :
    let x : M₂ := ((ξ : M₂ˣ) : M₂)
    let μ : CliffordAlgebra Q' := algebraMap F _ ((matMu Q' ξ : Fˣ) : F)
    x 0 0 * reverse (x 1 1) - x 0 1 * reverse (x 1 0) = μ ∧
      reverse (x 1 1) * x 0 0 - reverse (x 0 1) * x 1 0 = μ ∧
      x 0 0 * reverse (x 0 1) = x 0 1 * reverse (x 0 0) ∧ x 1 0 * reverse (x 1 1) = x 1 1 * reverse (x 1 0) ∧
      reverse (x 0 0) * x 1 0 = reverse (x 1 0) * x 0 0 ∧
      reverse (x 0 1) * x 1 1 = reverse (x 1 1) * x 0 1 := by
  intro x μ
  have h1 := matMu_spec ξ
  have h2 := mul_matJ_matStar_of (ξ : M₂ˣ) _ h1
  rw [matStar_matJ_mul] at h1
  rw [mul_matJ_matStar] at h2
  have e1 := congrArg (fun M : M₂ => M 0 0) h1
  have e2 := congrArg (fun M : M₂ => M 1 0) h1
  have e3 := congrArg (fun M : M₂ => M 1 1) h1
  have f1 := congrArg (fun M : M₂ => M 0 0) h2
  have f2 := congrArg (fun M : M₂ => M 0 1) h2
  have f3 := congrArg (fun M : M₂ => M 1 1) h2
  simp only [matJ, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, smul_zero,
    Algebra.smul_def, mul_one, mul_neg, mul_zero] at e1 e2 e3 f1 f2 f3
  refine ⟨?_, e2, ?_, ?_, ?_, ?_⟩
  · rw [← neg_sub, f2, neg_neg]
  · exact (sub_eq_zero.1 f1).symm
  · exact (sub_eq_zero.1 f3).symm
  · exact (sub_eq_zero.1 e1).symm
  · exact (sub_eq_zero.1 e3).symm

/-- **(3.9a)**, p. 25: $\xi^{-1} = \mu_\xi^{-1}\begin{pmatrix} d^* & -b^* \\ -c^* & a^*\end{pmatrix}$ for
$\xi = \begin{pmatrix} a & b \\ c & d\end{pmatrix} \in \mathcal G$. -/
@[kb "shimura2004" "(3.9a), p. 25 (ξ⁻¹ = μ_ξ⁻¹ [[d*, −b*], [−c*, a*]])"]
theorem formula_3_9a (ξ : matGroup Q') :
    (((ξ : M₂ˣ)⁻¹ : M₂ˣ) : M₂) = (((matMu Q' ξ)⁻¹ : Fˣ) : F) •
      !![reverse (((ξ : M₂ˣ) : M₂) 1 1), -reverse (((ξ : M₂ˣ) : M₂) 0 1);
        -reverse (((ξ : M₂ˣ) : M₂) 1 0), reverse (((ξ : M₂ˣ) : M₂) 0 0)] := by
  set x : M₂ := ((ξ : M₂ˣ) : M₂)
  have h1 := matMu_spec ξ
  -- $-J\xi^*J \cdot \xi = \mu$
  have hX : (-matJ * matStar x * matJ) * x = ((matMu Q' ξ : Fˣ) : F) • (1 : M₂) := by
    rw [mul_assoc (-matJ * _), mul_assoc (-matJ), ← mul_assoc (matStar _), h1, Matrix.mul_smul,
      neg_matJ_mul_matJ]
  have hJ : -matJ * matStar x * matJ = !![reverse (x 1 1), -reverse (x 0 1); -reverse (x 1 0),
      reverse (x 0 0)] := by
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two, matJ, matStar, Matrix.map_apply, Matrix.transpose_apply,
      Matrix.neg_apply]
    fin_cases i <;> fin_cases j <;> simp
  calc (((ξ : M₂ˣ)⁻¹ : M₂ˣ) : M₂)
      = (((matMu Q' ξ)⁻¹ : Fˣ) : F) • ((((matMu Q' ξ : Fˣ) : F) • (1 : M₂)) *
          (((ξ : M₂ˣ)⁻¹ : M₂ˣ) : M₂)) := by
        rw [Matrix.smul_mul, one_mul, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    _ = _ := by
        rw [← hX, mul_assoc, (ξ : M₂ˣ).mul_inv, mul_one, hJ]

end General

/-! ### (3.10): $\Psi(G'(V)) \subseteq \mathcal G(U)$ -/

variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V} {e f : V}
  (he : Q e = 0) (hf : Q f = 0) (hef : QuadraticMap.polar Q e f = 1)
  (hQ : (QuadraticMap.associated Q).Nondegenerate)

/-- $\Psi$ maps units to units. -/
def psiUnits : (CliffordAlgebra Q)ˣ →* (Matrix (Fin 2) (Fin 2) (AU Q e f))ˣ :=
  Units.map (psi he hf hef).toMonoidHom

include he hf hef in
/-- The key identity behind (3.10): $\Psi(a)^*J\Psi(a) = \mu(a)J$ for $a \in G'(V)$, where $\mu(a) = a'a^*$
(3.21). -/
theorem psi_star_matJ_psi (a : homogeneousCliffordGroup Q) :
    matStar (psi he hf hef ((a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) * matJ *
        psi he hf hef ((a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      ((muHom hQ a : Fˣ) : F) • matJ := by
  set α : CliffordAlgebra Q := ((a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
  -- $\alpha'\alpha^* = \mu$, so $\Psi(\alpha')J\Psi(\alpha')^* = \mu J$ by (2.10)
  have hmu := algebraMap_muHom hQ a
  have h1 : psi he hf hef (involute α) * matJ * matStar (psi he hf hef (involute α)) =
      ((muHom hQ a : Fˣ) : F) • matJ := by
    have := congrArg (psi he hf hef) hmu
    rw [AlgHom.commutes, map_mul, psi_reverse] at this
    -- $\Psi(\alpha')\,J\,\Psi(\alpha')^*\,(-J) = \mu$
    have h2 := congrArg (· * matJ) this
    rw [mul_assoc, mul_assoc, neg_matJ_mul_matJ, mul_one, ← mul_assoc, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mul, one_mul] at h2
    exact h2.symm
  -- $\alpha' = \pm\alpha$
  have hunit : IsUnit (psi he hf hef (involute α)) :=
    ((Units.map (involute : CliffordAlgebra Q →ₐ[F] CliffordAlgebra Q).toMonoidHom
      (a : (CliffordAlgebra Q)ˣ)).isUnit.map (psi he hf hef))
  have h3 := matStar_mul_matJ_of hunit.unit _ h1
  simp only [IsUnit.unit_spec] at h3
  rcases a.2.2 with h | h
  · rwa [involute_eq_of_mem_even h] at h3
  · rwa [involute_eq_of_mem_odd h, map_neg, matStar_neg, neg_mul, mul_neg, neg_mul, neg_neg] at h3

include he hf hef hQ in
/-- **(3.10)**, p. 25: $\Psi(G'(V)) \subseteq \mathcal G(U)$. -/
@[kb "shimura2004" "(3.10), p. 25 (Ψ(G'(V)) ⊂ 𝒢(U))"]
theorem psi_mem_matGroup (a : homogeneousCliffordGroup Q) :
    psiUnits he hf hef (a : (CliffordAlgebra Q)ˣ) ∈ matGroup (QU Q e f) :=
  ⟨muHom hQ a, psi_star_matJ_psi he hf hef hQ a⟩

include he hf hef in
/-- **(3.10)**, p. 25: $\mu_\xi = \mu(a)$ for $\xi = \Psi(a)$, $a \in G'(V)$, with $\mu$ of (3.21). -/
@[kb "shimura2004" "(3.10), p. 25 (μ_ξ = ±ν(a) if ξ = Ψ(a), a ∈ G^±(V))"]
theorem matMu_psi (a : homogeneousCliffordGroup Q) :
    matMu (QU Q e f) ⟨psiUnits he hf hef (a : (CliffordAlgebra Q)ˣ), psi_mem_matGroup he hf hef hQ a⟩ =
      muHom hQ a :=
  matMu_eq_of _ _ (psi_star_matJ_psi he hf hef hQ a)

include he hf hef in
/-- **(3.10)**, p. 25: $\mu_{\Psi(a)} = \nu(a)$ for $a \in G^+(V)$. -/
@[kb "shimura2004" "(3.10), p. 25 (μ_ξ = ±ν(a) if ξ = Ψ(a), a ∈ G^±(V))"]
theorem matMu_psi_of_mem_M0 (a : homogeneousCliffordGroup Q) (h : (a : (CliffordAlgebra Q)ˣ) ∈ M0 Q) :
    matMu (QU Q e f) ⟨psiUnits he hf hef (a : (CliffordAlgebra Q)ˣ), psi_mem_matGroup he hf hef hQ a⟩ =
      multiplier hQ a := by
  rw [matMu_psi he hf hef hQ a, muHom_of_mem_M0 hQ a h]

include he hf hef in
/-- **(3.10)**, p. 25: $\mu_{\Psi(a)} = -\nu(a)$ for $a \in G^-(V)$. -/
@[kb "shimura2004" "(3.10), p. 25 (μ_ξ = ±ν(a) if ξ = Ψ(a), a ∈ G^±(V))"]
theorem matMu_psi_of_mem_odd (a : homogeneousCliffordGroup Q) (h : (a : (CliffordAlgebra Q)ˣ) ∈ cliffordGroupOdd Q) :
    matMu (QU Q e f) ⟨psiUnits he hf hef (a : (CliffordAlgebra Q)ˣ), psi_mem_matGroup he hf hef hQ a⟩ =
      -multiplier hQ a := by
  rw [matMu_psi he hf hef hQ a, muHom_of_mem_odd hQ a h]

end MatrixModel

end QuadFormsKB.Shimura2004
