/-
# Shimura 2004, §7.4 (B): the Clifford algebra of $(B, d\,xx^\iota)$ is $M_2(B)$

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), §7.4 (B), formulas (7.4a),
(7.4b), (7.5a), (7.5b) (printed pp. 54–55). Page numbers in the tags are printed pages.

**Setting and dictionary.** $F$ is a field of characteristic $\ne 2$ (`Invertible (2 : F)`). Shimura takes a
quaternion algebra $B$ over $F$ with main involution $x \mapsto x^\iota$ and $d \in F^\times$, and the quadratic form
$\varphi[x] = d\,xx^\iota$ on $Z = B$. Here $B$ is Mathlib's `ℍ[F, c₀, c₁]` (`QuaternionAlgebra F c₀ 0 c₁`: basis
$1, i, j, k = ij$ with $i^2 = c_0$, $j^2 = c_1$, $ij = -ji$), with $c_0c_1 \ne 0$, and $x^\iota$ is `star x`.
*Restriction:* every quaternion algebra over a field of characteristic $\ne 2$ has this form, but that
classification is not in Mathlib, so the results are stated for $B$ given in this standard form.
The reduced norm $N(x) = xx^\iota$ is `nrd x`
($= x_0^2 - c_0x_1^2 - c_1x_2^2 + c_0c_1x_3^2$ in the coordinates $x = x_0 + x_1i + x_2j + x_3k$), and $\varphi$ is
`quatForm c₀ c₁ d` with `quatForm c₀ c₁ d x = d * nrd x`. As in `CliffordGroups.lean`: $A(Z)$ = `CliffordAlgebra φ`,
$A^+(Z)$ = `evenOdd φ 0`, $a \mapsto a^*$ = `reverse`, $G^+(Z)$ = `M0 φ`, $G^1(Z)$ = `spinGroupG1 φ`, $\nu$ =
`multiplier`, $\tau$ = `tau` (with $x\tau(a) = a^{-1}xa$, written `tau a x`). Matrix indices are 0-based: the
entries of $\begin{pmatrix} p & q \\ r & s \end{pmatrix}$ are `M 0 0 = p`, `M 0 1 = q`, `M 1 0 = r`, `M 1 1 = s`.

**Proves** (all unconditional; standard axioms only)
* (7.4a): $\rho(x) = \begin{pmatrix} 0 & x \\ dx^\iota & 0 \end{pmatrix}$ satisfies $\rho(x)^2 = \varphi[x]$
  (`rho_mul_self`), and $\rho(B)$ generates $M_2(B)$ (`lift_rho_surjective`);
* (7.4b): the $F$-algebra homomorphism $A(Z) \to M_2(B)$ extending $\rho$ is an isomorphism (`cliffordEquiv`,
  `cliffordEquiv_ι`, headline `exists_cliffordEquiv`), so $A(Z) = M_2(B)$ with $Z = \rho(B)$;
* $A^+(Z) = \{\mathrm{diag}[a, b] \mid a, b \in B\}$ (`evenOdd_zero_iff`);
* the involution: $\begin{pmatrix} p & q \\ r & s \end{pmatrix}^* =
  \begin{pmatrix} p^\iota & d^{-1}r^\iota \\ dq^\iota & s^\iota \end{pmatrix}$ (`cliffordEquiv_reverse`);
* (7.5a): $G^+(Z) = \{(a, b) \in B^\times \times B^\times \mid aa^\iota = bb^\iota\}$ (`mem_M0_iff`,
  `exists_mem_M0_of_nrd_eq`), $\nu((a, b)) = aa^\iota$ (`multiplier_eq_nrd`);
* (7.5b): $G^1(Z) = \{(a, b) \mid aa^\iota = bb^\iota = 1\}$ (`mem_spinGroupG1_iff`);
* $\rho(x)\tau(\alpha) = \rho(a^{-1}xb)$ for $\alpha = (a, b) \in G^+(Z)$ (`tau_eq`), and for
  $\eta = \rho(1)$, $\rho(x)\tau(\eta) = \rho(x^\iota)$ (`tau_eta`);
* the main involution $\iota$ of $B$ lies in $O^\varphi$ and has determinant $-1$, so $O^\varphi = SO^\varphi \cup
  SO^\varphi\iota$ (`orth_eq_orthPlus_or_mul_star`, `det_starEquiv`).
-/
import QuadFormsKB.Literature.Shimura2004.Wave6.Dim3
import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Matrix.Notation
import QuadFormsKB.Citation

open Module CliffordAlgebra Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Cassels QuadFormsKB.OMeara

namespace QuatModel

variable {F : Type*} [Field F] {c₀ c₁ : F}

/-! ### The reduced norm and the form $\varphi[x] = d\,xx^\iota$ -/

/-- The reduced norm $N(x) = xx^\iota = x_0^2 - c_0x_1^2 - c_1x_2^2 + c_0c_1x_3^2$ of $x = x_0 + x_1i + x_2j + x_3k$
in $B = (c_0, c_1)_F$ = `ℍ[F, c₀, c₁]`. -/
def nrd (x : ℍ[F, c₀, c₁]) : F :=
  x.re ^ 2 - c₀ * x.imI ^ 2 - c₁ * x.imJ ^ 2 + c₀ * c₁ * x.imK ^ 2

theorem mul_star_eq_nrd (x : ℍ[F, c₀, c₁]) : x * star x = ((nrd x : F) : ℍ[F, c₀, c₁]) := by
  ext <;> simp [nrd, -QuaternionAlgebra.coe_sub, -QuaternionAlgebra.coe_add, -QuaternionAlgebra.coe_mul,
    -QuaternionAlgebra.coe_pow] <;> ring

theorem star_mul_eq_nrd (x : ℍ[F, c₀, c₁]) : star x * x = ((nrd x : F) : ℍ[F, c₀, c₁]) := by
  ext <;> simp [nrd, -QuaternionAlgebra.coe_sub, -QuaternionAlgebra.coe_add, -QuaternionAlgebra.coe_mul,
    -QuaternionAlgebra.coe_pow] <;> ring

theorem nrd_mul (x y : ℍ[F, c₀, c₁]) : nrd (x * y) = nrd x * nrd y := by
  simp only [nrd, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul]
  ring

theorem nrd_star (x : ℍ[F, c₀, c₁]) : nrd (star x) = nrd x := by
  simp [nrd]

variable (c₀ c₁) in
/-- The quadratic form $\varphi[x] = d\,xx^\iota$ on $B$ (Shimura §7.4 (B)). -/
def quatForm (d : F) : QuadraticForm F ℍ[F, c₀, c₁] :=
  d • (QuadraticMap.sq.comp (QuaternionAlgebra.reₗ c₀ 0 c₁)
    - c₀ • QuadraticMap.sq.comp (QuaternionAlgebra.imIₗ c₀ 0 c₁)
    - c₁ • QuadraticMap.sq.comp (QuaternionAlgebra.imJₗ c₀ 0 c₁)
    + (c₀ * c₁) • QuadraticMap.sq.comp (QuaternionAlgebra.imKₗ c₀ 0 c₁))

theorem quatForm_apply (d : F) (x : ℍ[F, c₀, c₁]) : quatForm c₀ c₁ d x = d * nrd x := by
  simp [quatForm, nrd, sq]; ring

/-! ### The map $\rho$ of (7.4a) -/

local notation "M₂" => Matrix (Fin 2) (Fin 2) ℍ[F, c₀, c₁]

variable (c₀ c₁) in
/-- **The map $\rho$** of (7.4a): $\rho(x) = \begin{pmatrix} 0 & x \\ dx^\iota & 0 \end{pmatrix} \in M_2(B)$. -/
@[kb "shimura2004" "(7.4a), p. 54 (ρ : B → M₂(B), ρ(x) = [[0, x], [dx^ι, 0]])"]
def rho (d : F) : ℍ[F, c₀, c₁] →ₗ[F] Matrix (Fin 2) (Fin 2) ℍ[F, c₀, c₁] where
  toFun x := !![0, x; d • star x, 0]
  map_add' x y := by
    refine Matrix.ext fun i j => ?_; fin_cases i <;> fin_cases j <;> simp [smul_add]
  map_smul' r x := by
    refine Matrix.ext fun i j => ?_; fin_cases i <;> fin_cases j <;> simp [smul_comm r d]

theorem rho_apply (d : F) (x : ℍ[F, c₀, c₁]) : rho c₀ c₁ d x = !![0, x; d • star x, 0] := rfl

theorem rho_00 (d : F) (x : ℍ[F, c₀, c₁]) : rho c₀ c₁ d x 0 0 = 0 := rfl
theorem rho_01 (d : F) (x : ℍ[F, c₀, c₁]) : rho c₀ c₁ d x 0 1 = x := rfl
theorem rho_10 (d : F) (x : ℍ[F, c₀, c₁]) : rho c₀ c₁ d x 1 0 = d • star x := rfl
theorem rho_11 (d : F) (x : ℍ[F, c₀, c₁]) : rho c₀ c₁ d x 1 1 = 0 := rfl

theorem algebraMap_matrix_eq (r : F) :
    algebraMap F M₂ r = !![(r : ℍ[F, c₀, c₁]), 0; 0, (r : ℍ[F, c₀, c₁])] := by
  refine Matrix.ext fun i j => ?_; fin_cases i <;> fin_cases j <;> simp [Matrix.algebraMap_matrix_apply]

/-- (7.4a), p. 54: $\rho(x)^2 = d\,xx^\iota\,1_2 = \varphi[x]\,1_2$. -/
@[kb "shimura2004" "(7.4a), p. 54 (ρ(x)² = d·xx^ι·1₂ = φ[x]·1₂)"]
theorem rho_mul_self (d : F) (x : ℍ[F, c₀, c₁]) :
    rho c₀ c₁ d x * rho c₀ c₁ d x = algebraMap F M₂ (quatForm c₀ c₁ d x) := by
  rw [rho_apply, Matrix.mul_fin_two, algebraMap_matrix_eq, quatForm_apply]
  simp only [zero_mul, mul_zero, zero_add, add_zero, smul_zero, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, mul_star_eq_nrd,
    star_mul_eq_nrd, QuaternionAlgebra.smul_coe]

variable (c₀ c₁) in
/-- The $F$-algebra homomorphism $A(Z) \to M_2(B)$ extending $\rho$ (universal property of $A(Z)$). -/
def liftRho (d : F) : CliffordAlgebra (quatForm c₀ c₁ d) →ₐ[F] M₂ :=
  CliffordAlgebra.lift (quatForm c₀ c₁ d) ⟨rho c₀ c₁ d, rho_mul_self d⟩

theorem liftRho_ι (d : F) (x : ℍ[F, c₀, c₁]) :
    liftRho c₀ c₁ d (ι (quatForm c₀ c₁ d) x) = rho c₀ c₁ d x :=
  CliffordAlgebra.lift_ι_apply _ _ _

/-- $\mathrm{diag}[x, x^\iota]$. -/
def diagX (x : ℍ[F, c₀, c₁]) : M₂ := !![x, 0; 0, star x]

/-- $E = \mathrm{diag}[0, 1]$. -/
def E11 : M₂ := !![0, 0; 0, 1]

theorem rho_mem_range (d : F) (x : ℍ[F, c₀, c₁]) : rho c₀ c₁ d x ∈ (liftRho c₀ c₁ d).range :=
  ⟨ι _ x, liftRho_ι d x⟩

theorem diagX_eq {d : F} (hd : d ≠ 0) (x : ℍ[F, c₀, c₁]) :
    diagX x = d⁻¹ • (rho c₀ c₁ d x * rho c₀ c₁ d 1) := by
  rw [rho_apply, rho_apply, Matrix.mul_fin_two, diagX]
  refine Matrix.ext fun i j => ?_; fin_cases i <;> fin_cases j <;> simp [smul_smul, inv_mul_cancel₀ hd]

theorem diagX_mem_range {d : F} (hd : d ≠ 0) (x : ℍ[F, c₀, c₁]) : diagX x ∈ (liftRho c₀ c₁ d).range := by
  rw [diagX_eq hd]
  exact Subalgebra.smul_mem _ (Subalgebra.mul_mem _ (rho_mem_range d x) (rho_mem_range d 1)) _

theorem E11_eq [Invertible (2 : F)] (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0) :
    (E11 : M₂) = (-(4 * c₀ * c₁))⁻¹ •
      ((diagX ⟨0, 1, 0, 0⟩ * diagX ⟨0, 0, 1, 0⟩ - diagX ⟨0, 0, 0, 1⟩) *
        (diagX ⟨0, 1, 0, 0⟩ * diagX ⟨0, 0, 1, 0⟩ - diagX ⟨0, 0, 0, 1⟩)) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero' F
  have h4 : (4 * c₀ * c₁ : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h₀) h₁
  have h4' : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  simp only [diagX, E11]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> ext <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h4'] <;> field_simp <;> ring

theorem E11_mem_range [Invertible (2 : F)] {d : F} (hd : d ≠ 0) (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0) :
    (E11 : M₂) ∈ (liftRho c₀ c₁ d).range := by
  rw [E11_eq h₀ h₁]
  refine Subalgebra.smul_mem _ (Subalgebra.mul_mem _ ?_ ?_) _ <;>
    exact Subalgebra.sub_mem _ (Subalgebra.mul_mem _ (diagX_mem_range hd _) (diagX_mem_range hd _))
      (diagX_mem_range hd _)

theorem matrix_decomp {d : F} (hd : d ≠ 0) (M : M₂) :
    M = diagX (M 0 0) * (1 - E11) + E11 * diagX (star (M 1 1)) + rho c₀ c₁ d (M 0 1) * E11 +
      d⁻¹ • (E11 * rho c₀ c₁ d (star (M 1 0))) := by
  have hsub : (1 : M₂) - E11 = !![1, 0; 0, 0] := by
    refine Matrix.ext fun i j => ?_; fin_cases i <;> fin_cases j <;> simp [E11]
  rw [hsub]
  conv_lhs => rw [Matrix.eta_fin_two M]
  simp only [diagX, E11, rho_apply, Matrix.mul_fin_two]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, smul_smul, inv_mul_cancel₀ hd]

/-- (7.4a), p. 54: **$\rho(B)$ generates $M_2(B)$ over $F$**, i.e. the homomorphism $A(Z) \to M_2(B)$ extending
$\rho$ is surjective. -/
@[kb "shimura2004" "(7.4a), p. 54 (ρ(B) generates M₂(B) over F)"]
theorem lift_rho_surjective [Invertible (2 : F)] {d : F} (hd : d ≠ 0) (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0) :
    Function.Surjective (liftRho c₀ c₁ d) := by
  intro M
  have hE := E11_mem_range hd h₀ h₁ (c₀ := c₀) (c₁ := c₁)
  have : M ∈ (liftRho c₀ c₁ d).range := by
    rw [matrix_decomp hd M]
    refine Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _ ?_ ?_) ?_) ?_
    · exact Subalgebra.mul_mem _ (diagX_mem_range hd _) (Subalgebra.sub_mem _ (Subalgebra.one_mem _) hE)
    · exact Subalgebra.mul_mem _ hE (diagX_mem_range hd _)
    · exact Subalgebra.mul_mem _ (rho_mem_range d _) hE
    · exact Subalgebra.smul_mem _ (Subalgebra.mul_mem _ hE (rho_mem_range d _)) _
  exact this

/-! ### $\dim_F A(Z) \le 16$ and the isomorphism (7.4b) -/

section Span

variable {V : Type*} [AddCommGroup V] [Module F V] [Invertible (2 : F)] [FiniteDimensional F V]
  {Q : QuadraticForm F V} {h : Fin 4 → V}

/-- In dimension 4, with an orthogonal basis $h_0, \dots, h_3$, $A(V)$ is spanned by the sixteen monomials. -/
theorem mem_span_genE_sup_genW (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : ∀ z : V, ∃ c : Fin 4 → F, z = ∑ i, c i • h i) (a : CliffordAlgebra Q) :
    a ∈ Submodule.span F (LowDim.genE Q h) ⊔ Submodule.span F (LowDim.genW Q h) := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
    apply Submodule.mem_sup_left
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [LowDim.genE]))
  | add x y hx hy => exact add_mem hx hy
  | ι_mul x m hx =>
    obtain ⟨e, he, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨a0, a1, a2, a3, rfl⟩ := LowDim.hspan4 hspan m
    rw [mul_add]
    exact add_mem (Submodule.mem_sup_right (LowDim.ιmul_E horth _ _ _ _ he))
      (Submodule.mem_sup_left (LowDim.ιmul_W horth _ _ _ _ hw))

variable (Q h) in
/-- The sixteen monomials, listed. -/
def mono16 : Fin 8 ⊕ Fin 8 → CliffordAlgebra Q :=
  Sum.elim ![1, ι Q (h 0) * ι Q (h 1), ι Q (h 0) * ι Q (h 2), ι Q (h 0) * ι Q (h 3), ι Q (h 1) * ι Q (h 2),
      ι Q (h 1) * ι Q (h 3), ι Q (h 2) * ι Q (h 3), ι Q (h 0) * (ι Q (h 1) * (ι Q (h 2) * ι Q (h 3)))]
    ![ι Q (h 0), ι Q (h 1), ι Q (h 2), ι Q (h 3), ι Q (h 0) * (ι Q (h 1) * ι Q (h 2)),
      ι Q (h 0) * (ι Q (h 1) * ι Q (h 3)), ι Q (h 0) * (ι Q (h 2) * ι Q (h 3)),
      ι Q (h 1) * (ι Q (h 2) * ι Q (h 3))]

theorem genE_union_genW_subset : LowDim.genE Q h ∪ LowDim.genW Q h ⊆ Set.range (mono16 Q h) := by
  rintro x (hx | hx)
  · simp only [LowDim.genE, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [⟨Sum.inl 0, rfl⟩, ⟨Sum.inl 1, rfl⟩, ⟨Sum.inl 2, rfl⟩, ⟨Sum.inl 3, rfl⟩, ⟨Sum.inl 4, rfl⟩,
      ⟨Sum.inl 5, rfl⟩, ⟨Sum.inl 6, rfl⟩, ⟨Sum.inl 7, rfl⟩]
  · simp only [LowDim.genW, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [⟨Sum.inr 0, rfl⟩, ⟨Sum.inr 1, rfl⟩, ⟨Sum.inr 2, rfl⟩, ⟨Sum.inr 3, rfl⟩, ⟨Sum.inr 4, rfl⟩,
      ⟨Sum.inr 5, rfl⟩, ⟨Sum.inr 6, rfl⟩, ⟨Sum.inr 7, rfl⟩]

theorem span_mono16_eq_top (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : ∀ z : V, ∃ c : Fin 4 → F, z = ∑ i, c i • h i) :
    Submodule.span F (Set.range (mono16 Q h)) = ⊤ := by
  refine eq_top_iff.2 fun a _ => ?_
  have := mem_span_genE_sup_genW horth hspan a
  rw [← Submodule.span_union] at this
  exact Submodule.span_mono genE_union_genW_subset this

theorem clifford_finite (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : ∀ z : V, ∃ c : Fin 4 → F, z = ∑ i, c i • h i) : Module.Finite F (CliffordAlgebra Q) := by
  classical exact ⟨⟨Finset.univ.image (mono16 Q h), by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact span_mono16_eq_top horth hspan⟩⟩

theorem finrank_clifford_le (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (h i) (h j) = 0)
    (hspan : ∀ z : V, ∃ c : Fin 4 → F, z = ∑ i, c i • h i) : finrank F (CliffordAlgebra Q) ≤ 16 := by
  have := finrank_range_le_card (R := F) (mono16 Q h)
  unfold Set.finrank at this
  rw [span_mono16_eq_top horth hspan, finrank_top] at this
  simpa using this

end Span

/-- The basis $1, i, j, k$ of $B$. -/
def basis4 : Fin 4 → ℍ[F, c₀, c₁] := ![1, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

theorem basis4_orth (d : F) :
    ∀ i j, i ≠ j → QuadraticMap.polar (quatForm c₀ c₁ d) (basis4 i) (basis4 j) = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [QuadraticMap.polar, quatForm_apply, nrd, basis4] <;> ring

theorem basis4_span (z : ℍ[F, c₀, c₁]) : ∃ c : Fin 4 → F, z = ∑ i, c i • basis4 i :=
  ⟨![z.re, z.imI, z.imJ, z.imK], by ext <;> simp [Fin.sum_univ_four, basis4]⟩

theorem finrank_matrix_eq : finrank F M₂ = 16 := by
  rw [Module.finrank_matrix, QuaternionAlgebra.finrank_eq_four]; rfl

theorem lift_rho_injective [Invertible (2 : F)] {d : F} (hd : d ≠ 0) (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0) :
    Function.Injective (liftRho c₀ c₁ d) := by
  haveI := clifford_finite (basis4_orth (c₀ := c₀) (c₁ := c₁) d) basis4_span
  have hs := lift_rho_surjective hd h₀ h₁ (c₀ := c₀) (c₁ := c₁)
  have hle := finrank_clifford_le (basis4_orth (c₀ := c₀) (c₁ := c₁) d) basis4_span
  have hge : finrank F M₂ ≤ finrank F (CliffordAlgebra (quatForm c₀ c₁ d)) := by
    have := LinearMap.finrank_range_le (liftRho c₀ c₁ d).toLinearMap
    rwa [LinearMap.range_eq_top.2 (show Function.Surjective (liftRho c₀ c₁ d).toLinearMap from hs),
      finrank_top] at this
  have heq : finrank F (CliffordAlgebra (quatForm c₀ c₁ d)) = finrank F M₂ := by
    rw [finrank_matrix_eq] at hge ⊢; omega
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq
    (f := (liftRho c₀ c₁ d).toLinearMap)).2 hs

variable (c₀ c₁) in
/-- **(7.4b)**: the isomorphism $A(Z) \cong M_2(B)$ extending $\rho$ (for $c_0, c_1, d \ne 0$). -/
def cliffordEquiv [Invertible (2 : F)] {d : F} (hd : d ≠ 0) (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0) :
    CliffordAlgebra (quatForm c₀ c₁ d) ≃ₐ[F] M₂ :=
  AlgEquiv.ofBijective (liftRho c₀ c₁ d) ⟨lift_rho_injective hd h₀ h₁, lift_rho_surjective hd h₀ h₁⟩

theorem cliffordEquiv_apply [Invertible (2 : F)] {d : F} (hd : d ≠ 0) (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0)
    (a : CliffordAlgebra (quatForm c₀ c₁ d)) : cliffordEquiv c₀ c₁ hd h₀ h₁ a = liftRho c₀ c₁ d a := rfl

theorem cliffordEquiv_ι [Invertible (2 : F)] {d : F} (hd : d ≠ 0) (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0)
    (x : ℍ[F, c₀, c₁]) : cliffordEquiv c₀ c₁ hd h₀ h₁ (ι _ x) = rho c₀ c₁ d x := liftRho_ι d x

/-- **(7.4b)**, p. 54: $M_2(B) = A(Z)$ with $Z = \rho(B)$: there is an $F$-algebra isomorphism
$A(Z) \to M_2(B)$ sending each $x \in Z = B$ to $\rho(x) = \begin{pmatrix} 0 & x \\ dx^\iota & 0 \end{pmatrix}$
(for $B = (c_0, c_1)_F$ and $d \in F^\times$). -/
@[kb "shimura2004" "(7.4b), p. 54 (M₂(B) = A(Z) with Z = ρ(B))"]
theorem exists_cliffordEquiv [Invertible (2 : F)] {d : F} (hd : d ≠ 0) (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0) :
    ∃ Φ : CliffordAlgebra (quatForm c₀ c₁ d) ≃ₐ[F] M₂, ∀ x, Φ (ι _ x) = rho c₀ c₁ d x :=
  ⟨cliffordEquiv c₀ c₁ hd h₀ h₁, cliffordEquiv_ι hd h₀ h₁⟩

/-! ### $A^+(Z)$ and the involution -/

theorem liftRho_even {d : F} {a : CliffordAlgebra (quatForm c₀ c₁ d)} (ha : a ∈ evenOdd (quatForm c₀ c₁ d) 0) :
    liftRho c₀ c₁ d a 0 1 = 0 ∧ liftRho c₀ c₁ d a 1 0 = 0 := by
  induction a, ha using CliffordAlgebra.even_induction with
  | algebraMap r => simp [algebraMap_matrix_eq]
  | add x y hx hy ihx ihy => simp [ihx.1, ihx.2, ihy.1, ihy.2]
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    simp only [map_mul, liftRho_ι]
    simp [Matrix.mul_apply, Fin.sum_univ_two, rho_00, rho_11, ih.1, ih.2]

theorem liftRho_odd {d : F} {a : CliffordAlgebra (quatForm c₀ c₁ d)} (ha : a ∈ evenOdd (quatForm c₀ c₁ d) 1) :
    liftRho c₀ c₁ d a 0 0 = 0 ∧ liftRho c₀ c₁ d a 1 1 = 0 := by
  induction a, ha using CliffordAlgebra.odd_induction with
  | ι v => simp [liftRho_ι, rho_00, rho_11]
  | add x y hx hy ihx ihy => simp [ihx.1, ihx.2, ihy.1, ihy.2]
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    simp only [map_mul, liftRho_ι]
    simp [Matrix.mul_apply, Fin.sum_univ_two, rho_00, rho_11, ih.1, ih.2]

section Model

variable [Invertible (2 : F)] {d : F} (hd : d ≠ 0) (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0)

local notation "Φ" => cliffordEquiv c₀ c₁ hd h₀ h₁
local notation "φ" => quatForm c₀ c₁ d

/-- **$A^+(Z) = \{\mathrm{diag}[a, b] \mid a, b \in B\} = B \times B$** (§7.4 (B), p. 54): an element of
$A(Z) = M_2(B)$ is even if and only if it is a diagonal matrix. -/
@[kb "shimura2004" "§7.4 (B), p. 54 (A⁺(Z) = {diag[a, b] | a, b ∈ B} = B × B)"]
theorem evenOdd_zero_iff (a : CliffordAlgebra φ) : a ∈ evenOdd φ 0 ↔ Φ a 0 1 = 0 ∧ Φ a 1 0 = 0 := by
  refine ⟨fun ha => liftRho_even ha, fun ⟨h01, h10⟩ => ?_⟩
  have hmem : a ∈ evenOdd φ 0 ⊔ evenOdd φ 1 := by rw [(evenOdd_isCompl φ).sup_eq_top]; trivial
  obtain ⟨e, he, o, ho, rfl⟩ := Submodule.mem_sup.1 hmem
  have hE := liftRho_even he
  have hO := liftRho_odd ho
  have ho0 : o = 0 := by
    apply lift_rho_injective hd h₀ h₁
    rw [map_zero]
    simp only [cliffordEquiv_apply, map_add, Matrix.add_apply] at h01 h10
    refine Matrix.ext fun i j => ?_; fin_cases i <;> fin_cases j
    · exact hO.1
    · simpa [hE.1] using h01
    · simpa [hE.2] using h10
    · exact hO.2
  rw [ho0, add_zero]; exact he

variable (d) in
/-- Shimura's formula for $a \mapsto a^*$ on $M_2(B)$:
$\begin{pmatrix} p & q \\ r & s \end{pmatrix} \mapsto \begin{pmatrix} p^\iota & d^{-1}r^\iota \\ dq^\iota & s^\iota
\end{pmatrix}$. -/
def sigmaMat (M : M₂) : M₂ :=
  !![star (M 0 0), d⁻¹ • star (M 1 0); d • star (M 0 1), star (M 1 1)]

theorem sigmaMat_mul {d : F} (hd : d ≠ 0) (M N : M₂) : sigmaMat d (M * N) = sigmaMat d N * sigmaMat d M := by
  rw [Matrix.eta_fin_two M, Matrix.eta_fin_two N]
  simp only [sigmaMat, Matrix.mul_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
  refine Matrix.ext fun i j => ?_; fin_cases i <;> fin_cases j <;>
    simp [star_add, smul_add, smul_mul_assoc, mul_smul_comm, smul_smul, inv_mul_cancel₀ hd,
      mul_inv_cancel₀ hd, add_comm]

omit [Invertible (2 : F)] in
theorem sigmaMat_add (M N : M₂) : sigmaMat d (M + N) = sigmaMat d M + sigmaMat d N := by
  refine Matrix.ext fun i j => ?_; fin_cases i <;> fin_cases j <;> simp [sigmaMat, star_add, smul_add]

theorem liftRho_reverse (hd : d ≠ 0) (a : CliffordAlgebra φ) :
    liftRho c₀ c₁ d (reverse a) = sigmaMat d (liftRho c₀ c₁ d a) := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [reverse.commutes, AlgHom.commutes, algebraMap_matrix_eq]
    refine Matrix.ext fun i j => ?_; fin_cases i <;> fin_cases j <;> simp [sigmaMat]
  | ι x =>
    rw [reverse_ι, liftRho_ι, rho_apply]
    refine Matrix.ext fun i j => ?_; fin_cases i <;> fin_cases j <;> simp [sigmaMat, smul_smul, inv_mul_cancel₀ hd]
  | mul a b ha hb => rw [reverse.map_mul, map_mul, map_mul, ha, hb, sigmaMat_mul hd]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb, sigmaMat_add]

/-- **The involution $a \mapsto a^*$ on $A(Z) = M_2(B)$** (§7.4 (B), p. 54): for
$\Phi(a) = \begin{pmatrix} p & q \\ r & s \end{pmatrix}$,
$\Phi(a^*) = \begin{pmatrix} p^\iota & d^{-1}r^\iota \\ dq^\iota & s^\iota \end{pmatrix}$. -/
@[kb "shimura2004" "§7.4 (B), p. 54 (a* = [[p^ι, d⁻¹r^ι], [dq^ι, s^ι]] for a = [[p, q], [r, s]])"]
theorem cliffordEquiv_reverse (a : CliffordAlgebra φ) :
    Φ (reverse a) = !![star (Φ a 0 0), d⁻¹ • star (Φ a 1 0); d • star (Φ a 0 1), star (Φ a 1 1)] :=
  liftRho_reverse (c₀ := c₀) (c₁ := c₁) hd a

theorem cliffordEquiv_mul_reverse {a : CliffordAlgebra φ} (h01 : Φ a 0 1 = 0) (h10 : Φ a 1 0 = 0) :
    Φ (a * reverse a) =
      !![((nrd (Φ a 0 0) : F) : ℍ[F, c₀, c₁]), 0; 0, ((nrd (Φ a 1 1) : F) : ℍ[F, c₀, c₁])] := by
  rw [map_mul, cliffordEquiv_reverse, Matrix.eta_fin_two (Φ a), h01, h10]
  simp [Matrix.mul_fin_two, mul_star_eq_nrd]

include hd h₀ h₁ in
theorem basis4_ne_zero : ∀ i, φ (basis4 i) ≠ 0 := by
  intro i
  fin_cases i <;> simp [quatForm_apply, nrd, basis4, hd, h₀, h₁]

include hd h₀ h₁ in
theorem nondeg : (QuadraticMap.associated φ).Nondegenerate :=
  LowDim.nondegenerate_of_orthogonal (basis4_ne_zero hd h₀ h₁) (basis4_orth d) basis4_span

theorem exists_algebraMap_iff {a : CliffordAlgebra φ} (h01 : Φ a 0 1 = 0) (h10 : Φ a 1 0 = 0) (c : F) :
    a * reverse a = algebraMap F _ c ↔ nrd (Φ a 0 0) = c ∧ nrd (Φ a 1 1) = c := by
  rw [← (cliffordEquiv c₀ c₁ hd h₀ h₁).injective.eq_iff, AlgEquiv.commutes,
    cliffordEquiv_mul_reverse hd h₀ h₁ h01 h10, algebraMap_matrix_eq]
  constructor
  · intro h
    have e0 := congrArg (fun M => (M 0 0).re) h
    have e1 := congrArg (fun M => (M 1 1).re) h
    simp at e0 e1
    exact ⟨e0, e1⟩
  · rintro ⟨e0, e1⟩
    rw [e0, e1]

/-- **(7.5a)**, p. 55: $G^+(Z) = \{(a, b) \in B^\times \times B^\times \mid aa^\iota = bb^\iota\}$: a unit $u$ of
$A(Z) = M_2(B)$ lies in $G^+(Z)$ if and only if $\Phi(u) = \mathrm{diag}[a, b]$ with $aa^\iota = bb^\iota$ (then
$a, b \in B^\times$, see `nrd_ne_zero_of_mem_M0`). -/
@[kb "shimura2004" "(7.5a), p. 55 (G⁺(Z) = {(a, b) ∈ B^× × B^× | aa^ι = bb^ι})"]
theorem mem_M0_iff (u : (CliffordAlgebra φ)ˣ) :
    u ∈ M0 φ ↔ Φ u 0 1 = 0 ∧ Φ u 1 0 = 0 ∧ nrd (Φ u 0 0) = nrd (Φ u 1 1) := by
  rw [LowDim.dim4_mem_M0_iff (basis4_ne_zero hd h₀ h₁) (basis4_orth d) basis4_span, evenOdd_zero_iff hd h₀ h₁]
  constructor
  · rintro ⟨⟨h01, h10⟩, c, hc⟩
    obtain ⟨e0, e1⟩ := (exists_algebraMap_iff hd h₀ h₁ h01 h10 c).1 hc
    exact ⟨h01, h10, e0.trans e1.symm⟩
  · rintro ⟨h01, h10, e⟩
    exact ⟨⟨h01, h10⟩, _, (exists_algebraMap_iff hd h₀ h₁ h01 h10 _).2 ⟨rfl, e.symm⟩⟩

/-- **$\nu((a, b)) = aa^\iota$** for $(a, b) \in G^+(Z)$ (§7.4 (B), p. 55). -/
@[kb "shimura2004" "§7.4 (B), p. 55 (ν((a, b)) = aa^ι for (a, b) ∈ G⁺(Z))"]
theorem multiplier_eq_nrd (u : M0 φ) :
    (multiplier (nondeg hd h₀ h₁) ⟨u, M0_le_homogeneous u.2⟩ : F) = nrd (Φ (u : (CliffordAlgebra φ)ˣ) 0 0) := by
  obtain ⟨h01, h10, -⟩ := (mem_M0_iff hd h₀ h₁ _).1 u.2
  have := (exists_algebraMap_iff hd h₀ h₁ h01 h10 _).1 (algebraMap_multiplier_M0 (nondeg hd h₀ h₁) u).symm
  exact this.1.symm

/-- For $(a, b) \in G^+(Z)$, $a$ and $b$ are invertible: $aa^\iota = bb^\iota = \nu \ne 0$. -/
theorem nrd_ne_zero_of_mem_M0 (u : M0 φ) :
    nrd (Φ (u : (CliffordAlgebra φ)ˣ) 0 0) ≠ 0 ∧ nrd (Φ (u : (CliffordAlgebra φ)ˣ) 1 1) ≠ 0 := by
  obtain ⟨-, -, e⟩ := (mem_M0_iff hd h₀ h₁ _).1 u.2
  have h := multiplier_eq_nrd hd h₀ h₁ u
  have hne := (multiplier (nondeg hd h₀ h₁) ⟨u, M0_le_homogeneous u.2⟩).ne_zero
  rw [h] at hne
  exact ⟨hne, e ▸ hne⟩

theorem inv_mul_self (x : ℍ[F, c₀, c₁]) (hx : nrd x ≠ 0) : ((nrd x)⁻¹ • star x) * x = 1 := by
  rw [smul_mul_assoc, star_mul_eq_nrd, QuaternionAlgebra.smul_coe, inv_mul_cancel₀ hx]; rfl

theorem mul_inv_self (x : ℍ[F, c₀, c₁]) (hx : nrd x ≠ 0) : x * ((nrd x)⁻¹ • star x) = 1 := by
  rw [mul_smul_comm, mul_star_eq_nrd, QuaternionAlgebra.smul_coe, inv_mul_cancel₀ hx]; rfl

/-- **(7.5a)**, converse inclusion: every $\mathrm{diag}[a, b]$ with $a, b \in B^\times$ and $aa^\iota = bb^\iota$ is
the image of an element of $G^+(Z)$. -/
@[kb "shimura2004" "(7.5a), p. 55 (every (a, b) ∈ B^× × B^× with aa^ι = bb^ι lies in G⁺(Z))"]
theorem exists_mem_M0_of_nrd_eq (a b : ℍ[F, c₀, c₁]) (ha : nrd a ≠ 0) (hab : nrd a = nrd b) :
    ∃ u : (CliffordAlgebra φ)ˣ, u ∈ M0 φ ∧ Φ u = !![a, 0; 0, b] := by
  have hb : nrd b ≠ 0 := hab ▸ ha
  let X : M₂ := !![a, 0; 0, b]
  let Y : M₂ := !![(nrd a)⁻¹ • star a, 0; 0, (nrd b)⁻¹ • star b]
  have hXY : X * Y = 1 := by
    simp only [X, Y, Matrix.mul_fin_two, mul_inv_self a ha, mul_inv_self b hb, Matrix.one_fin_two]; simp
  have hYX : Y * X = 1 := by
    simp only [X, Y, Matrix.mul_fin_two, inv_mul_self a ha, inv_mul_self b hb, Matrix.one_fin_two]; simp
  let u : (CliffordAlgebra φ)ˣ :=
    ⟨(cliffordEquiv c₀ c₁ hd h₀ h₁).symm X, (cliffordEquiv c₀ c₁ hd h₀ h₁).symm Y,
      by rw [← map_mul, hXY, map_one], by rw [← map_mul, hYX, map_one]⟩
  have hu : Φ u = X := AlgEquiv.apply_symm_apply _ _
  refine ⟨u, (mem_M0_iff hd h₀ h₁ u).2 ?_, hu⟩
  rw [hu]
  simpa [X] using hab

/-- **(7.5b)**, p. 55: $G^1(Z) = \{(a, b) \in B^\times \times B^\times \mid aa^\iota = bb^\iota = 1\}$. -/
@[kb "shimura2004" "(7.5b), p. 55 (G¹(Z) = {(a, b) ∈ B^× × B^× | aa^ι = bb^ι = 1})"]
theorem mem_spinGroupG1_iff (u : (CliffordAlgebra φ)ˣ) :
    u ∈ spinGroupG1 φ ↔ Φ u 0 1 = 0 ∧ Φ u 1 0 = 0 ∧ nrd (Φ u 0 0) = 1 ∧ nrd (Φ u 1 1) = 1 := by
  change (u ∈ M0 φ ∧ (u : CliffordAlgebra φ) * reverse (u : CliffordAlgebra φ) = 1) ↔ _
  rw [mem_M0_iff hd h₀ h₁]
  constructor
  · rintro ⟨⟨h01, h10, -⟩, h1⟩
    rw [← map_one (algebraMap F (CliffordAlgebra φ))] at h1
    exact ⟨h01, h10, (exists_algebraMap_iff hd h₀ h₁ h01 h10 1).1 h1⟩
  · rintro ⟨h01, h10, e0, e1⟩
    refine ⟨⟨h01, h10, e0.trans e1.symm⟩, ?_⟩
    rw [← map_one (algebraMap F (CliffordAlgebra φ))]
    exact (exists_algebraMap_iff hd h₀ h₁ h01 h10 1).2 ⟨e0, e1⟩

/-! ### $\tau$ on $G^+(Z)$ and $\eta$ -/

theorem rho_injective (x y : ℍ[F, c₀, c₁]) (h : rho c₀ c₁ d x = rho c₀ c₁ d y) : x = y := by
  simpa [rho_01] using congrArg (fun M => M 0 1) h

/-- For $\alpha = (a, b) \in G^+(Z)$ the $(0,0)$ entry of $\Phi(\alpha^{-1})$ is $a^{-1}$. -/
theorem inv_entry_mul (u : M0 φ) :
    Φ (((u : (CliffordAlgebra φ)ˣ)⁻¹ : (CliffordAlgebra φ)ˣ) : CliffordAlgebra φ) 0 0 *
      Φ (u : (CliffordAlgebra φ)ˣ) 0 0 = 1 := by
  have h : Φ ((((u : (CliffordAlgebra φ)ˣ)⁻¹ : (CliffordAlgebra φ)ˣ) : CliffordAlgebra φ) *
      ((u : (CliffordAlgebra φ)ˣ) : CliffordAlgebra φ)) = 1 := by
    rw [Units.inv_mul, map_one]
  rw [map_mul] at h
  have h00 := congrArg (fun M => M 0 0) h
  obtain ⟨h01, -, -⟩ := (mem_M0_iff hd h₀ h₁ _).1 ((M0 φ).inv_mem u.2)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, h01, zero_mul, add_zero, Matrix.one_apply_eq] at h00
  exact h00

/-- **$\rho(x)\tau(\alpha) = \rho(a^{-1}xb)$** for $\alpha = (a, b) \in G^+(Z)$ (§7.4 (B), p. 55): with
$x\tau(\alpha) = \alpha^{-1}x\alpha$ written `tau α x`, $x\tau(\alpha) = a^{-1}xb$, where $a^{-1}$ is the $(0,0)$
entry of $\Phi(\alpha^{-1})$ (`inv_entry_mul`). -/
@[kb "shimura2004" "§7.4 (B), p. 55 (ρ(x)τ(α) = ρ(a⁻¹xb) for α = (a, b) ∈ G⁺(Z))"]
theorem tau_eq (u : M0 φ) (x : ℍ[F, c₀, c₁]) :
    tau ⟨(u : (CliffordAlgebra φ)ˣ), ((Shimura2004.mem_M0_iff _).1 u.2).1⟩ x =
      Φ (((u : (CliffordAlgebra φ)ˣ)⁻¹ : (CliffordAlgebra φ)ˣ) : CliffordAlgebra φ) 0 0 * x *
        Φ (u : (CliffordAlgebra φ)ˣ) 1 1 := by
  have h := congrArg (cliffordEquiv c₀ c₁ hd h₀ h₁) (tau_spec ⟨u, ((Shimura2004.mem_M0_iff _).1 u.2).1⟩ x)
  rw [cliffordEquiv_ι, map_mul, map_mul, cliffordEquiv_ι] at h
  have h01 := congrArg (fun M => M 0 1) h
  obtain ⟨i01, -, -⟩ := (mem_M0_iff hd h₀ h₁ _).1 ((M0 φ).inv_mem u.2)
  simp only [rho_01] at h01
  rw [h01]
  simp [Matrix.mul_apply, Fin.sum_univ_two, rho_00, rho_01, rho_11, i01, mul_assoc]

include hd h₀ h₁ in
theorem quatForm_one_ne_zero : φ 1 ≠ 0 := by
  simpa [basis4] using basis4_ne_zero hd h₀ h₁ 0

/-- **$\eta = \rho(1) = \begin{pmatrix} 0 & 1 \\ d & 0 \end{pmatrix}$ and $\rho(x)\tau(\eta) = \rho(x^\iota)$**
(§7.4 (B), p. 55): $\eta$ is the vector $1 \in Z = B$ (`vecUnit 1`), and $\tau(\eta)$ is the main involution of $B$. -/
@[kb "shimura2004" "§7.4 (B), p. 55 (ρ(x)τ(η) = ρ(x^ι) for η = ρ(1))"]
theorem tau_eta (x : ℍ[F, c₀, c₁]) :
    tau ⟨vecUnit (1 : ℍ[F, c₀, c₁]) (quatForm_one_ne_zero hd h₀ h₁),
      (vecUnit_mem_cliffordGroupOdd _ (quatForm_one_ne_zero hd h₀ h₁)).1⟩ x = star x := by
  apply rho_injective (d := d)
  rw [← cliffordEquiv_ι hd h₀ h₁, tau_spec]
  change Φ (((φ 1)⁻¹ • ι φ 1) * ι φ x * ι φ 1) = _
  rw [map_mul, map_mul, map_smul, cliffordEquiv_ι, cliffordEquiv_ι, quatForm_apply]
  rw [rho_apply, rho_apply, rho_apply]
  have hn : nrd (1 : ℍ[F, c₀, c₁]) = 1 := by simp [nrd]
  rw [hn, mul_one]
  refine Matrix.ext fun i j => ?_; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_fin_two, smul_smul, inv_mul_cancel₀ hd, smul_mul_assoc, mul_smul_comm]

end Model

/-! ### The main involution of $B$ in $O^\varphi$ -/

variable (c₀ c₁) in
/-- The main involution $x \mapsto x^\iota$ of $B$, as an $F$-linear automorphism of $Z = B$. -/
def starEquiv : ℍ[F, c₀, c₁] ≃ₗ[F] ℍ[F, c₀, c₁] where
  toFun := star
  invFun := star
  map_add' := star_add
  map_smul' r x := by simp
  left_inv := star_star
  right_inv := star_star

theorem starEquiv_mem_orth (d : F) : starEquiv c₀ c₁ ∈ orth (quatForm c₀ c₁ d) := fun x => by
  simp [starEquiv, quatForm_apply, nrd_star]

theorem det_starEquiv : LinearEquiv.det (starEquiv c₀ c₁) = -1 := by
  ext
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix (QuaternionAlgebra.basisOneIJK c₀ 0 c₁)]
  have : LinearMap.toMatrix (QuaternionAlgebra.basisOneIJK c₀ 0 c₁) (QuaternionAlgebra.basisOneIJK c₀ 0 c₁)
      (starEquiv c₀ c₁).toLinearMap = Matrix.diagonal ![1, -1, -1, -1] := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, QuaternionAlgebra.basisOneIJK, starEquiv, Matrix.diagonal]
  rw [this, Matrix.det_diagonal, Fin.prod_univ_four]
  norm_num

/-- **The main involution $\iota$ of $B$ belongs to $O^\varphi$ and has determinant $-1$; thus $O^\varphi$ is
generated by $SO^\varphi$ and $\iota$** (§7.4 (B), p. 55): every $\alpha \in O^\varphi(Z)$ lies in $SO^\varphi(Z)$
or in $SO^\varphi(Z)\,\iota$. -/
@[kb "shimura2004" "§7.4 (B), p. 55 (ι ∈ O^φ, det ι = -1, O^φ = SO^φ ∪ SO^φ ι)"]
theorem orth_eq_orthPlus_or_mul_star [Invertible (2 : F)] {d : F} (hd : d ≠ 0) (h₀ : c₀ ≠ 0) (h₁ : c₁ ≠ 0)
    {α : ℍ[F, c₀, c₁] ≃ₗ[F] ℍ[F, c₀, c₁]} (hα : α ∈ orth (quatForm c₀ c₁ d)) :
    starEquiv c₀ c₁ ∈ orth (quatForm c₀ c₁ d) ∧ LinearEquiv.det (starEquiv c₀ c₁) = -1 ∧
      (α ∈ orthPlus (quatForm c₀ c₁ d) ∨ α * starEquiv c₀ c₁ ∈ orthPlus (quatForm c₀ c₁ d)) := by
  refine ⟨starEquiv_mem_orth d, det_starEquiv, ?_⟩
  rcases det_eq_one_or_neg_one (nondeg hd h₀ h₁) hα with h | h
  · exact Or.inl ⟨hα, h⟩
  · refine Or.inr ⟨(orth _).mul_mem hα (starEquiv_mem_orth d), ?_⟩
    change LinearEquiv.det (α * starEquiv c₀ c₁) = 1
    rw [map_mul, h, det_starEquiv]; norm_num

end QuatModel

end QuadFormsKB.Shimura2004
