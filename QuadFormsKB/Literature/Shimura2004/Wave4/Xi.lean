/-
# Shimura 2004, §2.5: the twisted matrix model $\Xi : A(V) \cong M_2(A(U))$

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Chapter I, §2.5 and
Theorem 2.6 (printed p. 19), formulas (2.14), (2.15). Page numbers in the tags are printed pages.

**Setting and dictionary.** As in `Wave4/MatrixModel.lean`: $V = U + Fe + Ff$ with `Q e = 0`, `Q f = 0`,
`QuadraticMap.polar Q e f = 1`, $U$ = `uSpace Q e f`, $A(U)$ = `AU Q e f`, $\Psi$ = `psi`. We assume
$U \ne \{0\}$ in the form: there is $g \in U$ with $g^2 = \varphi[g] \ne 0$ (`g : uSpace Q e f`,
`hg : Q (g : V) ≠ 0`); here $g$ also denotes $\iota(g) \in A(U)$. Put
$\Delta = \mathrm{diag}[g, 1] \in M_2(A(U))$ (`delta`), invertible with
$\Delta^{-1} = \mathrm{diag}[g^{-1}, 1]$ (`deltaInv`), $g^{-1} = \varphi[g]^{-1} g$ (`ginv`).

**Defines**
* (2.14) $\Xi(\alpha) = \Delta^{-1}\Psi(\alpha)\Delta$ (`xi`), an $F$-algebra homomorphism
  $A(V) \to M_2(A(U))$; if $\Psi(\alpha) = \begin{pmatrix} a & b \\ c & d\end{pmatrix}$ then
  $\Xi(\alpha) = \begin{pmatrix} g^{-1}ag & g^{-1}b \\ cg & d\end{pmatrix}$ (`xi_apply_zero_zero`, ...).

**Proves** (all unconditional; standard axioms only)
* $\Xi$ is bijective (`xi_bijective`);
* (2.15) $\Xi(A^+(V)) = M_2(A^+(U))$ (`xi_mem_evenOdd_zero_iff`), using $g^{-1}A^-(U) = A^-(U)g = A^+(U)$ and
  $g^{-1}A^+(U)g = A^+(U)$;
* Theorem 2.6, "moreover" part, case $s = 1$, $X = U \ne 0$: $A^+(V) \cong M_2(A^+(U))$ as $F$-algebras
  (`theorem_2_6_one_even`).
-/
import QuadFormsKB.Literature.Shimura2004.Wave4.MatrixModel
import QuadFormsKB.Citation

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Cassels QuadFormsKB.OMeara

namespace MatrixModel

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V} {e f : V}

/-! ### Grading lemmas for a unit of odd degree -/

section Grading

variable {W : Type*} [AddCommGroup W] [Module F W] {Q' : QuadraticForm F W}
  {x y : CliffordAlgebra Q'}

private theorem mul_mem_one_one {a b : CliffordAlgebra Q'} (ha : a ∈ evenOdd Q' 1) (hb : b ∈ evenOdd Q' 1) :
    a * b ∈ evenOdd Q' 0 := by
  have := SetLike.mul_mem_graded ha hb
  rwa [show (1 : ZMod 2) + 1 = 0 from rfl] at this

private theorem mul_mem_one_zero {a b : CliffordAlgebra Q'} (ha : a ∈ evenOdd Q' 1) (hb : b ∈ evenOdd Q' 0) :
    a * b ∈ evenOdd Q' 1 := by
  have := SetLike.mul_mem_graded ha hb
  rwa [add_zero] at this

private theorem mul_mem_zero_one {a b : CliffordAlgebra Q'} (ha : a ∈ evenOdd Q' 0) (hb : b ∈ evenOdd Q' 1) :
    a * b ∈ evenOdd Q' 1 := by
  have := SetLike.mul_mem_graded ha hb
  rwa [zero_add] at this

/-- If $x, y$ are odd with $xy = yx = 1$ then $a \in A^+ \iff y a x \in A^+$. -/
private theorem mem_zero_iff_conj (hx : x ∈ evenOdd Q' 1) (hy : y ∈ evenOdd Q' 1) (hxy : x * y = 1)
    (a : CliffordAlgebra Q') : a ∈ evenOdd Q' 0 ↔ y * a * x ∈ evenOdd Q' 0 := by
  constructor
  · intro ha; exact mul_mem_one_zero hy ha |> fun h => mul_mem_one_one h hx
  · intro h
    have : a = x * (y * a * x) * y := by
      calc a = (x * y) * a * (x * y) := by rw [hxy, one_mul, mul_one]
        _ = x * (y * a * x) * y := by simp only [mul_assoc]
    rw [this]; exact mul_mem_one_one (mul_mem_one_zero hx h) hy

/-- If $x, y$ are odd with $xy = 1$ then $b \in A^- \iff y b \in A^+$. -/
private theorem mem_one_iff_mul_left (hx : x ∈ evenOdd Q' 1) (hy : y ∈ evenOdd Q' 1) (hxy : x * y = 1)
    (b : CliffordAlgebra Q') : b ∈ evenOdd Q' 1 ↔ y * b ∈ evenOdd Q' 0 := by
  constructor
  · intro h; exact mul_mem_one_one hy h
  · intro h
    have : b = x * (y * b) := by rw [← mul_assoc, hxy, one_mul]
    rw [this]; exact mul_mem_one_zero hx h

/-- If $x, y$ are odd with $xy = 1$ then $c \in A^- \iff c x \in A^+$. -/
private theorem mem_one_iff_mul_right (hx : x ∈ evenOdd Q' 1) (hy : y ∈ evenOdd Q' 1) (hxy : x * y = 1)
    (c : CliffordAlgebra Q') : c ∈ evenOdd Q' 1 ↔ c * x ∈ evenOdd Q' 0 := by
  constructor
  · intro h; exact mul_mem_one_one h hx
  · intro h
    have : c = (c * x) * y := by rw [mul_assoc, hxy, mul_one]
    rw [this]; exact mul_mem_zero_one h hy

omit [Invertible (2 : F)] in
private theorem mem_even_iff {a : CliffordAlgebra Q'} : a ∈ CliffordAlgebra.even Q' ↔ a ∈ evenOdd Q' 0 := by
  rw [← CliffordAlgebra.even_toSubmodule]; rfl

end Grading

/-! ### $\Delta = \mathrm{diag}[g, 1]$ -/

section Hyp

variable (he : Q e = 0) (hf : Q f = 0) (hef : QuadraticMap.polar Q e f = 1)

/-- **$g^{-1}$ in $A(U)$**: $g^{-1} = \varphi[g]^{-1}\, g$ (with $g$ meaning $\iota(g)$). -/
def ginv (g : uSpace Q e f) : AU Q e f := algebraMap F _ (QU Q e f g)⁻¹ * ι (QU Q e f) g

variable {g : uSpace Q e f}

theorem mul_ginv (hg : Q (g : V) ≠ 0) : ι (QU Q e f) g * ginv g = 1 := by
  have h : QU Q e f g ≠ 0 := hg
  rw [ginv, ← mul_assoc, ← Algebra.commutes, mul_assoc, ι_sq_scalar, ← map_mul, inv_mul_cancel₀ h, map_one]

theorem ginv_mul (hg : Q (g : V) ≠ 0) : ginv g * ι (QU Q e f) g = 1 := by
  have h : QU Q e f g ≠ 0 := hg
  rw [ginv, mul_assoc, ι_sq_scalar, ← map_mul, inv_mul_cancel₀ h, map_one]

theorem ginv_mem_evenOdd_one : ginv g ∈ evenOdd (QU Q e f) 1 := by
  rw [ginv, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (ι_mem_evenOdd_one _ _)

variable (g) in
/-- **Shimura's $\Delta = \mathrm{diag}[g, 1]$** (§2.5, p. 19). -/
def delta : Matrix (Fin 2) (Fin 2) (AU Q e f) := !![ι (QU Q e f) g, 0; 0, 1]

variable (g) in
/-- $\Delta^{-1} = \mathrm{diag}[g^{-1}, 1]$ (§2.5, p. 19). -/
def deltaInv : Matrix (Fin 2) (Fin 2) (AU Q e f) := !![ginv g, 0; 0, 1]

theorem deltaInv_mul_delta (hg : Q (g : V) ≠ 0) : deltaInv g * delta g = 1 := by
  rw [deltaInv, delta, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [ginv_mul hg]

theorem delta_mul_deltaInv (hg : Q (g : V) ≠ 0) : delta g * deltaInv g = 1 := by
  rw [deltaInv, delta, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [mul_ginv hg]

include he hf hef

/-- **Shimura's $\Xi$** (2.14), p. 19: $\Xi(\alpha) = \Delta^{-1}\Psi(\alpha)\Delta$ with
$\Delta = \mathrm{diag}[g, 1]$, for a fixed $g \in U$ with $\varphi[g] \ne 0$. It is an $F$-algebra
isomorphism $A(V) \to M_2(A(U))$ (`xi_bijective`). -/
@[kb "shimura2004" "(2.14), p. 19 (Ξ(α) = Δ⁻¹Ψ(α)Δ, Δ = diag[g, 1])"]
def xi (hg : Q (g : V) ≠ 0) : CliffordAlgebra Q →ₐ[F] Matrix (Fin 2) (Fin 2) (AU Q e f) where
  toFun x := deltaInv g * psi he hf hef x * delta g
  map_one' := by simp [deltaInv_mul_delta hg]
  map_mul' x y := by
    have h := delta_mul_deltaInv hg
    have : (deltaInv g * psi he hf hef x * delta g) * (deltaInv g * psi he hf hef y * delta g) =
        deltaInv g * psi he hf hef x * (delta g * deltaInv g) * psi he hf hef y * delta g := by
      simp only [mul_assoc]
    rw [this, h, mul_one, map_mul]
    simp only [mul_assoc]
  map_zero' := by simp
  map_add' x y := by simp [mul_add, add_mul]
  commutes' r := by
    rw [AlgHom.commutes, ← Algebra.commutes, mul_assoc, deltaInv_mul_delta hg, mul_one]

theorem xi_apply (hg : Q (g : V) ≠ 0) (α : CliffordAlgebra Q) :
    xi he hf hef hg α = deltaInv g * psi he hf hef α * delta g := rfl

/-- (2.14), entry $(0,0)$: $\Xi(\alpha)_{00} = g^{-1}ag$ where $a = \Psi(\alpha)_{00}$. -/
theorem xi_apply_zero_zero (hg : Q (g : V) ≠ 0) (α : CliffordAlgebra Q) :
    xi he hf hef hg α 0 0 = ginv g * psi he hf hef α 0 0 * ι (QU Q e f) g := by
  simp only [xi_apply, deltaInv, delta, Matrix.mul_apply, Fin.sum_univ_two]
  simp

/-- (2.14), entry $(0,1)$: $\Xi(\alpha)_{01} = g^{-1}b$ where $b = \Psi(\alpha)_{01}$. -/
theorem xi_apply_zero_one (hg : Q (g : V) ≠ 0) (α : CliffordAlgebra Q) :
    xi he hf hef hg α 0 1 = ginv g * psi he hf hef α 0 1 := by
  simp only [xi_apply, deltaInv, delta, Matrix.mul_apply, Fin.sum_univ_two]
  simp

/-- (2.14), entry $(1,0)$: $\Xi(\alpha)_{10} = cg$ where $c = \Psi(\alpha)_{10}$. -/
theorem xi_apply_one_zero (hg : Q (g : V) ≠ 0) (α : CliffordAlgebra Q) :
    xi he hf hef hg α 1 0 = psi he hf hef α 1 0 * ι (QU Q e f) g := by
  simp only [xi_apply, deltaInv, delta, Matrix.mul_apply, Fin.sum_univ_two]
  simp

/-- (2.14), entry $(1,1)$: $\Xi(\alpha)_{11} = d$ where $d = \Psi(\alpha)_{11}$. -/
theorem xi_apply_one_one (hg : Q (g : V) ≠ 0) (α : CliffordAlgebra Q) :
    xi he hf hef hg α 1 1 = psi he hf hef α 1 1 := by
  simp only [xi_apply, deltaInv, delta, Matrix.mul_apply, Fin.sum_univ_two]
  simp

theorem psi_eq (hg : Q (g : V) ≠ 0) (α : CliffordAlgebra Q) :
    psi he hf hef α = delta g * xi he hf hef hg α * deltaInv g := by
  rw [xi_apply]
  calc psi he hf hef α = (delta g * deltaInv g) * psi he hf hef α * (delta g * deltaInv g) := by
        rw [delta_mul_deltaInv hg, one_mul, mul_one]
    _ = _ := by simp only [mul_assoc]

/-- **(2.14)**, p. 19: $\Xi$ is a bijection of $A(V)$ onto $M_2(A(U))$. -/
@[kb "shimura2004" "(2.14), p. 19 (Ξ is a ring isomorphism of A(V) onto M₂(A(U)))"]
theorem xi_bijective (hg : Q (g : V) ≠ 0) : Function.Bijective (xi he hf hef hg) := by
  have h1 := deltaInv_mul_delta hg
  have h2 := delta_mul_deltaInv hg
  constructor
  · intro x y hxy
    apply (psi_bijective he hf hef).1
    rw [psi_eq he hf hef hg x, psi_eq he hf hef hg y, hxy]
  · intro M
    obtain ⟨α, hα⟩ := (psi_bijective he hf hef).2 (delta g * M * deltaInv g)
    refine ⟨α, ?_⟩
    rw [xi_apply, hα]
    calc deltaInv g * (delta g * M * deltaInv g) * delta g
        = (deltaInv g * delta g) * M * (deltaInv g * delta g) := by simp only [mul_assoc]
      _ = M := by rw [h1, one_mul, mul_one]

/-- **(2.15)**, p. 19: $\alpha \in A^+(V)$ if and only if all four entries of $\Xi(\alpha)$ lie in $A^+(U)$;
that is, $\Xi(A^+(V)) = M_2(A^+(U))$ (as $\Xi$ is bijective). -/
@[kb "shimura2004" "(2.15), p. 19 (Ξ(A⁺(V)) = M₂(A⁺(U)))"]
theorem xi_mem_evenOdd_zero_iff (hg : Q (g : V) ≠ 0) (α : CliffordAlgebra Q) :
    α ∈ evenOdd Q 0 ↔ ∀ i j, xi he hf hef hg α i j ∈ evenOdd (QU Q e f) 0 := by
  have hgm : ι (QU Q e f) g ∈ evenOdd (QU Q e f) 1 := ι_mem_evenOdd_one _ _
  have hgi : ginv g ∈ evenOdd (QU Q e f) 1 := ginv_mem_evenOdd_one
  rw [psi_mem_evenOdd_zero_iff he hf hef, Fin.forall_fin_two, Fin.forall_fin_two, Fin.forall_fin_two,
    xi_apply_zero_zero, xi_apply_zero_one, xi_apply_one_zero, xi_apply_one_one,
    ← mem_zero_iff_conj hgm hgi (mul_ginv hg), ← mem_one_iff_mul_left hgm hgi (mul_ginv hg),
    ← mem_one_iff_mul_right hgm hgi (mul_ginv hg)]
  tauto

/-- **Theorem 2.6** (Shimura 2004, p. 19), "moreover" part, case $s = 1$, $X = U \ne 0$: if there is
$g \in U$ with $\varphi[g] \ne 0$ then $A^+(V) \cong M_2(A^+(U))$ as $F$-algebras. -/
@[kb "shimura2004" "Theorem 2.6, p. 19 (case s = 1, X = U ≠ 0: A⁺(V) ≅ M₂(A⁺(U)))"]
theorem theorem_2_6_one_even (hg : Q (g : V) ≠ 0) :
    Nonempty (CliffordAlgebra.even Q ≃ₐ[F]
      Matrix (Fin 2) (Fin 2) (CliffordAlgebra.even (QU Q e f))) := by
  classical
  let φ : CliffordAlgebra.even Q →ₐ[F] Matrix (Fin 2) (Fin 2) (AU Q e f) :=
    (xi he hf hef hg).comp (CliffordAlgebra.even Q).val
  let ψ : Matrix (Fin 2) (Fin 2) (CliffordAlgebra.even (QU Q e f)) →ₐ[F]
      Matrix (Fin 2) (Fin 2) (AU Q e f) :=
    (CliffordAlgebra.even (QU Q e f)).val.mapMatrix
  have hφ : Function.Injective φ :=
    (xi_bijective he hf hef hg).1.comp Subtype.val_injective
  have hψ : Function.Injective ψ := by
    intro M N h
    ext i j
    have := congrArg (fun P => P i j) h
    exact this
  have hrange : φ.range = ψ.range := by
    ext M
    constructor
    · rintro ⟨α, rfl⟩
      have hα : (α : CliffordAlgebra Q) ∈ evenOdd Q 0 := mem_even_iff.1 α.2
      have hall := (xi_mem_evenOdd_zero_iff he hf hef hg _).1 hα
      refine ⟨Matrix.of fun i j => ⟨xi he hf hef hg α i j, ?_⟩, ?_⟩
      · rw [← CliffordAlgebra.even_toSubmodule] at hall
        exact hall i j
      · ext i j; rfl
    · rintro ⟨N, rfl⟩
      obtain ⟨α, hα⟩ := (xi_bijective he hf hef hg).2 (ψ N)
      have hall : ∀ i j, xi he hf hef hg α i j ∈ evenOdd (QU Q e f) 0 := by
        intro i j
        rw [hα]
        exact mem_even_iff.1 (N i j).2
      have : α ∈ CliffordAlgebra.even Q :=
        mem_even_iff.2 ((xi_mem_evenOdd_zero_iff he hf hef hg _).2 hall)
      exact ⟨⟨α, this⟩, hα⟩
  exact ⟨(AlgEquiv.ofInjective φ hφ).trans
    ((Subalgebra.equivOfEq _ _ hrange).trans (AlgEquiv.ofInjective ψ hψ).symm)⟩

end Hyp

end MatrixModel

end QuadFormsKB.Shimura2004
