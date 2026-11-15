/-
# Shimura 2004, Theorem 2.6 for every $s$ and the isomorphism $\Theta$ of §4.5

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Theorem 2.6 (printed p. 19)
and §4.5, formulas (4.11)–(4.14) (printed p. 31). Page numbers in the tags are printed pages.

**Setting and dictionary.** As in `Wave4/MatrixModel.lean` and `Wave5/Levi.lean`: $F$ a field of characteristic
$\ne 2$ (`Invertible (2 : F)`), `Q : QuadraticForm F V` on a finite-dimensional $V$ with $Q(x) = \varphi[x]$,
$2\varphi(x,y)$ = `QuadraticMap.polar Q x y`, $A(V)$ = `CliffordAlgebra Q`. A weak Witt decomposition
$V = U + \sum_{i<s}(Fe_i + Ff_i)$ (Shimura's $e_1, \dots, e_s$ are `e 0, …, e (s-1)` here) is the hypothesis
`IsHypFamily Q e f`, and $U$ = `wSpace Q e f` is the orthogonal complement of all the hyperbolic pairs (so
$A(U)$ is `CliffordAlgebra (Q.restrict (wSpace Q e f))`).

For §4.5 we have $V$ with a pair $e_1, f_1$ and $U = (Fe_1 + Ff_1)^\perp$ = `uSpace Q e₁ f₁`, and in $U$ a pair
$e_2, f_2$ with $X = (Fe_2 + Ff_2)^\perp \cap U$ = `uSpace (QU Q e₁ f₁) e₂ f₂`; $A(U)$ = `AU Q e₁ f₁` and
$A(X)$ = `AU (QU Q e₁ f₁) e₂ f₂`. Shimura's $\Psi : A(V) \to M_2(A(U))$ is `MatrixModel.psi` for $(e_1, f_1)$
and his $\theta : A(U) \to M_2(A(X))$ (written $\Theta$-small in the book, (4.12)) is `MatrixModel.psi` for the
form `QU Q e₁ f₁` and $(e_2, f_2)$.

**Defines**
* (4.14) $\Theta : A(V) \to M_4(A(X))$ (`thetaBig`, an $F$-algebra homomorphism), the composite of $\Psi$, the entrywise
  $\theta$, and the identification $M_2(M_2(A(X))) = M_4(A(X))$ (`Matrix.compAlgEquiv`, index set $\{0,1\} \times \{0,1\}$,
  ordered lexicographically); the equivalence form is `thetaEquiv`.

**Proves** (all unconditional; standard axioms only)
* Theorem 2.6 for every $s$: $A(V) \cong M_{2^s}(A(U))$ as $F$-algebras (`theorem_2_6`), by induction on $s$
  (the hyperbolic pairs after the first live in $U_1 = (Fe_0 + Ff_0)^\perp$ and `wSpace` of the tail is the same
  subspace of $V$ as `wSpace Q e f`: `wEquiv`);
* (4.14) $\Theta(\alpha) = \begin{pmatrix}\theta(a) & \theta(b) \\ \theta(c) & \theta(d)\end{pmatrix}$ when
  $\Psi(\alpha) = \begin{pmatrix} a & b \\ c & d\end{pmatrix}$ (`thetaBig_apply`, `thetaBig_eq_comp`);
* $\Theta$ is an isomorphism (`thetaBig_bijective`);
* (4.12) $\theta(x + pe_2 + qf_2) = \begin{pmatrix} x & p \\ q & -x\end{pmatrix}$ for $x \in X$, $p, q \in F$
  (`theta_apply_x_add`);
* (4.13) $\theta(y^*) = j\,\theta(y')^*\,j^{-1}$ for $y \in A(U)$ (`theta_reverse`);
* $\Theta(x) = \mathrm{diag}[x, -x, -x, x]$ for $x \in X$ (`thetaBig_ι_X`), used in the proof of Proposition 4.6.
-/
import QuadFormsKB.Literature.Shimura2004.Wave4.MatrixModel
import QuadFormsKB.Literature.Shimura2004.Wave5.Levi
import Mathlib.Data.Matrix.Composition
import Mathlib.LinearAlgebra.Matrix.Reindex
import QuadFormsKB.Citation

open Module CliffordAlgebra

set_option linter.unusedSectionVars false

noncomputable section

universe u

namespace QuadFormsKB.Shimura2004

namespace Theta

open QuadFormsKB.Shimura2004.MatrixModel QuadFormsKB.Shimura2004.Levi

variable {F : Type*} [Field F] [Invertible (2 : F)]

/-! ### Theorem 2.6 for every $s$ -/

section Step

variable {V : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V} {s : ℕ}
  {e f : Fin (s + 1) → V}

theorem polar_QU (e₀ f₀ : V) (x y : uSpace Q e₀ f₀) :
    QuadraticMap.polar (QU Q e₀ f₀) x y = QuadraticMap.polar Q (x : V) (y : V) := rfl

theorem hyp_e0 (hH : IsHypFamily Q e f) : Q (e 0) = 0 := by
  rw [Q_eq_half_polar, hH.polar_e_e, mul_zero]

theorem hyp_f0 (hH : IsHypFamily Q e f) : Q (f 0) = 0 := by
  rw [Q_eq_half_polar, hH.polar_f_f, mul_zero]

theorem hyp_ef0 (hH : IsHypFamily Q e f) : QuadraticMap.polar Q (e 0) (f 0) = 1 := by
  simpa using hH.polar_e_f 0 0

theorem tailE_mem (hH : IsHypFamily Q e f) (i : Fin s) : e i.succ ∈ uSpace Q (e 0) (f 0) := by
  rw [mem_uSpace, hH.polar_e_e, hH.polar_e_f]
  simp [Fin.succ_ne_zero]

theorem tailF_mem (hH : IsHypFamily Q e f) (i : Fin s) : f i.succ ∈ uSpace Q (e 0) (f 0) := by
  rw [mem_uSpace, polar_f_e hH, hH.polar_f_f]
  simp [Fin.succ_ne_zero]

/-- The tail $e_1, \dots, e_{s-1}$ of the hyperbolic family, as vectors of $U = (Fe_0 + Ff_0)^\perp$. -/
def tailE (hH : IsHypFamily Q e f) : Fin s → uSpace Q (e 0) (f 0) := fun i => ⟨e i.succ, tailE_mem hH i⟩

/-- The tail $f_1, \dots, f_{s-1}$ of the hyperbolic family, as vectors of $U = (Fe_0 + Ff_0)^\perp$. -/
def tailF (hH : IsHypFamily Q e f) : Fin s → uSpace Q (e 0) (f 0) := fun i => ⟨f i.succ, tailF_mem hH i⟩

/-- The tails form a hyperbolic family for $\varphi|_U$. -/
theorem tail_hyp (hH : IsHypFamily Q e f) : IsHypFamily (QU Q (e 0) (f 0)) (tailE hH) (tailF hH) where
  polar_e_e i j := by rw [polar_QU]; exact hH.polar_e_e _ _
  polar_f_f i j := by rw [polar_QU]; exact hH.polar_f_f _ _
  polar_e_f i j := by
    rw [polar_QU]
    have := hH.polar_e_f i.succ j.succ
    show QuadraticMap.polar Q (e i.succ) (f j.succ) = _
    simpa [Fin.succ_inj] using this

/-- The orthogonal complement of the tail inside $U$ is the orthogonal complement of the whole family
inside $V$: as a linear equivalence. -/
def wEquiv (hH : IsHypFamily Q e f) :
    wSpace (QU Q (e 0) (f 0)) (tailE hH) (tailF hH) ≃ₗ[F] wSpace Q e f where
  toFun w := ⟨((w : uSpace Q (e 0) (f 0)) : V), by
    intro i
    induction i using Fin.cases with
    | zero => exact mem_uSpace.1 (w : uSpace Q (e 0) (f 0)).2
    | succ j => exact w.2 j⟩
  invFun w := ⟨⟨(w : V), mem_uSpace.2 (w.2 0)⟩, fun j => w.2 j.succ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- `wEquiv` is an isometry for the restricted forms. -/
def wIso (hH : IsHypFamily Q e f) :
    ((QU Q (e 0) (f 0)).restrict (wSpace (QU Q (e 0) (f 0)) (tailE hH) (tailF hH))).IsometryEquiv
      (Q.restrict (wSpace Q e f)) where
  toLinearEquiv := wEquiv hH
  map_app' _ := rfl

end Step

section Base

variable {V : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}

/-- With no hyperbolic pairs, $U = V$. -/
def wIsoZero (e f : Fin 0 → V) : Q.IsometryEquiv (Q.restrict (wSpace Q e f)) where
  toLinearEquiv :=
    { toFun := fun v => ⟨v, fun i => i.elim0⟩
      invFun := fun w => (w : V)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_app' _ := rfl

end Base

/-- $A \cong M_1(A)$ as $F$-algebras (the case $s = 0$ of Theorem 2.6, $2^0 = 1$). -/
def matOneEquiv (A : Type*) [Ring A] [Algebra F A] : A ≃ₐ[F] Matrix (Fin (2 ^ 0)) (Fin (2 ^ 0)) A where
  toFun a := Matrix.of fun _ _ => a
  invFun M := M 0 0
  left_inv _ := rfl
  right_inv M := by
    ext i j
    have hi : i = 0 := Subsingleton.elim (α := Fin 1) _ _
    have hj : j = 0 := Subsingleton.elim (α := Fin 1) _ _
    subst hi hj
    rfl
  map_mul' a b := by
    ext i j
    simp [Matrix.mul_apply]
  map_add' _ _ := by
    ext i j
    rfl
  commutes' r := by
    ext i j
    have hi : i = 0 := Subsingleton.elim (α := Fin 1) _ _
    have hj : j = 0 := Subsingleton.elim (α := Fin 1) _ _
    subst hi hj
    simp [Matrix.algebraMap_matrix_apply]

/-- Theorem 2.6, by induction on $s$ (universe-fixed form). -/
theorem theorem_2_6_aux (s : ℕ) : ∀ {V : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V) (e f : Fin s → V), IsHypFamily Q e f →
      Nonempty (CliffordAlgebra Q ≃ₐ[F]
        Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) (CliffordAlgebra (Q.restrict (wSpace Q e f)))) := by
  induction s with
  | zero =>
    intro V _ _ _ Q e f _
    exact ⟨(CliffordAlgebra.equivOfIsometry (wIsoZero e f)).trans
      (matOneEquiv (CliffordAlgebra (Q.restrict (wSpace Q e f))))⟩
  | succ s ih =>
    intro V _ _ _ Q e f hH
    obtain ⟨φ⟩ := ih (QU Q (e 0) (f 0)) (tailE hH) (tailF hH) (tail_hyp hH)
    refine ⟨(psiEquiv (hyp_e0 hH) (hyp_f0 hH) (hyp_ef0 hH)).trans ?_⟩
    refine (AlgEquiv.mapMatrix φ).trans ?_
    refine (Matrix.compAlgEquiv (Fin 2) (Fin (2 ^ s)) _ F).trans ?_
    refine (Matrix.reindexAlgEquiv F _ (finProdFinEquiv.trans (finCongr (show 2 * 2 ^ s = 2 ^ (s + 1) by ring)))).trans ?_
    exact AlgEquiv.mapMatrix (CliffordAlgebra.equivOfIsometry (wIso hH))

/-- **Theorem 2.6** (Shimura 2004, p. 19): if $V = U + \sum_{i<s}(Fe_i + Ff_i)$ is a weak Witt decomposition
(`IsHypFamily Q e f`, $U$ = `wSpace Q e f` the orthogonal complement of the hyperbolic pairs), then
$A(V) \cong M_{2^s}(A(U))$ as $F$-algebras. -/
@[kb "shimura2004" "Theorem 2.6, p. 19 (A(V) ≅ M_{2^s}(A(U)) for a weak Witt decomposition with s hyperbolic pairs)"]
theorem theorem_2_6 {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V) {s : ℕ} (e f : Fin s → V) (hH : IsHypFamily Q e f) :
    Nonempty (CliffordAlgebra Q ≃ₐ[F]
      Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) (CliffordAlgebra (Q.restrict (wSpace Q e f)))) :=
  theorem_2_6_aux s Q e f hH

/-! ### §4.5: $\theta$ and $\Theta$ -/

section Sec45

variable {V : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
  {e₁ f₁ : V} {e₂ f₂ : uSpace Q e₁ f₁}

section Hyp45

variable (he₁ : Q e₁ = 0) (hf₁ : Q f₁ = 0) (hef₁ : QuadraticMap.polar Q e₁ f₁ = 1)
  (he₂ : QU Q e₁ f₁ e₂ = 0) (hf₂ : QU Q e₁ f₁ f₂ = 0) (hef₂ : QuadraticMap.polar (QU Q e₁ f₁) e₂ f₂ = 1)

include he₂ hf₂ hef₂ in
/-- **Shimura's $\theta : A(U) \to M_2(A(X))$** (4.12), p. 31: the isomorphism of §2.4 applied to the form
$\varphi|_U$ and the weak Witt decomposition $U = X + Fe_2 + Ff_2$ (4.11). -/
@[kb "shimura2004" "(4.11), (4.12), p. 31 (θ : A(U) → M₂(A(X)) from U = X + Fe₂ + Ff₂)"]
def theta : CliffordAlgebra (QU Q e₁ f₁) →ₐ[F] Matrix (Fin 2) (Fin 2) (AU (QU Q e₁ f₁) e₂ f₂) :=
  psi he₂ hf₂ hef₂

include he₂ hf₂ hef₂ in
/-- $\theta$ is bijective (the isomorphism of (4.12)). -/
theorem theta_bijective : Function.Bijective (theta he₂ hf₂ hef₂) := psi_bijective he₂ hf₂ hef₂

include he₂ hf₂ hef₂ in
/-- **(4.12)**, p. 31: $\theta(x + pe_2 + qf_2) = \begin{pmatrix} x & p \\ q & -x\end{pmatrix}$ for $x \in X$,
$p, q \in F$ (here $x \in X \subseteq U$ is regarded as an element of $U$ and $\iota$ is the canonical map of
$U$ into $A(U)$ resp. of $X$ into $A(X)$). -/
@[kb "shimura2004" "(4.12), p. 31 (θ(x + pe₂ + qf₂) = [[x, p], [q, −x]] for x ∈ X, p, q ∈ F)"]
theorem theta_apply_x_add (x : uSpace (QU Q e₁ f₁) e₂ f₂) (p q : F) :
    theta he₂ hf₂ hef₂ (ι (QU Q e₁ f₁) ((x : uSpace Q e₁ f₁) + p • e₂ + q • f₂)) =
      !![ι (QU (QU Q e₁ f₁) e₂ f₂) x, algebraMap F _ p; algebraMap F _ q, -ι (QU (QU Q e₁ f₁) e₂ f₂) x] := by
  have hx := mem_uSpace.1 x.2
  have pf : QuadraticMap.polar (QU Q e₁ f₁) ((x : uSpace Q e₁ f₁) + p • e₂ + q • f₂) f₂ = p := by
    simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, hx.2, hef₂,
      polar_f_f he₂ hf₂ hef₂, smul_eq_mul]
    ring
  have pe : QuadraticMap.polar (QU Q e₁ f₁) ((x : uSpace Q e₁ f₁) + p • e₂ + q • f₂) e₂ = q := by
    simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, hx.1,
      polar_e_e he₂ hf₂ hef₂, polar_f_e he₂ hf₂ hef₂, smul_eq_mul]
    ring
  have hp : proj he₂ hf₂ hef₂ ((x : uSpace Q e₁ f₁) + p • e₂ + q • f₂) = x := by
    apply Subtype.ext
    rw [coe_proj, pf, pe]
    abel
  rw [theta, psi_ι, psiVec_apply, hp, pf, pe]

include he₂ hf₂ hef₂ in
/-- **(4.13)**, p. 31: $\theta(y^*) = j\,\theta(y')^*\,j^{-1}$ for every $y \in A(U)$, where
$j = \begin{pmatrix} 0 & -1 \\ 1 & 0\end{pmatrix}$ (`matJ`), $j^{-1} = -j$ and $\xi^*$ is `matStar` (this is (2.10)
for the pair $(U; e_2, f_2)$). -/
@[kb "shimura2004" "(4.13), p. 31 (θ(y*) = jθ(y')*j⁻¹ for y ∈ A(U))"]
theorem theta_reverse (y : CliffordAlgebra (QU Q e₁ f₁)) :
    theta he₂ hf₂ hef₂ (reverse y) = matJ * matStar (theta he₂ hf₂ hef₂ (involute y)) * -matJ :=
  psi_reverse he₂ hf₂ hef₂ y

include he₁ hf₁ hef₁ he₂ hf₂ hef₂ in
/-- **The equivalence $\Theta : A(V) \cong M_4(A(X))$** of (4.14), p. 31, as an `AlgEquiv`: $\Psi$ followed by
$\theta$ entrywise and the identification $M_2(M_2(A(X))) = M_4(A(X))$ (rows indexed by pairs
$(i, k) \in \{0,1\}^2$, lexicographically). -/
def thetaEquiv : CliffordAlgebra Q ≃ₐ[F]
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (AU (QU Q e₁ f₁) e₂ f₂) :=
  (psiEquiv he₁ hf₁ hef₁).trans
    ((AlgEquiv.mapMatrix (AlgEquiv.ofBijective (theta he₂ hf₂ hef₂) (theta_bijective he₂ hf₂ hef₂))).trans
      (Matrix.compAlgEquiv (Fin 2) (Fin 2) _ F))

include he₁ hf₁ hef₁ he₂ hf₂ hef₂ in
/-- **Shimura's $\Theta : A(V) \to M_4(A(X))$** (4.14), p. 31: the $F$-algebra homomorphism
$\Theta(\alpha) = \begin{pmatrix}\theta(a) & \theta(b) \\ \theta(c) & \theta(d)\end{pmatrix}$ when
$\Psi(\alpha) = \begin{pmatrix} a & b \\ c & d\end{pmatrix}$, as a $4 \times 4$ matrix over $A(X)$ with rows
indexed by $(i, k) \in \{0,1\}^2$ (`Matrix.comp`). It is an isomorphism (`thetaBig_bijective`). -/
@[kb "shimura2004" "(4.14), p. 31 (Θ : A(V) → M₄(A(X)), Θ(α) = [[θ(a), θ(b)], [θ(c), θ(d)]] for Ψ(α) = [[a, b], [c, d]])"]
def thetaBig : CliffordAlgebra Q →ₐ[F] Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (AU (QU Q e₁ f₁) e₂ f₂) :=
  (Matrix.compAlgEquiv (Fin 2) (Fin 2) _ F).toAlgHom.comp
    ((AlgHom.mapMatrix (theta he₂ hf₂ hef₂)).comp (psi he₁ hf₁ hef₁))

include he₁ hf₁ hef₁ he₂ hf₂ hef₂ in
/-- **(4.14)**, p. 31, entrywise: the entry of $\Theta(\alpha)$ in row $(i, k)$, column $(j, l)$ is the $(k, l)$
entry of $\theta(\Psi(\alpha)_{ij})$ ($i, j$ the block indices). -/
theorem thetaBig_apply (α : CliffordAlgebra Q) (i j k l : Fin 2) :
    thetaBig he₁ hf₁ hef₁ he₂ hf₂ hef₂ α (i, k) (j, l) =
      theta he₂ hf₂ hef₂ (psi he₁ hf₁ hef₁ α i j) k l := rfl

include he₁ hf₁ hef₁ he₂ hf₂ hef₂ in
/-- **(4.14)**, p. 31, as an identity of `Matrix.comp`: $\Theta(\alpha)$ is the block matrix with blocks
$\theta(a), \theta(b), \theta(c), \theta(d)$ when $\Psi(\alpha) = \begin{pmatrix} a & b \\ c & d
\end{pmatrix}$. -/
@[kb "shimura2004" "(4.14), p. 31 (Θ(α) is the block matrix [[θ(a), θ(b)], [θ(c), θ(d)]] when Ψ(α) = [[a, b], [c, d]])"]
theorem thetaBig_eq_comp (α : CliffordAlgebra Q) (a b c d : CliffordAlgebra (QU Q e₁ f₁))
    (h : psi he₁ hf₁ hef₁ α = !![a, b; c, d]) :
    thetaBig he₁ hf₁ hef₁ he₂ hf₂ hef₂ α =
      Matrix.comp (Fin 2) (Fin 2) (Fin 2) (Fin 2) _
        !![theta he₂ hf₂ hef₂ a, theta he₂ hf₂ hef₂ b; theta he₂ hf₂ hef₂ c, theta he₂ hf₂ hef₂ d] := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [thetaBig_apply, h]
  fin_cases i <;> fin_cases j <;> rfl

include he₁ hf₁ hef₁ he₂ hf₂ hef₂ in
/-- **$\Theta$ is an isomorphism** of $A(V)$ onto $M_4(A(X))$ (Shimura, p. 31, after (4.14)). -/
@[kb "shimura2004" "(4.14), p. 31 (Θ is an isomorphism of A(V) onto M₄(A(X)))"]
theorem thetaBig_bijective : Function.Bijective (thetaBig he₁ hf₁ hef₁ he₂ hf₂ hef₂) :=
  (thetaEquiv he₁ hf₁ hef₁ he₂ hf₂ hef₂).bijective

include he₁ hf₁ hef₁ he₂ hf₂ hef₂ in
/-- **$\Theta(x) = \mathrm{diag}[x, -x, -x, x]$** for $x \in X$ (p. 32, used in the proof of Proposition 4.6; the
index order is $(0,0), (0,1), (1,0), (1,1)$). Here $x \in X \subseteq U \subseteq V$. -/
@[kb "shimura2004" "§4.5, pp. 31–32 (Θ(x) = diag[x, −x, −x, x] for x ∈ X, before Proposition 4.6)"]
theorem thetaBig_ι_X (x : uSpace (QU Q e₁ f₁) e₂ f₂) :
    thetaBig he₁ hf₁ hef₁ he₂ hf₂ hef₂ (ι Q (((x : uSpace Q e₁ f₁)) : V)) =
      Matrix.diagonal (fun p : Fin 2 × Fin 2 =>
        if p.1 = p.2 then ι (QU (QU Q e₁ f₁) e₂ f₂) x else -ι (QU (QU Q e₁ f₁) e₂ f₂) x) := by
  have h1 := psi_ι_of_mem he₁ hf₁ hef₁ (x : uSpace Q e₁ f₁)
  have h2 : theta he₂ hf₂ hef₂ (ι (QU Q e₁ f₁) (x : uSpace Q e₁ f₁)) =
      !![ι (QU (QU Q e₁ f₁) e₂ f₂) x, 0; 0, -ι (QU (QU Q e₁ f₁) e₂ f₂) x] :=
    psi_ι_of_mem he₂ hf₂ hef₂ x
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [thetaBig_apply, h1]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [h2, map_neg]

end Hyp45

end Sec45

end Theta

end QuadFormsKB.Shimura2004
