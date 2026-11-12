/-
# Chenevier–Lannes, §1.3: Siegel theta series, Siegel modular forms, Theorem D

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §1.3 (pp. 6–9), §4.5 (pp. 116–118) and §5.1 (p. 123). Printed page numbers.

**Layer.** Functions on complex $g \times g$ matrices; even unimodular lattices as integral forms
(`EvenUnimodular.lean`). Mathlib has modular forms only in genus $1$; the genus-$g$ objects are defined here, minimally:

- `siegelUpper g` ($\mathbb{H}_g$): symmetric $Z \in M_g(\mathbb{C})$ with $\operatorname{Im} Z$ positive definite;
- `sp2gZ g` ($\mathrm{Sp}_{2g}(\mathbb{Z})$): Mathlib's `Matrix.symplecticGroup (Fin g) ℤ`, acting by
  $\gamma \cdot Z = (AZ + B)(CZ + D)^{-1}$ (`spAct`);
- `IsSiegelModularForm k g f` ($f \in M_k(\mathrm{Sp}_{2g}(\mathbb{Z}))$): holomorphic on $\mathbb{H}_g$, of weight $k$,
  bounded on $\{\operatorname{Im} Z \ge 1\}$; `IsSiegelCuspForm` (in $S_k$): moreover Siegel's operator $\Phi$ kills it;
- `siegelTheta g Q` ($\vartheta_g(L)$): $Z \mapsto \sum_{X \in M_{n \times g}(\mathbb{Z})} e^{i\pi\,\mathrm{tr}(X^{\mathsf T}HXZ)}$.

**States** (named propositions): `TheoremD` (p. 9), `WittIgusa` ((1.3.2), p. 7; (5.2.2), p. 125), `SiegelThetaModular`
(Siegel, §5.1, p. 123), `ThetaFourDistinct` (§5.2, pp. 125–126) and `DimCuspEightGenusFour` ((5.2.3), p. 126).

**Proves** (unconditional): `wittIgusa_genus_one` (the case $g = 1$ of (1.3.2), from Witt's equality of representation
numbers `Lattices.witt_sixteen`); `siegelTheta_zero`, `thetaMap_zero`, `mem_thetaKer_zero_iff` (genus $0$:
$\vartheta_0 = 1$, and $\mathrm{Ker}\,\vartheta_0$ is the hyperplane $\sum_x a_x = 0$).

*Conventions.* Holomorphy in the $g(g+1)/2$ independent entries of a symmetric $Z$ is expressed as complex
differentiability of $W \mapsto f(\tfrac12(W + W^{\mathsf T}))$ on the open set of all $W$ whose symmetrization lies in
$\mathbb{H}_g$. The book (§4.5.1, p. 117) asks for boundedness only when $g = 1$ (on $\operatorname{Im}\tau > 1$); here
boundedness on $\{\operatorname{Im} Z - 1 \ge 0\}$ is asked for every $g$, which is automatic for $g \ge 2$ (Koecher's
principle), so the spaces agree. The book defines cusp forms as the kernel of Siegel's operator $\Phi$ on Fourier
expansions (§4.5.2, p. 118); here $\Phi f$ is the limit $\lim_{t \to \infty} f\begin{pmatrix}Z'&0\\0&it\end{pmatrix}$, the
same operator (the Fourier series converges normally on $\{\operatorname{Im} Z \ge 1\}$). Spaces of forms are taken as `Submodule.span` of the set of forms (the set is already a vector
space; taking the span avoids proving the closure properties here).
-/
import QuadFormsKB.Literature.ChenevierLannes.EvenUnimodular
import QuadFormsKB.Literature.Cassels.AppBSec5
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix Complex Filter

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Lattices

/-! ### The Siegel upper half space and $\mathrm{Sp}_{2g}(\mathbb{Z})$ -/

/-- **The Siegel upper half space** $\mathbb{H}_g$ (Chenevier–Lannes, §4.5.1, p. 116): the symmetric complex $g \times g$ matrices
$Z$ whose imaginary part $\operatorname{Im} Z$ is positive definite. -/
@[kb "chenevierlannes2019" "§4.5.1, p. 116 (Siegel upper half space)"]
def siegelUpper (g : ℕ) : Set (Matrix (Fin g) (Fin g) ℂ) :=
  {Z | Zᵀ = Z ∧ (Z.map Complex.im).PosDef}

/-- **$\mathrm{Sp}_{2g}(\mathbb{Z})$**: the integral $2g \times 2g$ matrices $\gamma$ with $\gamma^{\mathsf T}J\gamma = J$
(Mathlib's `Matrix.symplecticGroup`, indexed by $\mathrm{Fin}\,g \oplus \mathrm{Fin}\,g$). -/
abbrev sp2gZ (g : ℕ) := Matrix.symplecticGroup (Fin g) ℤ

/-- The blocks $A, B, C, D$ of $\gamma = \begin{pmatrix}A&B\\C&D\end{pmatrix}$, as complex matrices. -/
def spBlockC {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ :=
  γ.map (Int.cast)

/-- **The factor of automorphy** $\det(CZ + D)$. -/
noncomputable def spJ {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (Z : Matrix (Fin g) (Fin g) ℂ) : ℂ :=
  ((spBlockC γ).toBlocks₂₁ * Z + (spBlockC γ).toBlocks₂₂).det

/-- **The action** $\gamma \cdot Z = (AZ + B)(CZ + D)^{-1}$ of $\mathrm{Sp}_{2g}(\mathbb{Z})$ on $\mathbb{H}_g$. -/
noncomputable def spAct {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (Z : Matrix (Fin g) (Fin g) ℂ) :
    Matrix (Fin g) (Fin g) ℂ :=
  ((spBlockC γ).toBlocks₁₁ * Z + (spBlockC γ).toBlocks₁₂) *
    ((spBlockC γ).toBlocks₂₁ * Z + (spBlockC γ).toBlocks₂₂)⁻¹

/-! ### Siegel modular forms and cusp forms -/

/-- **A Siegel modular form of weight $k$ and genus $g$ for $\mathrm{Sp}_{2g}(\mathbb{Z})$** (Chenevier–Lannes, §1.3,
p. 6, and §4.5.1, pp. 116–117; scalar-valued). Fields: `holo` (holomorphic on $\mathbb{H}_g$ in the independent entries, see the module
docstring), `modular` ($f(\gamma \cdot Z) = \det(CZ + D)^k f(Z)$ for $\gamma \in \mathrm{Sp}_{2g}(\mathbb{Z})$,
$Z \in \mathbb{H}_g$), `bounded` ($f$ is bounded on $\{Z \in \mathbb{H}_g : \operatorname{Im} Z - 1 \text{ positive
semidefinite}\}$). Only the values on $\mathbb{H}_g$ matter. -/
@[kb "chenevierlannes2019" "§1.3, p. 6; §4.5.1, pp. 116–117 (M_k(Sp_2g(Z)))"]
structure IsSiegelModularForm (k : ℤ) (g : ℕ) (f : Matrix (Fin g) (Fin g) ℂ → ℂ) : Prop where
  /-- Holomorphy on $\mathbb{H}_g$. -/
  holo : DifferentiableOn ℂ (fun W => f ((1 / 2 : ℂ) • (W + Wᵀ)))
    {W | (1 / 2 : ℂ) • (W + Wᵀ) ∈ siegelUpper g}
  /-- The transformation law of weight $k$. -/
  modular : ∀ γ ∈ sp2gZ g, ∀ Z ∈ siegelUpper g, f (spAct γ Z) = spJ γ Z ^ k * f Z
  /-- Boundedness at the cusp. -/
  bounded : ∃ C : ℝ, ∀ Z ∈ siegelUpper g, (Z.map Complex.im - 1).PosSemidef → ‖f Z‖ ≤ C

/-- The block-diagonal matrix $\begin{pmatrix}Z'&0\\0&it\end{pmatrix}$ of size $g + 1$. -/
def phiEmbed {g : ℕ} (Z' : Matrix (Fin g) (Fin g) ℂ) (t : ℝ) : Matrix (Fin (g + 1)) (Fin (g + 1)) ℂ :=
  Matrix.of fun i j =>
    Fin.lastCases (Fin.lastCases (I * t) (fun _ => 0) j) (fun i' => Fin.lastCases 0 (fun j' => Z' i' j') j) i

/-- **A Siegel cusp form of weight $k$ and genus $g + 1$** (Chenevier–Lannes, §1.3, p. 7, and §4.5.2, p. 118: the subspace
$S_k(\mathrm{Sp}_{2g+2}(\mathbb{Z}))$): a Siegel modular form killed by Siegel's operator
$\Phi f(Z') = \lim_{t \to +\infty} f\begin{pmatrix}Z'&0\\0&it\end{pmatrix}$ ($Z' \in \mathbb{H}_g$). For level one this
is the usual definition (vanishing of $\Phi(f|\gamma)$ for all $\gamma$ reduces to $\Phi f = 0$ by modularity). -/
@[kb "chenevierlannes2019" "§1.3, p. 7; §4.5.2, p. 118 (S_k(Sp_2g(Z)))"]
structure IsSiegelCuspForm (k : ℤ) (g : ℕ) (f : Matrix (Fin (g + 1)) (Fin (g + 1)) ℂ → ℂ) : Prop where
  /-- $f$ is a Siegel modular form. -/
  modularForm : IsSiegelModularForm k (g + 1) f
  /-- $\Phi f = 0$. -/
  phi_zero : ∀ Z' ∈ siegelUpper g, Tendsto (fun t : ℝ => f (phiEmbed Z' t)) atTop (nhds 0)

/-- **The space $S_k(\mathrm{Sp}_{2g+2}(\mathbb{Z}))$** (as the span of the cusp forms; see the module docstring). -/
noncomputable def cuspFormSpace (k : ℤ) (g : ℕ) : Submodule ℂ (Matrix (Fin (g + 1)) (Fin (g + 1)) ℂ → ℂ) :=
  Submodule.span ℂ {f | IsSiegelCuspForm k g f}

/-! ### Siegel theta series -/

/-- **The Siegel theta series of genus $g$** of the lattice with Gram matrix $H$ (Chenevier–Lannes, §1.3, p. 6, and
§5.1, p. 123):
$$\vartheta_g(L)(Z) = \sum_{v \in L^g} e^{i\pi\,\mathrm{tr}((v \cdot v) Z)}
= \sum_{X \in M_{n \times g}(\mathbb{Z})} e^{i\pi\,\mathrm{tr}(X^{\mathsf T}HXZ)},$$
where $v \cdot v = X^{\mathsf T}HX$ is the $g \times g$ Gram matrix of the $g$ vectors (columns of $X$). For an even
unimodular $L$ of dimension $n$ it lies in $M_{n/2}(\mathrm{Sp}_{2g}(\mathbb{Z}))$ (not proved here). A `tsum`; it
converges absolutely on $\mathbb{H}_g$ for positive definite $H$. -/
@[kb "chenevierlannes2019" "§1.3, p. 6; §5.1, p. 123 (Siegel theta series)"]
noncomputable def siegelTheta {n : ℕ} (g : ℕ) (Q : QuadForm ℤ n) (Z : Matrix (Fin g) (Fin g) ℂ) : ℂ :=
  ∑' X : Matrix (Fin n) (Fin g) ℤ,
    Complex.exp (Real.pi * I * ((Xᵀ * Q.hessian * X).map (Int.cast : ℤ → ℂ) * Z).trace)

/-- **Siegel's theorem** (Chenevier–Lannes, §5.1, p. 123, citing Freitag [88, Kap. I, Sect. 0]; named statement): for an
even unimodular lattice $L$ of dimension $n$ and every genus $g \ge 1$, $\vartheta_g(L) \in M_{n/2}(\mathrm{Sp}_{2g}(\mathbb{Z}))$.
(Only the values on $\mathbb{H}_g$ enter `IsSiegelModularForm`.) -/
@[kb "chenevierlannes2019" "§5.1, p. 123 (ϑ_g(L) ∈ M_{n/2}(Sp_2g(Z)))"]
def SiegelThetaModular : Prop :=
  ∀ (n : ℕ) (Q : QuadForm ℤ n), IsEvenUnimodular Q → ∀ g : ℕ, 1 ≤ g →
    IsSiegelModularForm ((n / 2 : ℕ) : ℤ) g (siegelTheta g Q)

/-- **Genus $0$**: $\vartheta_0(L) = 1$ (the sum has the single term $X = $ the empty $n \times 0$ matrix). Unconditional;
this is the convention $\vartheta_0([L]) = 1$ of Chenevier–Lannes, §5.1, p. 123. -/
@[kb "chenevierlannes2019" "§5.1, p. 123 (ϑ_0 = 1)"]
theorem siegelTheta_zero {n : ℕ} (Q : QuadForm ℤ n) (Z : Matrix (Fin 0) (Fin 0) ℂ) : siegelTheta 0 Q Z = 1 := by
  unfold siegelTheta
  rw [tsum_eq_single 0 fun X hX => absurd (Matrix.ext fun _ j => j.elim0) hX]
  simp [Matrix.trace]

/-- **The linear map $\vartheta_g : \mathbb{C}[X_n] \to M_{n/2}(\mathrm{Sp}_{2g}(\mathbb{Z}))$** (Chenevier–Lannes, §1.3,
p. 6): $\sum_x a_x x \mapsto \sum_x a_x \vartheta_g(x)$, with $\vartheta_g(x)$ the theta series of the chosen
representative of $x$; for $g = 0$, $\vartheta_0(x) = 1$ (the convention of footnote 4, p. 7). -/
@[kb "chenevierlannes2019" "§1.3, pp. 6–7 (the map ϑ_g)"]
noncomputable def thetaMap (n g : ℕ) (a : QClass n → ℂ) (Z : Matrix (Fin g) (Fin g) ℂ) : ℂ :=
  ∑ x ∈ (classSet_finite n).toFinset, a x * siegelTheta g (Quotient.out (s := intSetoid n) x) Z

/-- **$\mathrm{Ker}\,\vartheta_g$**: the coefficient vectors on $X_n$ whose theta combination vanishes on $\mathbb{H}_g$
(only the coefficients on $X_n$ matter). -/
def thetaKer (n g : ℕ) : Set (QClass n → ℂ) := {a | ∀ Z ∈ siegelUpper g, thetaMap n g a Z = 0}

/-- **$\vartheta_0(\sum_x a_x x) = \sum_{x \in X_n} a_x$** (Chenevier–Lannes, §5.1, p. 123). Unconditional. -/
theorem thetaMap_zero (n : ℕ) (a : QClass n → ℂ) (Z : Matrix (Fin 0) (Fin 0) ℂ) :
    thetaMap n 0 a Z = ∑ x ∈ (classSet_finite n).toFinset, a x := by
  unfold thetaMap
  simp only [siegelTheta_zero, mul_one]

/-- **$\mathrm{Ker}\,\vartheta_0$ is the hyperplane $\sum_{x \in X_n} a_x = 0$** (Chenevier–Lannes, §5.1, p. 124: "$\mathrm{Ker}\,
\vartheta_0$ has codimension $1$"). Unconditional ($\mathbb{H}_0$ is the single point, the empty matrix). -/
@[kb "chenevierlannes2019" "§5.1, p. 124 (Ker ϑ_0)"]
theorem mem_thetaKer_zero_iff (n : ℕ) (a : QClass n → ℂ) :
    a ∈ thetaKer n 0 ↔ ∑ x ∈ (classSet_finite n).toFinset, a x = 0 := by
  have h0 : (0 : Matrix (Fin 0) (Fin 0) ℂ) ∈ siegelUpper 0 :=
    ⟨Subsingleton.elim _ _, by
      rw [show (0 : Matrix (Fin 0) (Fin 0) ℂ).map Complex.im = 1 from Subsingleton.elim _ _]
      exact Matrix.PosDef.one⟩
  constructor
  · intro h
    rw [← thetaMap_zero n a 0]
    exact h 0 h0
  · intro h Z _
    rw [thetaMap_zero]
    exact h

/-! ### Theorem D -/

/-- The table of $\dim S_{12}(\mathrm{Sp}_{2g}(\mathbb{Z}))$, $g = 1, \dots, 12$ (Theorem D, p. 9), indexed by $g - 1$. -/
def dimS12Table : Fin 12 → ℕ := ![1, 1, 1, 2, 2, 3, 3, 4, 2, 2, 1, 1]

/-- **Theorem D** (Chenevier–Lannes, §1.3, p. 9; named statement, proved in the book in §9.5): for every genus
$1 \le g \le 12$,
- (`surj`) $\vartheta_g : \mathbb{C}[X_{24}] \to M_{12}(\mathrm{Sp}_{2g}(\mathbb{Z}))$ is surjective: every Siegel modular
  form of weight $12$ and genus $g$ agrees on $\mathbb{H}_g$ with a combination of theta series of Niemeier lattices;
- (`ker_image`) $\vartheta_g$ maps $\mathrm{Ker}\,\vartheta_{g-1}$ onto $S_{12}(\mathrm{Sp}_{2g}(\mathbb{Z}))$ (so
  $\mathrm{Ker}\,\vartheta_{g-1}/\mathrm{Ker}\,\vartheta_g \cong S_{12}$; the map (1.3.1) is always injective):
  the theta combinations of elements of $\mathrm{Ker}\,\vartheta_{g-1}$ are exactly the cusp forms, on $\mathbb{H}_g$;
- (`dim`) $\dim S_{12}(\mathrm{Sp}_{2g}(\mathbb{Z})) = 1, 1, 1, 2, 2, 3, 3, 4, 2, 2, 1, 1$ for $g = 1, \dots, 12$.
Written with $g = g' + 1$, $g' = 0, \dots, 11$. -/
@[kb "chenevierlannes2019" "Thm. D, p. 9"]
def TheoremD : Prop :=
  ∀ g' : Fin 12,
    (∀ f, IsSiegelModularForm 12 (g' + 1) f →
      ∃ a : QClass 24 → ℂ, ∀ Z ∈ siegelUpper (g' + 1), f Z = thetaMap 24 (g' + 1) a Z) ∧
    (∀ f, IsSiegelCuspForm 12 g' f ↔
      IsSiegelModularForm 12 (g' + 1) f ∧
        ∃ a ∈ thetaKer 24 g', ∀ Z ∈ siegelUpper (g' + 1), f Z = thetaMap 24 (g' + 1) a Z) ∧
    Module.finrank ℂ (cuspFormSpace 12 g') = dimS12Table g'

/-! ### The Witt–Igusa identities -/

/-- **The Witt–Igusa identities** (1.3.2) (Chenevier–Lannes, §1.3, p. 7; named statement; Kneser's proof is in
Appendix A): $\vartheta_g(E_8 \oplus E_8) = \vartheta_g(E_{16})$ for $g \le 3$, i.e. the two lattices represent every
positive integral quadratic form of rank at most $3$ the same number of times. -/
@[kb "chenevierlannes2019" "(1.3.2), p. 7 (Witt–Igusa)"]
def WittIgusa : Prop :=
  ∀ g : ℕ, g ≤ 3 → ∀ Z ∈ siegelUpper g, siegelTheta g twoE8 Z = siegelTheta g gamma16 Z

/-- **Genus $4$: $\vartheta_4(E_8 \oplus E_8) \ne \vartheta_4(E_{16})$** (Chenevier–Lannes, §5.2, p. 125, Proposition 5.2.1
and "Thus, we have $\mathrm{Ker}\,\vartheta_4 = 0$", p. 126; named statement): the difference
$F = \vartheta_4(E_8 \oplus E_8) - \vartheta_4(E_{16}) \in S_8(\mathrm{Sp}_8(\mathbb{Z}))$ is not zero (it is proportional
to Schottky's form, Igusa). The book proves it by computing two Fourier coefficients of $F$
($c_{D_4}/|O(D_4)| = 4480$, $c_{A_4}/|O(A_4)| = -21504$). So (1.3.2) is sharp. -/
@[kb "chenevierlannes2019" "Prop. 5.2.1, p. 125; §5.2, p. 126 (F ≠ 0)"]
def ThetaFourDistinct : Prop :=
  ∃ Z ∈ siegelUpper 4, siegelTheta 4 twoE8 Z ≠ siegelTheta 4 gamma16 Z

/-- **(5.2.3): $\dim S_8(\mathrm{Sp}_8(\mathbb{Z})) = 1$** (Chenevier–Lannes, §5.2, p. 126, due to Poor and Yen; also
Theorem 9.5.9; named statement). `cuspFormSpace 8 3` is $S_8(\mathrm{Sp}_{2 \cdot 4}(\mathbb{Z}))$ (genus $3 + 1$). -/
@[kb "chenevierlannes2019" "(5.2.3), p. 126"]
def DimCuspEightGenusFour : Prop := Module.finrank ℂ (cuspFormSpace 8 3) = 1

/-- Helper: the summand of `siegelTheta 1 Q Z` at `X` depends only on the column `x = X·0`, through `2 Q(x)`. -/
private theorem siegelTheta_one_summand {n : ℕ} (Q : QuadForm ℤ n) (Z : Matrix (Fin 1) (Fin 1) ℂ)
    (X : Matrix (Fin n) (Fin 1) ℤ) :
    Complex.exp (Real.pi * I * ((Xᵀ * Q.hessian * X).map (Int.cast : ℤ → ℂ) * Z).trace) =
      Complex.exp (Real.pi * I * (((2 * Q.eval (fun i => X i 0) : ℤ) : ℂ) * Z 0 0)) := by
  have h : (Xᵀ * Q.hessian * X) 0 0 = 2 * Q.eval (fun i => X i 0) := by
    rw [LocalDensity.two_mul_eval_eq_hessian]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  generalize Xᵀ * Q.hessian * X = A at h ⊢
  simp [Matrix.trace, Matrix.mul_apply, h]

/-- Helper: the theta series in genus one as a sum over vectors in `ℤⁿ`. -/
private theorem siegelTheta_one_eq {n : ℕ} (Q : QuadForm ℤ n) (Z : Matrix (Fin 1) (Fin 1) ℂ) :
    siegelTheta 1 Q Z =
      ∑' x : Fin n → ℤ, Complex.exp (Real.pi * I * (((2 * Q.eval x : ℤ) : ℂ) * Z 0 0)) := by
  let e : Matrix (Fin n) (Fin 1) ℤ ≃ (Fin n → ℤ) :=
    { toFun := fun X i => X i 0
      invFun := fun x => Matrix.of fun i _ => x i
      left_inv := fun X => by ext i j; fin_cases j; rfl
      right_inv := fun x => rfl }
  unfold siegelTheta
  rw [tsum_congr (siegelTheta_one_summand Q Z)]
  exact e.tsum_eq (fun x : Fin n → ℤ => Complex.exp (Real.pi * I * (((2 * Q.eval x : ℤ) : ℂ) * Z 0 0)))

/-- Helper: a bijection of `ℤ¹⁶` carrying `twoE8` to `gamma16` (from Witt's equality of representation numbers). -/
private theorem exists_equiv_twoE8_gamma16 :
    ∃ E : (Fin 16 → ℤ) ≃ (Fin 16 → ℤ), ∀ x, gamma16.eval (E x) = twoE8.eval x := by
  have φ : ∀ m : ℤ, Nonempty ({x // twoE8.eval x = m} ≃ {x // gamma16.eval x = m}) := by
    intro m
    have h1 : Finite {x // twoE8.eval x = m} := (IntQF.PosDef.repSet_finite twoE8_posDef m).to_subtype
    have h2 : Finite {x // gamma16.eval x = m} := (IntQF.PosDef.repSet_finite gamma16_posDef m).to_subtype
    exact Finite.card_eq.mp (witt_sixteen.2.2 m).symm
  have ψ : ∀ m : ℤ, {x // twoE8.eval x = m} ≃ {x // gamma16.eval x = m} := fun m => (φ m).some
  refine ⟨(Equiv.sigmaFiberEquiv (fun x => twoE8.eval x)).symm.trans
    ((Equiv.sigmaCongrRight fun m => (ψ m)).trans (Equiv.sigmaFiberEquiv (fun x => gamma16.eval x))),
    fun x => ?_⟩
  exact (ψ (twoE8.eval x) ⟨x, rfl⟩).2

/-- **The case $g = 1$ of (1.3.2)** (Chenevier–Lannes, §1.3, p. 7: "well known in genus $g = 1$, as a consequence of the
vanishing $S_8(\mathrm{SL}_2(\mathbb{Z})) = 0$"): $\vartheta_1(E_8 \oplus E_8) = \vartheta_1(E_{16})$, as functions on all
of $M_1(\mathbb{C})$. Unconditional: the two forms have the same representation numbers (`Lattices.witt_sixteen`), so
a bijection $\mathbb{Z}^{16} \to \mathbb{Z}^{16}$ carrying one form to the other reindexes the series. -/
@[kb "chenevierlannes2019" "(1.3.2), p. 7 (g = 1)"]
theorem wittIgusa_genus_one (Z : Matrix (Fin 1) (Fin 1) ℂ) : siegelTheta 1 twoE8 Z = siegelTheta 1 gamma16 Z := by
  rw [siegelTheta_one_eq, siegelTheta_one_eq]
  obtain ⟨E, hE⟩ := exists_equiv_twoE8_gamma16
  symm
  rw [← E.tsum_eq]
  exact tsum_congr fun x => by rw [hE]

end QuadFormsKB.ChenevierLannes
