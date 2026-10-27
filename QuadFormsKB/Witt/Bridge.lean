/-
# Witt cancellation for our `QuadForm`, over ℚ and ℚ_p

This file restates Witt cancellation (`QuadraticForm.equivalent_of_prod_equivalent_prod`) for this
repository's primary definition `QuadForm R n` (a polynomial $\sum_{i \le j} c_{ij} x_i x_j$ with
upper-triangular coefficient matrix $C$; `Defs/QuadForm.lean`), through the conversion to Mathlib
of `Equiv/Mathlib.lean`.

**New definition.** `QuadForm.orthSum Q₁ Q₂` ($Q_1 \perp Q_2$): for $Q_1$ in $m$ variables and $Q_2$
in $n$ variables, the form in $m + n$ variables
$$(Q_1 \perp Q_2)(x_0, \dots, x_{m+n-1}) = Q_1(x_0, \dots, x_{m-1}) + Q_2(x_m, \dots, x_{m+n-1})$$
(block-diagonal coefficient matrix; `evalIn_orthSum`).

**Main results.**
* `QuadForm.isometricIn_of_orthSum`: for fields $F \subseteq K$ (any characteristic, any
  `Algebra F K`), forms $Q$ ($k$ variables) and $Q_1, Q_2$ ($n$ variables) over $F$ with $Q$, $Q_1$
  nondegenerate (`QuadForm.Nondegenerate`: $\det(C + C^{\mathsf T}) \neq 0$), if
  $Q \perp Q_1 \cong Q \perp Q_2$ over $K$ then $Q_1 \cong Q_2$ over $K$.
* `RatQF.isometric_of_orthSum` ($F = K = \mathbb{Q}$) and `RatQF.isometricIn_padic_of_orthSum`
  ($F = \mathbb{Q}$, $K = \mathbb{Q}_p$): the Witt-cancellation statements.

`QuadForm.Nondegenerate` is $\det H \neq 0$ for the Hessian $H = C + C^{\mathsf T}$, the Gram
matrix of the polar form $b$. So it says $Q$ is *nonsingular*, in every characteristic, and the
general theorem applies.

**Related ad hoc arguments in the repository (not refactored).** `Siegel/NeighborCount.lean`
counts vectors in $\vec{x}^\perp$ over $\mathbb{F}_p$ by an elementary argument that avoids Witt's
theorem; `LocalDensity/FormDensitySelf.lean` notes that the closed form for $|O_n(\mathbb{F}_q)|$
needs Witt's theorem over $\mathbb{F}_q$ (now available: `QuadraticForm.exists_isometryEquiv_apply_eq_of_nondegenerate`).
-/
import QuadFormsKB.Witt.Decomposition
import QuadFormsKB.Equiv.Mathlib
import QuadFormsKB.Defs.Rational

open Module QuadraticMap Matrix

namespace QuadFormsKB.QuadForm

variable {R : Type*} [CommRing R] {k m n : ℕ}

/-- **The orthogonal sum** $Q_1 \perp Q_2$ of a form $Q_1$ in $m$ variables and a form $Q_2$ in $n$
variables: the form in $m + n$ variables with block-diagonal coefficient matrix
$\begin{pmatrix} C_1 & 0 \\ 0 & C_2 \end{pmatrix}$, i.e.
$(Q_1 \perp Q_2)(\vec{x}) = Q_1(x_0, \dots, x_{m-1}) + Q_2(x_m, \dots, x_{m+n-1})$
(`evalIn_orthSum`). Indices are 0-based; $Q_2$'s variable $y_b$ becomes $x_{m+b}$. -/
def orthSum (Q₁ : QuadForm R m) (Q₂ : QuadForm R n) : QuadForm R (m + n) :=
  ofUpper fun i j =>
    Fin.addCases (fun a => Fin.addCases (fun b => Q₁.coeff a b) (fun _ => 0) j)
      (fun a => Fin.addCases (fun _ => 0) (fun b => Q₂.coeff a b) j) i

/-- **Values of the orthogonal sum:** $(Q_1 \perp Q_2)(\vec{x}) = Q_1(x_0, \dots, x_{m-1}) +
Q_2(x_m, \dots, x_{m+n-1})$ over every $R$-algebra $K$. -/
theorem evalIn_orthSum (K : Type*) [CommRing K] [Algebra R K] (Q₁ : QuadForm R m)
    (Q₂ : QuadForm R n) (x : Fin (m + n) → K) :
    (orthSum Q₁ Q₂).evalIn K x =
      Q₁.evalIn K (fun a => x (Fin.castAdd n a)) + Q₂.evalIn K (fun b => x (Fin.natAdd m b)) := by
  simp only [evalIn, Fin.sum_univ_add, orthSum, ofUpper, Matrix.of_apply, Fin.addCases_left,
    Fin.addCases_right]
  have h1 : ∀ (a : Fin m) (b : Fin n), Fin.castAdd n a ≤ Fin.natAdd m b := fun a b =>
    Fin.le_iff_val_le_val.mpr (by show a.val ≤ m + b.val; omega)
  have h2 : ∀ (a : Fin n) (b : Fin m), ¬ Fin.natAdd m a ≤ Fin.castAdd n b := fun a b h => by
    have := Fin.le_iff_val_le_val.mp h
    change m + a.val ≤ b.val at this
    omega
  have h3 : ∀ a b : Fin m, Fin.castAdd n a ≤ Fin.castAdd n b ↔ a ≤ b := fun a b =>
    Fin.le_iff_val_le_val.trans (Fin.le_iff_val_le_val (a := a) (b := b)).symm
  have h4 : ∀ a b : Fin n, Fin.natAdd m a ≤ Fin.natAdd m b ↔ a ≤ b := fun a b => by
    rw [Fin.le_iff_val_le_val, Fin.le_iff_val_le_val (a := a)]
    change m + a.val ≤ m + b.val ↔ _
    omega
  simp only [h1, h2, h3, h4, ite_true, ite_false, map_zero, zero_mul, Finset.sum_const_zero,
    add_zero, zero_add]
  congr 1 <;> refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_ <;>
    split_ifs <;> rfl

variable (K : Type*) [Field K]

/-- The linear equivalence $K^{m+n} \cong K^m \times K^n$,
$\vec{x} \mapsto \big((x_0, \dots, x_{m-1}), (x_m, \dots, x_{m+n-1})\big)$. -/
def finAddLinearEquiv (m n : ℕ) : (Fin (m + n) → K) ≃ₗ[K] (Fin m → K) × (Fin n → K) where
  toFun x := (fun a => x (Fin.castAdd n a), fun b => x (Fin.natAdd m b))
  invFun p := Fin.append p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := Fin.append_castAdd_natAdd
  right_inv p := by ext <;> simp

variable {F : Type*} [Field F] [Algebra F K]

/-- **The Mathlib form of $Q$ over an extension field $K$:** the `QuadraticForm K (Fin n → K)`
with values $\vec{x} \mapsto Q(\vec{x})$ for $\vec{x} \in K^n$ (`toQuadraticFormIn_apply`), i.e.
`toQuadraticForm` of the base change of $Q$ to $K$. -/
noncomputable def toQuadraticFormIn (Q : QuadForm F n) : QuadraticForm K (Fin n → K) :=
  (Q.map (algebraMap F K)).toQuadraticForm

theorem toQuadraticFormIn_apply (Q : QuadForm F n) (x : Fin n → K) :
    Q.toQuadraticFormIn K x = Q.evalIn K x := by
  rw [toQuadraticFormIn, toQuadraticForm_apply]
  simp [evalIn, map]

/-- **Isometry over $K$ in Mathlib's terms:** `Q.IsometricIn K Q'` (some $P \in \mathrm{GL}_n(K)$
with $Q(P\vec{x}) = Q'(\vec{x})$) iff the Mathlib forms over $K$ are equivalent. (The direction
of the equivalence is $Q' \to Q$, matching $\vec{x} \mapsto P\vec{x}$.) -/
theorem isometricIn_iff_equivalent (Q Q' : QuadForm F n) :
    Q.IsometricIn K Q' ↔ (Q'.toQuadraticFormIn K).Equivalent (Q.toQuadraticFormIn K) := by
  constructor
  · rintro ⟨P, hP, hPQ⟩
    let hinv := P.invertibleOfIsUnitDet hP
    exact ⟨{ Matrix.toLinearEquiv' P hinv with
      map_app' := fun x => by
        simp only [toQuadraticFormIn_apply]
        exact hPQ x }⟩
  · rintro ⟨e⟩
    refine ⟨LinearMap.toMatrix' e.toLinearEquiv.toLinearMap, ?_, fun x => ?_⟩
    · rw [LinearMap.det_toMatrix']
      exact LinearEquiv.isUnit_det' e.toLinearEquiv
    · rw [LinearMap.toMatrix'_mulVec, ← toQuadraticFormIn_apply, ← toQuadraticFormIn_apply]
      exact e.map_app x

/-- $Q_1 \perp Q_2$ over $K$ is Mathlib's orthogonal sum `prod` of the two forms over $K$. -/
theorem equivalent_toQuadraticFormIn_orthSum (Q₁ : QuadForm F m) (Q₂ : QuadForm F n) :
    ((orthSum Q₁ Q₂).toQuadraticFormIn K).Equivalent
      ((Q₁.toQuadraticFormIn K).prod (Q₂.toQuadraticFormIn K)) :=
  ⟨{ finAddLinearEquiv K m n with
    map_app' := fun x => by
      simp only [QuadraticMap.prod_apply, toQuadraticFormIn_apply, evalIn_orthSum]
      rfl }⟩

/-- **Nondegenerate forms are nonsingular over every extension field:** if
$\det(C + C^{\mathsf T}) \neq 0$ in $F$, the polar form of $Q$ over $K$ is nondegenerate. -/
theorem nondegenerate_polarBilin_toQuadraticFormIn {Q : QuadForm F n} (hQ : Q.Nondegenerate) :
    (polarBilin (Q.toQuadraticFormIn K)).Nondegenerate := by
  rw [QuadraticForm.nondegenerate_polarBilin_iff]
  intro v hv
  have hdet : ((Q.map (algebraMap F K)).hessian).det ≠ 0 := by
    have : (Q.map (algebraMap F K)).hessian = Q.hessian.map (algebraMap F K) := by
      simp [hessian, map, Matrix.transpose_map, Matrix.map_add]
    rw [this, show (Q.hessian.map (algebraMap F K)).det = algebraMap F K Q.hessian.det from
      (RingHom.map_det _ _).symm]
    exact (map_ne_zero_iff _ (algebraMap F K).injective).mpr hQ
  apply Matrix.eq_zero_of_vecMul_eq_zero hdet
  funext j
  have h := hv (Pi.single j 1)
  rw [toQuadraticFormIn, polar, toQuadraticForm_apply, toQuadraticForm_apply,
    toQuadraticForm_apply, polar_eq_hessian K] at h
  simp at h
  exact h

/-- **Witt cancellation for `QuadForm`** (every characteristic; EKM Thm 8.4).

Let $F \subseteq K$ be fields (`Algebra F K`), $Q$ a form in $k$ variables and $Q_1, Q_2$ forms in
$n$ variables over $F$. If $Q$ and $Q_1$ are nondegenerate ($\det(C + C^{\mathsf T}) \neq 0$; this
is nonsingularity of the polar form, in every characteristic) and
$Q \perp Q_1 \cong Q \perp Q_2$ over $K$, then $Q_1 \cong Q_2$ over $K$. -/
@[kb "ekm2008" "Thm 8.4; cassels1978 Ch. 2, Thm. 4.1, Cor. 1–2, pp. 21–22 (Witt cancellation)"]
theorem isometricIn_of_orthSum {Q : QuadForm F k} {Q₁ Q₂ : QuadForm F n} (hQ : Q.Nondegenerate)
    (hQ₁ : Q₁.Nondegenerate) (h : (orthSum Q Q₁).IsometricIn K (orthSum Q Q₂)) :
    Q₁.IsometricIn K Q₂ := by
  rw [isometricIn_iff_equivalent] at h ⊢
  obtain ⟨e₁⟩ := equivalent_toQuadraticFormIn_orthSum K Q Q₁
  obtain ⟨e₂⟩ := equivalent_toQuadraticFormIn_orthSum K Q Q₂
  obtain ⟨g⟩ := h
  have : ((Q.toQuadraticFormIn K).prod (Q₁.toQuadraticFormIn K)).Equivalent
      ((Q.toQuadraticFormIn K).prod (Q₂.toQuadraticFormIn K)) :=
    ⟨e₁.symm.trans (g.symm.trans e₂)⟩
  exact (QuadraticForm.equivalent_of_prod_equivalent_prod_of_nondegenerate
    (nondegenerate_polarBilin_toQuadraticFormIn K hQ)
    (nondegenerate_polarBilin_toQuadraticFormIn K hQ₁) this).symm

end QuadFormsKB.QuadForm

namespace QuadFormsKB.RatQF

open QuadForm

variable {k n : ℕ}

/-- **Witt cancellation over $\mathbb{Q}$**: for nondegenerate rational forms $Q$ ($k$
variables) and $Q_1$, and any $Q_2$ ($n$ variables), $Q \perp Q_1 \cong Q \perp Q_2$ over
$\mathbb{Q}$ implies $Q_1 \cong Q_2$ over $\mathbb{Q}$. -/
@[kb "lam2005" "Ch. I, Thm 4.2"]
theorem isometric_of_orthSum {Q : RatQF k} {Q₁ Q₂ : RatQF n} (hQ : Q.Nondegenerate)
    (hQ₁ : Q₁.Nondegenerate) (h : (orthSum Q Q₁).IsometricIn ℚ (orthSum Q Q₂)) :
    Q₁.IsometricIn ℚ Q₂ :=
  isometricIn_of_orthSum ℚ hQ hQ₁ h

/-- **Witt cancellation over $\mathbb{Q}_p$**: for nondegenerate rational forms $Q$ and
$Q_1$ and any rational $Q_2$, $Q \perp Q_1 \cong Q \perp Q_2$ over $\mathbb{Q}_p$ implies
$Q_1 \cong Q_2$ over $\mathbb{Q}_p$ (every prime $p$, including $p = 2$). -/
@[kb "lam2005" "Ch. I, Thm 4.2"]
theorem isometricIn_padic_of_orthSum (p : ℕ) [Fact p.Prime] {Q : RatQF k} {Q₁ Q₂ : RatQF n}
    (hQ : Q.Nondegenerate) (hQ₁ : Q₁.Nondegenerate)
    (h : (orthSum Q Q₁).IsometricIn ℚ_[p] (orthSum Q Q₂)) : Q₁.IsometricIn ℚ_[p] Q₂ :=
  isometricIn_of_orthSum ℚ_[p] hQ hQ₁ h

end QuadFormsKB.RatQF
