import QuadFormsKB.Literature.OMeara.Sec42Iso
import QuadFormsKB.Witt.Decomposition
import QuadFormsKB.Witt.Extension
import QuadFormsKB.Literature.OMeara.Sec41Extra
import QuadFormsKB.Literature.OMeara.Sec42Extra
import QuadFormsKB.Literature.OMeara.Sec58Bases

/-!
# O'Meara §42D, §42F, §42G: the index, 42:12, and effective orthogonalization

**Setting** (as in `Sec42.lean`, `Sec42Iso.lean`): $F$ a field with $2 \ne 0$ (`[Invertible (2 : F)]`),
$(V, Q)$ a finite-dimensional quadratic space, $B$ = `bil Q` with $B(x,x) = Q(x)$, *regular* =
`(QuadraticMap.associated Q).Nondegenerate`, `gram Q b` the matrix $(B(b_i, b_j))$, the radical of $V$ is
`splitComp Q ⊤ ⊤`. The index is the library's `QuadraticForm.wittIndex` (defined through the Witt
decomposition $Q \cong \mathbb H^m \perp Q_{\mathrm{an}}$).

**Proves** (O'Meara 1973 printing, Chapter IV):
* `finrank_le_wittIndex`, `finrank_eq_wittIndex_of_maximal`, `exists_maximal_totallyIsotropic`
  (**42.r28, 42.r30**, p. 99): every totally isotropic subspace of a regular space has dimension
  $\le \operatorname{ind} V$; every maximal one has dimension exactly $\operatorname{ind} V$ (so the index of the
  book, "the common dimension of all maximal totally isotropic subspaces", equals `wittIndex`), and the index is
  attained;
* `two_mul_wittIndex_le_finrank` (**§42 text, audit row 42.r29**): $0 \le 2\operatorname{ind} V \le \dim V$;
* `two_mul_wittIndex_eq_finrank_iff` (**§42 text, audit row 42.r31**): $2\operatorname{ind}V = \dim V$ iff $V \cong \mathbb H^r$;
* `isotropic_iff_of_dim_four` (**42:12**, p. 95): a regular ternary subspace $U$ of a regular quaternary $V$ with
  $dV = 1$ is isotropic iff $V$ is;
* `scaleRowCol_eq`, `swapRowCol_eq`, `addRowCol_eq` (**§42 text, audit row 42.r32**, pp. 99–100): the three elementary
  transformations are changes of base $M \mapsto T^{\mathsf t} M T$ with $T$ invertible;
* `exists_congruent_diagonal`, `exists_basis_gram_diagonal` (**§42 text, audit row 42.r33**, p. 100): every symmetric matrix
  (the matrix of a space in a base) is congruent to $\mathrm{diag}(\alpha_1, \dots, \alpha_r, 0, \dots, 0)$ with
  $\alpha_i \ne 0$, and the number of zeros is $\dim \operatorname{rad} V$.

**Proof notes.** For the index: with $Q \cong \mathbb H^m \perp Q_{\mathrm{an}}$, $m$ = `wittIndex`, the image
$T_0$ of the span of the first vectors of the $m$ planes is a totally isotropic $m$-dimensional subspace of $V$ that
is *maximal* (a totally isotropic subspace containing $T_0$ lies in $T_0$, since $Q_{\mathrm{an}}$ is anisotropic).
By Witt's theorem (`QuadraticForm.exists_isometryEquiv_extend_of_nondegenerate`) any totally isotropic subspace of
dimension $\ge m$ is carried over a copy of $T_0$ and any smaller one into $T_0$, which gives both bounds. This
replaces the book's route through 42:13 (the book defines the index through 42:13 and the splitting of hyperbolic
planes). 42:12 is proved directly instead of through 42:11 (see the docstring). The matrix diagonalization is
`LinearMap.BilinForm.exists_orthogonal_basis` followed by a reordering of the base so that the zeros come last.

**Conventions.** Indices are 0-based (the book's $\alpha_1, \dots, \alpha_r$ are `α 0 … α (r-1)`, nonzero exactly
for `i.val < r`). In 42:12, "$dV = 1$" is "some base of $V$ has a square discriminant" (the discriminant of a
regular space is nonzero), O'Meara's meaning of $dV = 1$ in $F/F^{\times 2}$ (p. 87). The elementary
transformations are stated for arbitrary symmetric or non-symmetric matrices (the identity $T^{\mathsf t} M T$
needs no symmetry); the book's "series of elementary transformations" is replaced by existence of an invertible
$T$ (a base change), not an explicit algorithm.
-/

open QuadraticMap Submodule Module LinearMap
open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Sec42Index

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)

/-- A subspace $M$ of $V$ is **totally isotropic** if $Q(M) = 0$ (O'Meara 1963, §42D, p. 94). -/
@[kb "omeara1963" "§42D, p. 94 (totally isotropic subspace)"]
def IsTotallyIsotropic (M : Submodule F V) : Prop := ∀ x ∈ M, Q x = 0

/-- A **maximal totally isotropic subspace**: totally isotropic and contained in no strictly larger totally
isotropic subspace (O'Meara §42F, p. 99). -/
@[kb "omeara1963" "§42F, p. 99 (maximal totally isotropic subspace)"]
def IsMaximalTotallyIsotropic (M : Submodule F V) : Prop :=
  IsTotallyIsotropic Q M ∧ ∀ N : Submodule F V, IsTotallyIsotropic Q N → M ≤ N → N = M

/-- **O'Meara §42 (running text, audit row 42.r17)** (p. 94). $Q(M) = 0$ iff $B(M, M) = 0$. -/
theorem isTotallyIsotropic_iff_bil [FiniteDimensional F V] (M : Submodule F V) :
    IsTotallyIsotropic Q M ↔ ∀ x ∈ M, ∀ y ∈ M, bil Q x y = 0 :=
  totallyIsotropic_iff Q M

theorem exists_injective_of_finrank_le {X Y : Type*} [AddCommGroup X] [Module F X] [AddCommGroup Y]
    [Module F Y] [FiniteDimensional F X] [FiniteDimensional F Y] (h : finrank F X ≤ finrank F Y) :
    ∃ f : X →ₗ[F] Y, Function.Injective f := by
  let bX := Module.finBasis F X
  let bY := Module.finBasis F Y
  exact ⟨bX.constr F (fun i => bY (Fin.castLE h i)),
    bX.injective_constr_of_linearIndependent
      (bY.linearIndependent.comp _ (Fin.castLE_injective h))⟩

section Witt

variable [FiniteDimensional F V]

/-- The embedding of $F^m$ as the span of the first vectors of the $m$ hyperbolic planes. -/
def hypIso (m : ℕ) {U : Type*} [AddCommGroup U] [Module F U] :
    (Fin m → F) →ₗ[F] ((Fin m → F × F) × U) where
  toFun a := (fun i => (a i, 0), 0)
  map_add' a b := by ext <;> simp
  map_smul' c a := by ext <;> simp

theorem hypIso_injective (m : ℕ) {U : Type*} [AddCommGroup U] [Module F U] :
    Function.Injective (hypIso (F := F) (U := U) m) := by
  intro a b h
  funext i
  have := congrArg (fun x => (x.1 i).1) h
  simpa [hypIso] using this

theorem Q_hypIso (m : ℕ) {U : Type*} [AddCommGroup U] [Module F U] (Qa : QuadraticForm F U)
    (a : Fin m → F) : ((QuadraticForm.hyperbolicSpace F m).prod Qa) (hypIso m a) = 0 := by
  simp [hypIso, QuadraticForm.hyperbolicSpace_apply]

/-- **Key lemma.** In $\mathbb H^m \perp Q_{an}$, a totally isotropic subspace containing the standard
$m$-dimensional totally isotropic subspace is equal to it. Stated through an isometry $e$. -/
theorem le_range_of_isTotallyIsotropic {m : ℕ} {U : Type*} [AddCommGroup U] [Module F U]
    {Qa : QuadraticForm F U} (ha : Qa.Anisotropic)
    (e : Q.IsometryEquiv ((QuadraticForm.hyperbolicSpace F m).prod Qa)) {N : Submodule F V}
    (hN : IsTotallyIsotropic Q N)
    (hle : ∀ a : Fin m → F, e.symm (hypIso m a) ∈ N) :
    ∀ v ∈ N, ∃ a : Fin m → F, e.symm (hypIso m a) = v := by
  classical
  intro v hv
  obtain ⟨⟨h, u⟩, hx⟩ : ∃ x, x = e v := ⟨_, rfl⟩
  have hQv : ((QuadraticForm.hyperbolicSpace F m).prod Qa) (h, u) = 0 := by
    rw [hx, e.map_app]; exact hN v hv
  have hi : ∀ i, (h i).2 = 0 := by
    intro i
    have hmem := N.add_mem hv (hle (Pi.single i 1))
    have h0 := hN _ hmem
    rw [← e.map_app, map_add, e.apply_symm_apply, ← hx] at h0
    simp [hypIso, QuadraticForm.hyperbolicSpace_apply, Pi.single_apply, add_mul,
      Finset.sum_add_distrib] at h0 hQv
    linear_combination h0 - hQv
  have hu : u = 0 := by
    apply ha
    simp [QuadraticForm.hyperbolicSpace_apply, hi] at hQv
    exact hQv
  refine ⟨fun i => (h i).1, ?_⟩
  apply e.injective
  show e (e.symm _) = e v
  rw [e.apply_symm_apply, ← hx]
  ext i
  · simp [hypIso]
  · simp [hypIso, hi]
  · simp [hypIso, hu]

variable {Q}

/-- A regular space has zero quadratic radical. -/
theorem radical_eq_bot_of_regular (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    Q.radical = ⊥ :=
  (QuadraticMap.nondegenerate_associated_iff.mp hQ).radical_eq_bot

/-- A regular space has a nondegenerate polar form. -/
theorem polarBilin_nondegenerate_of_regular (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    (QuadraticMap.polarBilin Q).Nondegenerate :=
  QuadraticMap.nondegenerate_polar_iff.mpr (QuadraticMap.nondegenerate_associated_iff.mp hQ)

/-- **The standard maximal totally isotropic subspace.** For regular $V$ (of index $m$ = `wittIndex Q`)
there is an injective linear map $j : F^m \to V$ whose image is totally isotropic and maximal (it is
the span of the first vectors of the $m$ hyperbolic planes of a Witt decomposition). -/
theorem exists_standard_totallyIsotropic (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    ∃ j : (Fin (QuadraticForm.wittIndex Q) → F) →ₗ[F] V, Function.Injective j ∧
      IsTotallyIsotropic Q (LinearMap.range j) ∧
      ∀ N : Submodule F V, IsTotallyIsotropic Q N → LinearMap.range j ≤ N → N = LinearMap.range j := by
  obtain ⟨U, _, _, _, Qa, ha, ⟨e⟩⟩ := QuadraticForm.wittIndex_spec Q (radical_eq_bot_of_regular hQ)
  let j : (Fin (QuadraticForm.wittIndex Q) → F) →ₗ[F] V :=
    (e.symm.toLinearEquiv : _ ≃ₗ[F] V).toLinearMap ∘ₗ hypIso _
  have hj : ∀ a, j a = e.symm (hypIso _ a) := fun a => rfl
  refine ⟨j, ?_, ?_, ?_⟩
  · intro a b h
    exact hypIso_injective _ (e.symm.injective h)
  · rintro _ ⟨a, rfl⟩
    rw [hj, e.symm.map_app]; exact Q_hypIso _ Qa a
  · intro N hN hle
    apply le_antisymm _ hle
    intro v hv
    obtain ⟨a, ha'⟩ := le_range_of_isTotallyIsotropic Q ha e hN
      (fun a => hle ⟨a, by rw [hj]⟩) v hv
    exact ⟨a, by rw [hj, ha']⟩

/-- **O'Meara §42 (running text, audit row 42.r28) / 42.r30 (a)** (p. 99). Every totally isotropic subspace $M$ of a regular space
has $\dim M \le \operatorname{ind} V$ (`QuadraticForm.wittIndex`). -/
@[kb "omeara1963" "§42F, p. 99 (index; dimension of totally isotropic subspaces)"]
theorem finrank_le_wittIndex (hQ : (QuadraticMap.associated Q).Nondegenerate) {M : Submodule F V}
    (hM : IsTotallyIsotropic Q M) : finrank F M ≤ QuadraticForm.wittIndex Q := by
  obtain ⟨j, hj, hjt, hjmax⟩ := exists_standard_totallyIsotropic hQ
  by_contra hlt
  push Not at hlt
  have hle : finrank F (Fin (QuadraticForm.wittIndex Q) → F) ≤ finrank F M := by
    simp; omega
  obtain ⟨σ0, hσ0⟩ := exists_injective_of_finrank_le hle
  let ej := LinearEquiv.ofInjective j hj
  let σ : LinearMap.range j →ₗ[F] V := M.subtype ∘ₗ σ0 ∘ₗ ej.symm.toLinearMap
  have hσi : Function.Injective σ :=
    M.injective_subtype.comp (hσ0.comp ej.symm.injective)
  have hσQ : ∀ w, Q (σ w) = Q w := fun w => by
    show Q ((σ0 (ej.symm w) : M) : V) = Q w
    rw [hM _ (σ0 (ej.symm w)).2, hjt _ w.2]
  obtain ⟨ρ, hρ⟩ := QuadraticForm.exists_isometryEquiv_extend_of_nondegenerate Q
    (polarBilin_nondegenerate_of_regular hQ) σ hσi hσQ
  let N : Submodule F V := M.map (ρ.symm.toLinearEquiv : V ≃ₗ[F] V).toLinearMap
  have hN : IsTotallyIsotropic Q N := by
    rintro _ ⟨y, hy, rfl⟩
    show Q (ρ.symm y) = 0
    rw [ρ.symm.map_app]; exact hM y hy
  have hjN : LinearMap.range j ≤ N := by
    intro w hw
    refine ⟨σ ⟨w, hw⟩, (σ0 _).2, ?_⟩
    show ρ.symm (σ ⟨w, hw⟩) = w
    rw [← hρ ⟨w, hw⟩]
    exact ρ.symm_apply_apply w
  have h1 := hjmax N hN hjN
  have h2 : finrank F N = finrank F M :=
    LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (ρ.symm.toLinearEquiv).injective M).symm
  have h3 : finrank F (LinearMap.range j) = QuadraticForm.wittIndex Q := by
    rw [LinearMap.finrank_range_of_inj hj]; simp
  rw [h1, h3] at h2
  omega

/-- **O'Meara §42 (running text, audit row 42.r28) / 42.r30 (b)** (p. 99). Every maximal totally isotropic subspace of a regular
space has dimension $\operatorname{ind} V$ = `QuadraticForm.wittIndex`. In particular all maximal
totally isotropic subspaces have the same dimension. -/
@[kb "omeara1963" "§42F, p. 99 (r = ind V; maximal totally isotropic subspaces)"]
theorem finrank_eq_wittIndex_of_maximal (hQ : (QuadraticMap.associated Q).Nondegenerate)
    {M : Submodule F V} (hM : IsMaximalTotallyIsotropic Q M) :
    finrank F M = QuadraticForm.wittIndex Q := by
  obtain ⟨j, hj, hjt, hjmax⟩ := exists_standard_totallyIsotropic hQ
  refine le_antisymm (finrank_le_wittIndex hQ hM.1) ?_
  by_contra hlt
  push Not at hlt
  have hle : finrank F M ≤ finrank F (Fin (QuadraticForm.wittIndex Q) → F) := by
    simp; omega
  obtain ⟨σ0, hσ0⟩ := exists_injective_of_finrank_le hle
  let σ : M →ₗ[F] V := j ∘ₗ σ0
  have hσi : Function.Injective σ := hj.comp hσ0
  have hσQ : ∀ w, Q (σ w) = Q w := fun w => by
    rw [hM.1 _ w.2]; exact hjt _ ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ := QuadraticForm.exists_isometryEquiv_extend_of_nondegenerate Q
    (polarBilin_nondegenerate_of_regular hQ) σ hσi hσQ
  let N : Submodule F V := (LinearMap.range j).map (ρ.symm.toLinearEquiv : V ≃ₗ[F] V).toLinearMap
  have hN : IsTotallyIsotropic Q N := by
    rintro _ ⟨y, hy, rfl⟩
    show Q (ρ.symm y) = 0
    rw [ρ.symm.map_app]; exact hjt y hy
  have hMN : M ≤ N := by
    intro x hx
    refine ⟨σ ⟨x, hx⟩, ⟨_, rfl⟩, ?_⟩
    show ρ.symm (σ ⟨x, hx⟩) = x
    rw [← hρ ⟨x, hx⟩]
    exact ρ.symm_apply_apply x
  have h1 := hM.2 N hN hMN
  have h2 : finrank F N = finrank F (LinearMap.range j) :=
    LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (ρ.symm.toLinearEquiv).injective _).symm
  have h3 : finrank F (LinearMap.range j) = QuadraticForm.wittIndex Q := by
    rw [LinearMap.finrank_range_of_inj hj]; simp
  rw [h1, h3] at h2
  omega

/-- **O'Meara §42 (running text, audit row 42.r28)** (p. 99). A regular space has a maximal totally isotropic subspace of dimension
$\operatorname{ind} V$ (so the index is attained). -/
@[kb "omeara1963" "§42F, p. 99 (the index is attained)"]
theorem exists_maximal_totallyIsotropic (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    ∃ M : Submodule F V, IsMaximalTotallyIsotropic Q M ∧ finrank F M = QuadraticForm.wittIndex Q := by
  obtain ⟨j, hj, hjt, hjmax⟩ := exists_standard_totallyIsotropic hQ
  refine ⟨LinearMap.range j, ⟨hjt, hjmax⟩, ?_⟩
  rw [LinearMap.finrank_range_of_inj hj]; simp

/-- **O'Meara §42 (running text, audit row 42.r29)** (p. 99), the missing inequality: $0 \le 2\operatorname{ind} V \le \dim V$
(the lower bound $0 \le 2\operatorname{ind}V$ is trivial in $\mathbb N$). -/
@[kb "omeara1963" "§42F, p. 99 (0 ≤ 2r ≤ dim V)"]
theorem two_mul_wittIndex_le_finrank (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    2 * QuadraticForm.wittIndex Q ≤ finrank F V := by
  obtain ⟨U, _, _, _, Qa, ha, ⟨e⟩⟩ := QuadraticForm.wittIndex_spec Q (radical_eq_bot_of_regular hQ)
  rw [LinearEquiv.finrank_eq e.toLinearEquiv, Module.finrank_prod]
  simp [Module.finrank_pi_fintype]
  omega

/-- **O'Meara §42 (running text, audit row 42.r31)** (p. 99). A regular space is *hyperbolic* ($2\operatorname{ind}V = \dim V$, i.e.
$V = H_1 \perp \dots \perp H_r$) if and only if it is isometric to the standard hyperbolic space
$\mathbb H^r$ (`QuadraticForm.hyperbolicSpace`) for some $r$. -/
@[kb "omeara1963" "§42F, p. 99 (hyperbolic space)"]
theorem two_mul_wittIndex_eq_finrank_iff (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    2 * QuadraticForm.wittIndex Q = finrank F V ↔
      ∃ r, Q.Equivalent (QuadraticForm.hyperbolicSpace F r) := by
  constructor
  · intro h
    obtain ⟨U, _, _, _, Qa, ha, ⟨e⟩⟩ :=
      QuadraticForm.wittIndex_spec Q (radical_eq_bot_of_regular hQ)
    have hfr := LinearEquiv.finrank_eq e.toLinearEquiv
    rw [Module.finrank_prod] at hfr
    simp [Module.finrank_pi_fintype] at hfr
    have hU : finrank F U = 0 := by omega
    have : Subsingleton U := Module.finrank_zero_iff.mp hU
    have : Unique U := uniqueOfSubsingleton 0
    refine ⟨QuadraticForm.wittIndex Q, ⟨e.trans
      { toLinearEquiv := LinearEquiv.prodUnique
        map_app' := fun x => ?_ }⟩⟩
    have : x.2 = 0 := Subsingleton.elim _ _
    simp [this]
  · rintro ⟨r, ⟨e⟩⟩
    have hrad : Q.radical = ⊥ := radical_eq_bot_of_regular hQ
    let Qa : QuadraticForm F PUnit := 0
    have ha : Qa.Anisotropic := fun x _ => Subsingleton.elim _ _
    have e2 : Q.Equivalent ((QuadraticForm.hyperbolicSpace F r).prod Qa) :=
      ⟨e.trans
        { toLinearEquiv := LinearEquiv.prodUnique.symm
          map_app' := fun x => by simp [Qa] }⟩
    have hr := QuadraticForm.eq_wittIndex Q hrad ha e2
    rw [LinearEquiv.finrank_eq e.toLinearEquiv, ← hr]
    simp [Module.finrank_pi_fintype]
    ring

end Witt

/-! ### §42G: elementary transformations and diagonalization -/

section Elementary

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Elementary transformation (a)** (O'Meara §42G, pp. 99–100): multiply column $i$ and row $i$ of $M$ by
$\alpha$ (the entry $(i,i)$ is multiplied by $\alpha^2$). -/
def scaleRowCol (i : n) (α : F) (M : Matrix n n F) : Matrix n n F :=
  Matrix.of fun r c => (if r = i then α else 1) * M r c * (if c = i then α else 1)

/-- **Elementary transformation (b)**: interchange columns $i, j$ and rows $i, j$ of $M$. -/
def swapRowCol (i j : n) (M : Matrix n n F) : Matrix n n F :=
  Matrix.of fun r c => M (Equiv.swap i j r) (Equiv.swap i j c)

/-- **Elementary transformation (c)**: add $\alpha\times$ column $i$ to column $j$ of $M$, and then
$\alpha\times$ row $i$ to row $j$ (of the result). -/
def addRowCol (i j : n) (α : F) (M : Matrix n n F) : Matrix n n F :=
  let M₁ := M.updateCol j fun r => M r j + α * M r i
  M₁.updateRow j fun c => M₁ j c + α * M₁ i c

/-- The matrix of the base change for (a): $\mathrm{diag}(1, \dots, \alpha, \dots, 1)$. -/
def scaleMat (i : n) (α : F) : Matrix n n F := Matrix.diagonal fun k => if k = i then α else 1

/-- **O'Meara §42 (running text, audit row 42.r32) (a)** (pp. 99–100). Scaling row and column $i$ by $\alpha \ne 0$ is the change of
base $M \mapsto T^{\mathsf t} M T$ with $T = \mathrm{diag}(1, .., \alpha, .., 1)$ invertible. -/
@[kb "omeara1963" "§42G, pp. 99-100 (elementary transformation (a))"]
theorem scaleRowCol_eq (i : n) {α : F} (hα : α ≠ 0) (M : Matrix n n F) :
    IsUnit (scaleMat i α).det ∧ scaleRowCol i α M = (scaleMat i α)ᵀ * M * scaleMat i α := by
  refine ⟨?_, ?_⟩
  · simp only [scaleMat, Matrix.det_diagonal]
    refine isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => ?_)
    split_ifs <;> simp [hα]
  · ext r c
    simp [scaleRowCol, scaleMat, Matrix.diagonal_transpose, Matrix.diagonal_mul,
      Matrix.mul_diagonal, mul_assoc]

/-- **O'Meara §42 (running text, audit row 42.r32) (b)** (pp. 99–100). Interchanging columns and rows $i, j$ is the change of base
$M \mapsto T^{\mathsf t} M T$ with $T$ the (invertible) permutation matrix of the transposition. -/
@[kb "omeara1963" "§42G, pp. 99-100 (elementary transformation (b))"]
theorem swapRowCol_eq (i j : n) (M : Matrix n n F) :
    IsUnit ((Equiv.swap i j).permMatrix F).det ∧
      swapRowCol i j M = ((Equiv.swap i j).permMatrix F)ᵀ * M * (Equiv.swap i j).permMatrix F := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap i j)) with h | h <;> rw [h] <;> simp
  · ext r c
    simp [swapRowCol, Matrix.mul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.swap_apply_eq_iff]
    rw [Finset.sum_eq_single (Equiv.swap i j r)]
    · simp
    · intro b _ hb
      rw [ite_eq_right_iff]
      intro h; exact absurd (by rw [h]; simp) hb
    · simp

/-- **O'Meara §42 (running text, audit row 42.r32) (c)** (pp. 99–100). Adding $\alpha\times$ column $i$ to column $j$ and then the same
on the rows ($i \ne j$) is the change of base $M \mapsto T^{\mathsf t} M T$ with $T$ the transvection
$1 + \alpha E_{ij}$ (invertible, of determinant $1$). -/
@[kb "omeara1963" "§42G, pp. 99-100 (elementary transformation (c))"]
theorem addRowCol_eq {i j : n} (hij : i ≠ j) (α : F) (M : Matrix n n F) :
    IsUnit (Matrix.transvection i j α).det ∧
      addRowCol i j α M = (Matrix.transvection i j α)ᵀ * M * Matrix.transvection i j α := by
  refine ⟨by rw [Matrix.det_transvection_of_ne i j hij]; exact isUnit_one, ?_⟩
  have hT : (Matrix.transvection i j α)ᵀ = Matrix.transvection j i α := by
    simp [Matrix.transvection, Matrix.transpose_add, Matrix.transpose_single]
  have h1 : M.updateCol j (fun r => M r j + α * M r i) = M * Matrix.transvection i j α := by
    ext r c
    by_cases hc : c = j
    · subst hc; simp
    · simp [hc]
  have h2 : ∀ N : Matrix n n F,
      N.updateRow j (fun c => N j c + α * N i c) = Matrix.transvection j i α * N := by
    intro N
    ext r c
    by_cases hr : r = j
    · subst hr; simp
    · simp [hr]
  simp only [addRowCol]
  rw [h1, h2, hT, Matrix.mul_assoc]

end Elementary

section Diagonalization

/-- A subset of `Fin m` closed downwards is an initial segment: $i \in S \iff i < |S|$. -/
theorem mem_iff_lt_card_of_downset {m : ℕ} (S : Finset (Fin m))
    (hS : ∀ i j : Fin m, i ≤ j → j ∈ S → i ∈ S) (i : Fin m) : i ∈ S ↔ i.val < S.card := by
  constructor
  · intro hi
    have h : Finset.Iic i ⊆ S := fun k hk => hS k i (Finset.mem_Iic.1 hk) hi
    have := Finset.card_le_card h
    simp at this; omega
  · intro hlt
    by_contra hi
    have h : S ⊆ Finset.Iio i := fun k hk =>
      Finset.mem_Iio.2 (lt_of_not_ge fun h => hi (hS i k h hk))
    have := Finset.card_le_card h
    simp at this; omega

/-- **O'Meara §42 (running text, audit row 42.r33)** (p. 100), matrix form. Every symmetric matrix $M$ over $F$ ($2 \ne 0$) is congruent,
$T^{\mathsf t} M T = \mathrm{diag}(\alpha_1, \dots, \alpha_r, 0, \dots, 0)$ with $T$ invertible and
$\alpha_i \ne 0$ exactly for the first $r = \operatorname{rank} M$ entries; the number of zeros is
$m - r = \dim \ker M$, the dimension of the radical of the form $(x, y) \mapsto x^{\mathsf t} M y$. -/
@[kb "omeara1963" "§42G, p. 100 (diagonalization of a symmetric matrix)"]
theorem exists_congruent_diagonal {m : ℕ} (M : Matrix (Fin m) (Fin m) F) (hM : Mᵀ = M) :
    ∃ (T : Matrix (Fin m) (Fin m) F) (α : Fin m → F), IsUnit T.det ∧
      Tᵀ * M * T = Matrix.diagonal α ∧ (∀ i : Fin m, α i ≠ 0 ↔ i.val < M.rank) ∧
      finrank F (LinearMap.ker (Matrix.toLin' M)) = m - M.rank := by
  classical
  have hsymm : (Matrix.toBilin' M).IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.2 hM
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.mp hsymm)
  let e : Fin (finrank F (Fin m → F)) ≃ Fin m := finCongr (Module.finrank_fin_fun F)
  let v1 : Basis (Fin m) F (Fin m → F) := v.reindex e
  have hv1 : ∀ i j, i ≠ j → Matrix.toBilin' M (v1 i) (v1 j) = 0 := fun i j hij => by
    have := hv (i := e.symm i) (j := e.symm j) (fun h => hij (e.symm.injective h))
    simpa [v1] using this
  let g : Fin m → F := fun k => Matrix.toBilin' M (v1 k) (v1 k)
  let f : Fin m → ℕ := fun k => if g k = 0 then 1 else 0
  let σ : Equiv.Perm (Fin m) := Tuple.sort f
  let v2 : Basis (Fin m) F (Fin m → F) := v1.reindex σ.symm
  have hv2 : ∀ i, v2 i = v1 (σ i) := fun i => by simp [v2]
  let T : Matrix (Fin m) (Fin m) F := Matrix.of fun i j => v2 j i
  let α : Fin m → F := fun i => g (σ i)
  have key : ∀ i j, (Tᵀ * M * T) i j = Matrix.toBilin' M (v2 i) (v2 j) := by
    intro i j
    rw [Matrix.toBilin'_apply']
    simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply, T,
      Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hdiag : Tᵀ * M * T = Matrix.diagonal α := by
    ext i j
    rw [key]
    by_cases hij : i = j
    · subst hij; simp [α, g, hv2]
    · rw [Matrix.diagonal_apply_ne _ hij, hv2, hv2]
      exact hv1 _ _ (fun h => hij (σ.injective h))
  have hTdet : IsUnit T.det := by
    have := (Pi.basisFun F (Fin m)).isUnit_det v2
    rw [Basis.det_apply] at this
    convert this using 2
    ext i j
    simp [T, Basis.toMatrix_apply]
  have hrank : M.rank = Fintype.card {i // α i ≠ 0} := by
    rw [← Matrix.rank_diagonal, ← hdiag, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hTdet,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by rwa [Matrix.det_transpose])]
  refine ⟨T, α, hTdet, hdiag, ?_, ?_⟩
  · set S : Finset (Fin m) := Finset.univ.filter fun i => α i ≠ 0 with hSdef
    have hcard : S.card = M.rank := by
      rw [hrank, hSdef, Fintype.card_subtype]
    have hd : ∀ i j : Fin m, i ≤ j → j ∈ S → i ∈ S := by
      intro i j hij hj
      have hmono : f (σ i) ≤ f (σ j) := Tuple.monotone_sort f hij
      simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and, α] at hj ⊢
      by_contra hi
      simp only [f] at hmono
      simp [hi, hj] at hmono
    intro i
    have := mem_iff_lt_card_of_downset S hd i
    rw [hcard] at this
    simpa [hSdef] using this
  · have h := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M)
    rw [Module.finrank_fin_fun] at h
    have : M.rank = finrank F (LinearMap.range (Matrix.toLin' M)) := rfl
    omega

end Diagonalization

section GramSpace

variable [FiniteDimensional F V] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The base $b'_j = \sum_i t_{ij} b_i$ obtained from a base $b$ and an invertible matrix $T$. -/
def basisOfUnitDet (b : Basis ι F V) (T : Matrix ι ι F) (hT : IsUnit T.det) : Basis ι F V :=
  b.map (LinearEquiv.ofIsUnitDet (f := Matrix.toLin b b T) (v := b) (v' := b)
    (by rw [LinearMap.toMatrix_toLin]; exact hT))

theorem basisOfUnitDet_apply (b : Basis ι F V) (T : Matrix ι ι F) (hT : IsUnit T.det) (j : ι) :
    basisOfUnitDet b T hT j = ∑ i, T i j • b i := by
  simp [basisOfUnitDet, Matrix.toLin_self]

theorem bil_expand (b : Basis ι F V) (x z : V) :
    bil Q x z = ∑ i, ∑ j, b.repr x i * gram Q b i j * b.repr z j := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr z]
  simp only [bil_sum_left, bil_sum_right, bil_smul_left, bil_smul_right, gram, Matrix.of_apply]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mem_rad_iff_gram (b : Basis ι F V) (x : V) :
    x ∈ splitComp (R := F) Q ⊤ ⊤ ↔ gram Q b *ᵥ (b.equivFun x) = 0 := by
  have hs : ∀ i j, gram Q b i j = gram Q b j i := fun i j => bil_comm Q _ _
  constructor
  · intro hx
    funext j
    have h0 := hx.2 (b j) Submodule.mem_top
    rw [bil_expand Q b] at h0
    simp only [Basis.repr_self, Finsupp.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h0
    simp only [Matrix.mulVec, dotProduct, Basis.equivFun_apply, Pi.zero_apply]
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs j i]; ring
  · intro hx
    refine ⟨Submodule.mem_top, fun z _ => ?_⟩
    rw [bil_expand Q b, Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h0 := congrFun hx j
    simp only [Matrix.mulVec, dotProduct, Basis.equivFun_apply, Pi.zero_apply] at h0
    calc ∑ i, b.repr x i * gram Q b i j * b.repr z j
        = (∑ i, gram Q b j i * b.repr x i) * b.repr z j := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hs j i]; ring
      _ = 0 := by rw [h0, zero_mul]

/-- The radical $\operatorname{rad} V$ corresponds, under the coordinate isomorphism of a base $b$, to the
kernel of the matrix $M$ of $V$ in $b$: $\dim \operatorname{rad} V = \dim \ker M$. -/
theorem finrank_rad_eq_finrank_ker_gram (b : Basis ι F V) :
    finrank F (splitComp (R := F) Q ⊤ ⊤) = finrank F (LinearMap.ker (Matrix.toLin' (gram Q b))) := by
  have h : splitComp (R := F) Q ⊤ ⊤ =
      (LinearMap.ker (Matrix.toLin' (gram Q b))).comap b.equivFun.toLinearMap := by
    ext x
    rw [mem_rad_iff_gram Q b]
    simp
  rw [h, Submodule.comap_equiv_eq_map_symm]
  exact LinearEquiv.finrank_map_eq _ _

/-- **O'Meara §42 (running text, audit row 42.r33)** (p. 100), for a space. If $V$ has $n$ vectors in a base $b$ with matrix $M$, there
is a base $b'$ in which the matrix of $V$ is $\mathrm{diag}(\alpha_1, \dots, \alpha_r, 0, \dots, 0)$ with
$\alpha_i \ne 0$ for $i < r = \operatorname{rank} M$ (0-based), and the number $n - r$ of zeros equals
$\dim \operatorname{rad} V$. (The base $b'$ is $b \cdot T$ for the invertible $T$ of
`exists_congruent_diagonal`.) -/
@[kb "omeara1963" "§42G, p. 100 (diagonal matrix of a space; zeros = dim rad V)"]
theorem exists_basis_gram_diagonal {n : ℕ} (b : Basis (Fin n) F V) :
    ∃ (b' : Basis (Fin n) F V) (α : Fin n → F), gram Q b' = Matrix.diagonal α ∧
      (∀ i : Fin n, α i ≠ 0 ↔ i.val < (gram Q b).rank) ∧
      finrank F (splitComp (R := F) Q ⊤ ⊤) = n - (gram Q b).rank := by
  have hsym : (gram Q b)ᵀ = gram Q b := by
    ext i j; exact bil_comm Q _ _
  obtain ⟨T, α, hT, hd, hα, hk⟩ := exists_congruent_diagonal (gram Q b) hsym
  refine ⟨basisOfUnitDet b T hT, α, ?_, hα, ?_⟩
  · rw [gram_change_of_base Q b _ T (basisOfUnitDet_apply b T hT)]
    exact hd
  · rw [finrank_rad_eq_finrank_ker_gram Q b]; exact hk

/-- The discriminants of two bases differ by the square of the nonzero determinant of the transition
matrix: $d(b') = (\det T)^2\, d(b)$ (O'Meara §41B, p. 87; cf. `det_gram_basis_change` in `Sec41Extra.lean`). -/
theorem det_gram_basis_change' (b b' : Basis ι F V) :
    (gram Q b').det = (b.toMatrix b').det ^ 2 * (gram Q b).det := by
  rw [gram_change_of_base Q b b' (b.toMatrix b') (fun j => by
    simp [Basis.toMatrix_apply, Basis.sum_repr]), Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

theorem det_toMatrix_ne_zero (b b' : Basis ι F V) : (b.toMatrix b').det ≠ 0 := by
  have := (b.isUnit_det b').ne_zero
  rwa [Basis.det_apply] at this

/-- A regular space has nonzero discriminant in every base. -/
theorem det_gram_ne_zero_of_regular (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (b : Basis ι F V) : (gram Q b).det ≠ 0 := by
  have : gram Q b = LinearMap.BilinForm.toMatrix b (QuadraticMap.associated Q) := by
    ext i j; simp [gram, LinearMap.BilinForm.toMatrix_apply]
  rw [this]
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hQ

/-- Discriminant of the block configuration $\langle -a\rangle \perp P \perp \langle a\rangle$ used in 42:12:
$d(u, p, q, w) = -a^2 (B(p,p)B(q,q) - B(p,q)^2)$. -/
theorem det_gram_four (u p q w : V) {a : F} (h1 : bil Q u u = -a) (h2 : bil Q u p = 0)
    (h3 : bil Q u q = 0) (h4 : bil Q u w = 0) (h5 : bil Q p w = 0) (h6 : bil Q q w = 0)
    (h7 : bil Q w w = a) :
    (gram Q ![u, p, q, w]).det =
      (-a) * (bil Q p p * bil Q q q - bil Q p q * bil Q p q) * a := by
  have c2 : bil Q p u = 0 := by rw [bil_comm]; exact h2
  have c3 : bil Q q u = 0 := by rw [bil_comm]; exact h3
  have c4 : bil Q w u = 0 := by rw [bil_comm]; exact h4
  have c5 : bil Q w p = 0 := by rw [bil_comm]; exact h5
  have c6 : bil Q w q = 0 := by rw [bil_comm]; exact h6
  have c7 : bil Q q p = bil Q p q := bil_comm Q _ _
  have hg : gram Q ![u, p, q, w] =
      !![-a, 0, 0, 0; 0, bil Q p p, bil Q p q, 0; 0, bil Q p q, bil Q q q, 0; 0, 0, 0, a] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gram, h1, h2, h3, h4, h5, h6, h7, c2, c3, c4, c5, c6, c7]
  rw [hg]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  ring

set_option maxHeartbeats 1000000 in
/-- **O'Meara 42:12** (p. 95). Let $U$ be a regular ternary subspace of a regular quaternary space $V$
with $dV = 1$ (some, equivalently every, base of $V$ has a square discriminant). Then $V$ is isotropic
if and only if $U$ is isotropic.

Deviation from the book's proof: the direction "$V$ isotropic $\Rightarrow$ $U$ isotropic" is proved
directly (writing $V = U \perp \langle a \rangle$, the isotropic vector gives $-a \in Q(U)$, as 42:11
would; then $U = P \perp \langle -a \rangle$ with $dP = -1$, so $P$ is a hyperbolic plane by 42:9
(`isHyperbolicPlane_tfae`)). -/
@[kb "omeara1963" "§42D, 42:12, p. 95"]
theorem isotropic_iff_of_dim_four (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (h4 : finrank F V = 4) (hd : ∃ b : Basis (Fin 4) F V, IsSquare (gram Q b).det)
    (U : Submodule F V) (hU3 : finrank F U = 3) (hUreg : splitComp (R := F) Q U U = ⊥) :
    (∃ v : V, v ≠ 0 ∧ Q v = 0) ↔ ∃ u ∈ U, u ≠ 0 ∧ Q u = 0 := by
  constructor
  swap
  · rintro ⟨u, -, hu0, hu⟩; exact ⟨u, hu0, hu⟩
  rintro ⟨v, hv0, hv⟩
  -- Step A: V = U ⊥ F w₀
  have hrefl : (QuadraticMap.associated Q).IsRefl := fun x y h => by
    rw [show (QuadraticMap.associated Q) y x = bil Q y x from rfl, bil_comm]; exact h
  have hUnd : (LinearMap.BilinForm.restrict (QuadraticMap.associated Q) U).Nondegenerate := by
    have key : ∀ x : U, (∀ y : U, bil Q (x : V) y = 0) → x = 0 := fun x hx => by
      have : (x : V) ∈ splitComp (R := F) Q U U := ⟨x.2, fun z hz => hx ⟨z, hz⟩⟩
      rw [hUreg] at this
      exact Subtype.ext ((Submodule.mem_bot F).1 this)
    refine ⟨fun x hx => key x fun y => ?_, fun y hy => key y fun x => ?_⟩
    · exact hx y
    · rw [bil_comm]; exact hy x
  have hc := LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl hUnd
  set W := LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) U with hW
  have hWmem : ∀ x, x ∈ W ↔ ∀ u ∈ U, bil Q u x = 0 := fun x => by
    rw [hW, LinearMap.BilinForm.mem_orthogonal_iff]
  have hWrank : finrank F W = 1 := by
    have := Submodule.finrank_add_eq_of_isCompl hc
    omega
  obtain ⟨w, hw0, hwspan⟩ := finrank_eq_one_iff'.1 hWrank
  have hw0V : (w : V) ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hwU : ∀ u ∈ U, bil Q u (w : V) = 0 := (hWmem w).1 w.2
  have hdecomp : ∀ x : V, ∃ u ∈ U, ∃ c : F, x = u + c • (w : V) := by
    intro x
    have hx : x ∈ U ⊔ W := hc.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨u, hu, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, hc'⟩ := hwspan ⟨y, hy⟩
    have hy2 : c • (w : V) = y := congrArg Subtype.val hc'
    exact ⟨u, hu, c, by rw [hy2]⟩
  have ha0 : Q (w : V) ≠ 0 := by
    intro h
    apply hw0V
    apply hQ.1
    intro z
    obtain ⟨u, hu, c, rfl⟩ := hdecomp z
    show bil Q (w : V) (u + c • (w : V)) = 0
    rw [bil_add_right, bil_smul_right, bil_comm Q (w : V) u, hwU u hu, bil_self, h]
    simp
  -- Step B: the isotropic vector gives u₁ ∈ U with Q u₁ = -a
  obtain ⟨u, hu, c, rfl⟩ := hdecomp v
  have hQv : Q u + c ^ 2 * Q (w : V) = 0 := by
    have := hv
    rw [Q_add, bil_smul_right, hwU u hu, Q_smul] at this
    linear_combination this
  by_cases hc0 : c = 0
  · subst hc0
    exact ⟨u, hu, by simpa using hv0, by simpa using hv⟩
  have hu1U : c⁻¹ • u ∈ U := U.smul_mem _ hu
  have hu1 : Q (c⁻¹ • u) = -Q (w : V) := by
    rw [Q_smul]
    field_simp
    linear_combination hQv
  obtain ⟨u1, hu1U, hu1⟩ : ∃ u1 ∈ U, Q u1 = -Q (w : V) := ⟨_, hu1U, hu1⟩
  -- Step C: P = {x ∈ U : B(u₁, x) = 0} is binary
  let φ : U →ₗ[F] F := (QuadraticMap.associated Q u1) ∘ₗ U.subtype
  have hφu1 : φ ⟨u1, hu1U⟩ = -Q (w : V) := by
    show bil Q u1 u1 = _
    rw [bil_self, hu1]
  have hφsurj : Function.Surjective φ := fun t =>
    ⟨(t / (-Q (w : V))) • ⟨u1, hu1U⟩, by
      rw [map_smul, hφu1, smul_eq_mul]; field_simp⟩
  have hKrank : finrank F (LinearMap.ker φ) = 2 := by
    have h := LinearMap.finrank_range_add_finrank_ker φ
    rw [LinearMap.range_eq_top.2 hφsurj, finrank_top, Module.finrank_self, hU3] at h
    omega
  let pb := Module.finBasisOfFinrankEq F (LinearMap.ker φ) hKrank
  let ιK : LinearMap.ker φ →ₗ[F] V := U.subtype ∘ₗ (LinearMap.ker φ).subtype
  have hιK : Function.Injective ιK := U.injective_subtype.comp (LinearMap.ker φ).injective_subtype
  have hpU : ∀ x : LinearMap.ker φ, ιK x ∈ U := fun x => x.1.2
  have hpu1 : ∀ x : LinearMap.ker φ, bil Q u1 (ιK x) = 0 := fun x => x.2
  have hpw : ∀ x : LinearMap.ker φ, bil Q (ιK x) (w : V) = 0 := fun x => hwU _ (hpU x)
  have hu1w : bil Q u1 (w : V) = 0 := hwU u1 hu1U
  -- Step D: the base u₁, p₀, p₁, w of V
  let x : Fin 4 → V := ![u1, ιK (pb 0), ιK (pb 1), (w : V)]
  have hli : LinearIndependent F x := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_four] at hg
    replace hg : g 0 • u1 + g 1 • ιK (pb 0) + g 2 • ιK (pb 1) + g 3 • (w : V) = 0 := hg
    have e1 := congrArg (fun z => bil Q u1 z) hg
    have e2 := congrArg (fun z => bil Q (w : V) z) hg
    have hw1 : bil Q (w : V) u1 = 0 := by rw [bil_comm]; exact hu1w
    have hwp : ∀ y : LinearMap.ker φ, bil Q (w : V) (ιK y) = 0 := fun y => by
      rw [bil_comm]; exact hpw y
    simp only [bil_add_right, bil_smul_right, bil_self, hu1, hpu1, hu1w, iv_bil_zero_right,
      mul_zero, add_zero] at e1
    simp only [bil_add_right, bil_smul_right, bil_self, hw1, hwp, iv_bil_zero_right,
      mul_zero, zero_add] at e2
    have g0 : g 0 = 0 := by
      rcases mul_eq_zero.1 e1 with h | h
      · exact h
      · exact absurd (neg_eq_zero.1 h) ha0
    have g3 : g 3 = 0 := by
      rcases mul_eq_zero.1 e2 with h | h
      · exact h
      · exact absurd h ha0
    rw [g0, g3] at hg
    simp only [zero_smul, zero_add, add_zero] at hg
    have hK : g 1 • pb 0 + g 2 • pb 1 = 0 := by
      apply hιK
      rw [map_add, map_smul, map_smul, LinearMap.map_zero]
      exact hg
    have hg12 := Fintype.linearIndependent_iff.1 pb.linearIndependent ![g 1, g 2]
      (by simpa [Fin.sum_univ_two] using hK)
    intro i
    fin_cases i
    · exact g0
    · simpa using hg12 0
    · simpa using hg12 1
    · exact g3
  -- Step E: the matrix of x, and the discriminant of P
  let b' : Basis (Fin 4) F V := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h4])
  have hb' : (b' : Fin 4 → V) = x := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  set g00 := bil Q (ιK (pb 0)) (ιK (pb 0)) with hg00
  set g01 := bil Q (ιK (pb 0)) (ιK (pb 1)) with hg01
  set g11 := bil Q (ιK (pb 1)) (ιK (pb 1)) with hg11
  have hdet : (gram Q x).det = (-Q (w : V)) * (g00 * g11 - g01 * g01) * Q (w : V) :=
    det_gram_four Q u1 (ιK (pb 0)) (ιK (pb 1)) (w : V) (a := Q (w : V)) (by rw [bil_self, hu1]) (hpu1 (pb 0)) (hpu1 (pb 1)) hu1w
      (hpw (pb 0)) (hpw (pb 1)) (bil_self Q _)
  -- Step F: dP = -τ² for a nonzero τ, using dV = 1
  obtain ⟨b, r, hr⟩ := hd
  have hs := det_toMatrix_ne_zero b b'
  have hr0 : r ≠ 0 := by
    intro h0
    apply det_gram_ne_zero_of_regular Q hQ b
    rw [hr, h0, zero_mul]
  have hmain : (-Q (w : V)) * (g00 * g11 - g01 * g01) * Q (w : V) =
      (b.toMatrix b').det ^ 2 * (r * r) := by
    have h := det_gram_basis_change' Q b b'
    have hgb : gram Q (b' : Fin 4 → V) = gram Q x := by rw [hb']
    rw [hgb, hdet, hr] at h
    exact h
  set τ : F := (b.toMatrix b').det * r / Q (w : V) with hτdef
  have hτ : τ ≠ 0 := div_ne_zero (mul_ne_zero hs hr0) ha0
  have hP : g00 * g11 - g01 * g01 = -τ ^ 2 := by
    rw [hτdef]
    field_simp
    linear_combination (-1 : F) * hmain
  -- Step G: P is a hyperbolic plane (42:9), so U is isotropic
  let Qp : QuadraticForm F (LinearMap.ker φ) := Q.comp ιK
  have hbilp : ∀ y z, bil Qp y z = bil Q (ιK y) (ιK z) := fun y z => by
    simp [bil, Qp, QuadraticMap.associated_apply]
  let qb : Basis (Fin 2) F (LinearMap.ker φ) :=
    pb.unitsSMul ![Units.mk0 τ⁻¹ (inv_ne_zero hτ), 1]
  have hq : (gram Qp qb).det = -1 := by
    rw [Matrix.det_fin_two]
    have q0 : qb 0 = τ⁻¹ • pb 0 := by simp [qb, Basis.unitsSMul_apply]
    have q1 : qb 1 = pb 1 := by simp [qb, Basis.unitsSMul_apply]
    have c01 : bil Q (ιK (pb 1)) (ιK (pb 0)) = g01 := bil_comm Q _ _
    have e00 : gram Qp qb 0 0 = τ⁻¹ * τ⁻¹ * g00 := by
      simp only [gram, Matrix.of_apply]
      rw [hbilp, q0, LinearMap.map_smul, bil_smul_left, bil_smul_right]; ring
    have e11 : gram Qp qb 1 1 = g11 := by
      simp only [gram, Matrix.of_apply]
      rw [hbilp, q1]
    have e01 : gram Qp qb 0 1 = τ⁻¹ * g01 := by
      simp only [gram, Matrix.of_apply]
      rw [hbilp, q0, q1, LinearMap.map_smul, bil_smul_left]
    have e10 : gram Qp qb 1 0 = τ⁻¹ * g01 := by
      simp only [gram, Matrix.of_apply]
      rw [hbilp, q0, q1, LinearMap.map_smul, bil_smul_right, c01]
    rw [e00, e11, e01, e10]
    field_simp
    linear_combination hP
  have h2 : finrank F (LinearMap.ker φ) = 2 := hKrank
  have h21 : (∃ b : Basis (Fin 2) F (LinearMap.ker φ), (gram Qp b).det = -1) →
      (∃ y : LinearMap.ker φ, y ≠ 0 ∧ Qp y = 0) ∧ (QuadraticMap.associated Qp).Nondegenerate :=
    (List.TFAE.out (isHyperbolicPlane_tfae Qp h2) 3 2).mp
  obtain ⟨⟨y, hy0, hy⟩, -⟩ := h21 ⟨qb, hq⟩
  refine ⟨ιK y, hpU y, fun h => hy0 (hιK ?_), hy⟩
  rw [h, LinearMap.map_zero]

end GramSpace

end Sec42Index

attribute [kb "omeara1963" "§42F, p. 99 (V = H_1 ⊥ … ⊥ H_r ⊥ V_0, V_0 zero or anisotropic)"]
  QuadraticForm.exists_wittDecomposition
attribute [kb "omeara1963" "§42A, p. 90 (orthogonal base; V ≅ ⟨α_1⟩ ⊥ … ⊥ ⟨α_n⟩)"] IsOrthogonalBasis

end QuadFormsKB.OMeara
