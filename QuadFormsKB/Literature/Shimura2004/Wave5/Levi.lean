/-
# Shimura 2004, §4.1 and §4.7: the Levi decomposition of a parabolic subgroup of $O^\varphi$

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), §4.1 (formulas (4.3)–(4.7),
printed pp. 28–29) and §4.7 (formulas (4.22), (4.23), printed p. 32). Page numbers are printed pages.

**Setting and dictionary.** As in `Wave2/Parabolic.lean`: $F$ a field of characteristic $\ne 2$ (`Invertible 2`),
`Q : QuadraticForm F V` on a finite-dimensional $V$ with $Q(x) = \varphi[x]$, and $2\varphi(x, y)$ =
`QuadraticMap.polar Q x y`. Linear maps act on the left, so Shimura's $J\alpha$ is `J.map α`. Shimura's setting (4.3)
is a weak Witt decomposition $V = I'_m + W + I_m$ with $I_m = \sum_{i \le m} Fe_i$, $I'_m = \sum_{i\le m} Ff_i$,
$2\varphi(e_i, f_j) = \delta_{ij}$, $\varphi(e_i, e_j) = \varphi(f_i, f_j) = 0$, and $W$ the orthogonal complement of
$I_m + I'_m$. Here the vectors are `e f : Fin m → V` (indices $0, \dots, m-1$: Shimura's $e_1, \dots, e_m$ are
`e 0, …, e (m-1)`), the hypothesis is `IsHypFamily Q e f`, $I_m$ = `spanE F e`, $I'_m$ = `spanE F f`, and
$W$ = `wSpace Q e f` is *defined* as the orthogonal complement (so (4.3) is a theorem, `decomp`). Shimura's
$J = I_m$, so $P^\varphi_m = P^J \cap SO^\varphi$ (4.8a) is `parabolicSO Q (spanE F e)` of wave 2.

Nondegeneracy of $\varphi$ is not needed for anything in this file (Shimura assumes it throughout).

**Defines**
* the projections of $V = I_m + W + I'_m$ onto its three summands (`projE`, `projF`, `projW`);
* (4.7) $\pi^J : P^J \to O^\omega(W)$, $\pi^J(\varepsilon)$ the element $\beta$ with $z\varepsilon - z\beta \in J$
  for $z \in W$ (`piJ`; values in $O^\omega$ by `piJ_mem_orth`, characterized by `piJ_spec`, `piJ_unique`);
* (4.23a) $Q^\varphi = \{\mathrm{diag}[\hat a, e, a] \mid a \in GL_m(F),\ e \in SO^\omega(W)\}$ (`leviQ`), as the
  isometries preserving each of $I'_m$, $W$, $I_m$ whose restriction to $W$ has determinant $1$, and its
  $O^\omega$-version (`leviQO`);
* (4.23b) $R^\varphi = P^\varphi_m \cap \mathrm{Ker}(\pi^\varphi) \cap \mathrm{Ker}(\lambda^\varphi)$ (`unipR`), and
  its $O$-version $P^J \cap \mathrm{Ker}\,\pi^J \cap \mathrm{Ker}\,\lambda^J$ (`unipRO`).

**Proves** (all unconditional; standard axioms only)
* (4.3) $V = I_m \oplus W \oplus I'_m$ (`decomp`, `projE_*`, `projF_*`, `projW_*`), $I_m$ and $I'_m$ totally
  isotropic and in duality (`Q_eq_zero_of_mem_spanE`, `eq_zero_of_polar_spanE`);
* (4.6), the shape of $P^J$: $\varepsilon \in P^J$ maps $J^\perp = I_m + W$ into itself (`map_perp_le`), with
  diagonal blocks $d = \lambda^J(\varepsilon)$ and $e = \pi^J(\varepsilon)$, the block $a$ dual to $d$ by (4.22)
  (`polar_projF_map`);
* (4.7) $\pi^J$ is a homomorphism into $O^\omega(W)$ (`piJ`, `piJ_mem_orth`);
* (4.23) $P^J = Q^J R^J$ with $Q^J \cap R^J = 1$ and $R^J$ normal in $P^J$ (`parabolicO_eq_leviQO_mul_unipRO`,
  `leviQO_inf_unipRO`, `unipRO_normal`); the $SO$-version used by Shimura, $P^\varphi_m = Q^\varphi R^\varphi$ with
  $R^\varphi$ normal in $P^\varphi_m$, is in `Wave5/Det.lean` (`theorem_4_23`, `unipR_normal`), since it needs
  determinants;
* the description of $R^\varphi$ as the elements of (4.6) with $d = 1$ and $e = 1$ (`mem_unipRO_iff`).
-/
import QuadFormsKB.Literature.Shimura2004.Wave2.Parabolic
import QuadFormsKB.Citation

open Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.OMeara

namespace Levi

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V} {m : ℕ}

/-! ### The setting (4.3) -/

/-- **A hyperbolic family** $e_0, \dots, e_{m-1}, f_0, \dots, f_{m-1}$ (the isotropic part of Shimura's Witt
decomposition (1.2a), (4.3), p. 28): $\varphi(e_i, e_j) = \varphi(f_i, f_j) = 0$ and $2\varphi(e_i, f_j) =
\delta_{ij}$, written with `QuadraticMap.polar Q` $= 2\varphi$. -/
@[kb "shimura2004" "(4.3), p. 28 (the hyperbolic pairs e_i, f_i of a weak Witt decomposition)"]
structure IsHypFamily (Q : QuadraticForm F V) (e f : Fin m → V) : Prop where
  /-- $\varphi(e_i, e_j) = 0$. -/
  polar_e_e : ∀ i j, QuadraticMap.polar Q (e i) (e j) = 0
  /-- $\varphi(f_i, f_j) = 0$. -/
  polar_f_f : ∀ i j, QuadraticMap.polar Q (f i) (f j) = 0
  /-- $2\varphi(e_i, f_j) = \delta_{ij}$. -/
  polar_e_f : ∀ i j, QuadraticMap.polar Q (e i) (f j) = if i = j then 1 else 0

/-- The span $\sum_i Fv_i$ of a family of vectors; Shimura's $I_m$ is `spanE F e`, $I'_m$ is `spanE F f` (4.1a). -/
@[kb "shimura2004" "(4.1a), p. 28 (I_m = Σ Fe_i, I'_m = Σ Ff_i)"]
def spanE (F : Type*) [Field F] [Module F V] (e : Fin m → V) : Submodule F V :=
  Submodule.span F (Set.range e)

variable (Q) in
/-- **Shimura's $W$** in (4.3), p. 28: the orthogonal complement of $I_m + I'_m$, i.e. the vectors $x$ with
$\varphi(x, e_i) = \varphi(x, f_i) = 0$ for all $i$. -/
@[kb "shimura2004" "(4.3), p. 28 (W, the orthogonal complement of I_m + I'_m)"]
def wSpace (e f : Fin m → V) : Submodule F V where
  carrier := {x | ∀ i, QuadraticMap.polar Q x (e i) = 0 ∧ QuadraticMap.polar Q x (f i) = 0}
  add_mem' := by
    intro x y hx hy i
    simp [QuadraticMap.polar_add_left, (hx i).1, (hx i).2, (hy i).1, (hy i).2]
  zero_mem' := by intro i; simp
  smul_mem' := by
    intro c x hx i
    simp [QuadraticMap.polar_smul_left, (hx i).1, (hx i).2]

theorem mem_wSpace {e f : Fin m → V} {x : V} :
    x ∈ wSpace Q e f ↔ ∀ i, QuadraticMap.polar Q x (e i) = 0 ∧ QuadraticMap.polar Q x (f i) = 0 := Iff.rfl

/-! ### Elementary facts on `polar` -/

theorem polar_sum_smul_left (c : Fin m → F) (u : Fin m → V) (y : V) :
    QuadraticMap.polar Q (∑ i, c i • u i) y = ∑ i, c i * QuadraticMap.polar Q (u i) y := by
  have h : ∀ x, QuadraticMap.polar Q x y = QuadraticMap.polarBilin Q x y := fun x => rfl
  rw [h, map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, ← h]

/-- Vanishing of $\varphi(x, \cdot)$ on a span follows from vanishing on the generators. -/
theorem polar_eq_zero_of_mem_spanE {u : Fin m → V} {x : V} (hx : ∀ i, QuadraticMap.polar Q x (u i) = 0)
    {y : V} (hy : y ∈ spanE F u) : QuadraticMap.polar Q x y = 0 := by
  have hle : spanE F u ≤ LinearMap.ker (QuadraticMap.polarBilin Q x) := by
    rw [spanE, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp [QuadraticMap.polarBilin_apply_apply, hx i]
  simpa [QuadraticMap.polarBilin_apply_apply] using hle hy

/-- An isometry preserves `polar`. -/
theorem polar_map_of_mem_orth {α : V ≃ₗ[F] V} (hα : α ∈ orth Q) (x y : V) :
    QuadraticMap.polar Q (α x) (α y) = QuadraticMap.polar Q x y := by
  simp only [QuadraticMap.polar, ← map_add]
  rw [hα (x + y), hα x, hα y]

theorem Q_eq_half_polar (x : V) : Q x = ⅟(2 : F) * QuadraticMap.polar Q x x := by
  rw [QuadraticMap.polar_self, two_nsmul, ← two_mul, ← mul_assoc, invOf_mul_self, one_mul]

section Hyp

variable {e f : Fin m → V} (hH : IsHypFamily Q e f)
include hH

theorem polar_f_e (i j : Fin m) : QuadraticMap.polar Q (f i) (e j) = if i = j then 1 else 0 := by
  rw [QuadraticMap.polar_comm Q, hH.polar_e_f]; simp [eq_comm]

/-- $I_m$ is totally isotropic: $\varphi(x, y) = 0$ for $x, y \in I_m$. -/
theorem polar_spanE_spanE {x y : V} (hx : x ∈ spanE F e) (hy : y ∈ spanE F e) : QuadraticMap.polar Q x y = 0 := by
  have hx' : ∀ i, QuadraticMap.polar Q y (e i) = 0 := fun i =>
    by rw [QuadraticMap.polar_comm Q]; exact polar_eq_zero_of_mem_spanE (hH.polar_e_e i) hy
  rw [QuadraticMap.polar_comm Q]; exact polar_eq_zero_of_mem_spanE hx' hx

/-- $I'_m$ is totally isotropic. -/
theorem polar_spanF_spanF {x y : V} (hx : x ∈ spanE F f) (hy : y ∈ spanE F f) : QuadraticMap.polar Q x y = 0 := by
  have hx' : ∀ i, QuadraticMap.polar Q y (f i) = 0 := fun i =>
    by rw [QuadraticMap.polar_comm Q]; exact polar_eq_zero_of_mem_spanE (hH.polar_f_f i) hy
  rw [QuadraticMap.polar_comm Q]; exact polar_eq_zero_of_mem_spanE hx' hx

/-- $\varphi[x] = 0$ on $I_m$. -/
theorem Q_eq_zero_of_mem_spanE {x : V} (hx : x ∈ spanE F e) : Q x = 0 := by
  rw [Q_eq_half_polar, polar_spanE_spanE hH hx hx, mul_zero]

/-- $\varphi[x] = 0$ on $I'_m$. -/
theorem Q_eq_zero_of_mem_spanF {x : V} (hx : x ∈ spanE F f) : Q x = 0 := by
  rw [Q_eq_half_polar, polar_spanF_spanF hH hx hx, mul_zero]

omit hH in
theorem polar_wSpace_spanE {x y : V} (hx : x ∈ wSpace Q e f) (hy : y ∈ spanE F e) :
    QuadraticMap.polar Q x y = 0 :=
  polar_eq_zero_of_mem_spanE (fun i => (hx i).1) hy

omit hH in
theorem polar_wSpace_spanF {x y : V} (hx : x ∈ wSpace Q e f) (hy : y ∈ spanE F f) :
    QuadraticMap.polar Q x y = 0 :=
  polar_eq_zero_of_mem_spanE (fun i => (hx i).2) hy

end Hyp

/-! ### The projections of $V = I_m + W + I'_m$ -/

variable (Q) in
/-- The projection onto $I_m$: $x \mapsto \sum_i 2\varphi(x, f_i)\,e_i$. -/
def projE (e f : Fin m → V) : V →ₗ[F] V :=
  ∑ i, LinearMap.smulRight ((QuadraticMap.polarBilin Q).flip (f i)) (e i)

variable (Q) in
/-- The projection onto $I'_m$: $x \mapsto \sum_i 2\varphi(x, e_i)\,f_i$. -/
def projF (e f : Fin m → V) : V →ₗ[F] V :=
  ∑ i, LinearMap.smulRight ((QuadraticMap.polarBilin Q).flip (e i)) (f i)

variable (Q) in
/-- The projection onto $W$: $x \mapsto x - (\text{projection onto } I_m) - (\text{projection onto } I'_m)$. -/
def projW (e f : Fin m → V) : V →ₗ[F] V := LinearMap.id - projE Q e f - projF Q e f

variable {e f : Fin m → V}

theorem projE_apply (x : V) : projE Q e f x = ∑ i, QuadraticMap.polar Q x (f i) • e i := by
  simp [projE, LinearMap.sum_apply, QuadraticMap.polarBilin_apply_apply]

theorem projF_apply (x : V) : projF Q e f x = ∑ i, QuadraticMap.polar Q x (e i) • f i := by
  simp [projF, LinearMap.sum_apply, QuadraticMap.polarBilin_apply_apply]

theorem projW_apply (x : V) : projW Q e f x = x - projE Q e f x - projF Q e f x := rfl

/-- **(4.3)**: $x = x_{I_m} + x_W + x_{I'_m}$. -/
@[kb "shimura2004" "(4.3), p. 28 (V = I'_m + W + I_m)"]
theorem decomp (x : V) : x = projE Q e f x + projW Q e f x + projF Q e f x := by
  rw [projW_apply]; abel

theorem projE_mem (x : V) : projE Q e f x ∈ spanE F e := by
  rw [projE_apply]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem projF_mem (x : V) : projF Q e f x ∈ spanE F f := by
  rw [projF_apply]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

section Hyp

variable (hH : IsHypFamily Q e f)
include hH

theorem polar_projE_f (x : V) (j : Fin m) :
    QuadraticMap.polar Q (projE Q e f x) (f j) = QuadraticMap.polar Q x (f j) := by
  rw [projE_apply, polar_sum_smul_left]
  simp [hH.polar_e_f]

theorem polar_projE_e (x : V) (j : Fin m) : QuadraticMap.polar Q (projE Q e f x) (e j) = 0 := by
  rw [projE_apply, polar_sum_smul_left]
  simp [hH.polar_e_e]

theorem polar_projF_e (x : V) (j : Fin m) :
    QuadraticMap.polar Q (projF Q e f x) (e j) = QuadraticMap.polar Q x (e j) := by
  rw [projF_apply, polar_sum_smul_left]
  simp [polar_f_e hH]

theorem polar_projF_f (x : V) (j : Fin m) : QuadraticMap.polar Q (projF Q e f x) (f j) = 0 := by
  rw [projF_apply, polar_sum_smul_left]
  simp [hH.polar_f_f]

theorem projW_mem (x : V) : projW Q e f x ∈ wSpace Q e f := by
  intro i
  rw [projW_apply]
  simp only [QuadraticMap.polar_sub_left]
  rw [polar_projE_f hH, polar_projE_e hH, polar_projF_e hH, polar_projF_f hH]
  constructor <;> ring

theorem projE_of_mem_wSpace {x : V} (hx : x ∈ wSpace Q e f) : projE Q e f x = 0 := by
  rw [projE_apply]; simp [(hx _).2]

theorem projF_of_mem_wSpace {x : V} (hx : x ∈ wSpace Q e f) : projF Q e f x = 0 := by
  rw [projF_apply]; simp [(hx _).1]

theorem projW_of_mem_wSpace {x : V} (hx : x ∈ wSpace Q e f) : projW Q e f x = x := by
  rw [projW_apply, projE_of_mem_wSpace hH hx, projF_of_mem_wSpace hH hx]; abel

theorem projE_of_mem_spanE {x : V} (hx : x ∈ spanE F e) : projE Q e f x = x := by
  have hle : spanE F e ≤ LinearMap.eqLocus (projE Q e f) LinearMap.id := by
    rw [spanE, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    change projE Q e f (e i) = e i
    rw [projE_apply]
    simp [hH.polar_e_f]
  exact hle hx

theorem projF_of_mem_spanE {x : V} (hx : x ∈ spanE F e) : projF Q e f x = 0 := by
  rw [projF_apply]
  simp [polar_spanE_spanE hH hx (Submodule.subset_span ⟨_, rfl⟩)]

theorem projW_of_mem_spanE {x : V} (hx : x ∈ spanE F e) : projW Q e f x = 0 := by
  rw [projW_apply, projE_of_mem_spanE hH hx, projF_of_mem_spanE hH hx]; abel

theorem projF_of_mem_spanF {x : V} (hx : x ∈ spanE F f) : projF Q e f x = x := by
  have hle : spanE F f ≤ LinearMap.eqLocus (projF Q e f) LinearMap.id := by
    rw [spanE, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    change projF Q e f (f i) = f i
    rw [projF_apply]
    simp [polar_f_e hH]
  exact hle hx

theorem projE_of_mem_spanF {x : V} (hx : x ∈ spanE F f) : projE Q e f x = 0 := by
  rw [projE_apply]
  simp [polar_spanF_spanF hH hx (Submodule.subset_span ⟨_, rfl⟩)]

theorem projW_of_mem_spanF {x : V} (hx : x ∈ spanE F f) : projW Q e f x = 0 := by
  rw [projW_apply, projE_of_mem_spanF hH hx, projF_of_mem_spanF hH hx]; abel

/-- $x \perp I_m$ if and only if its $I'_m$-component vanishes; so $I_m^\perp = I_m + W$. -/
theorem projF_eq_zero_iff (x : V) :
    projF Q e f x = 0 ↔ ∀ y ∈ spanE F e, QuadraticMap.polar Q x y = 0 := by
  constructor
  · intro h y hy
    refine polar_eq_zero_of_mem_spanE (fun i => ?_) hy
    rw [← polar_projF_e hH, h, QuadraticMap.polar_zero_left]
  · intro h
    rw [projF_apply]
    simp [h _ (Submodule.subset_span ⟨_, rfl⟩)]

/-- **Duality of $I'_m$ and $I_m$** (§4.7, p. 32): an element of $I'_m$ orthogonal to $I_m$ is $0$. -/
theorem eq_zero_of_polar_spanE {x : V} (hx : x ∈ spanE F f) (h : ∀ y ∈ spanE F e, QuadraticMap.polar Q x y = 0) :
    x = 0 := by
  rw [← projF_of_mem_spanF hH hx]; exact (projF_eq_zero_iff hH x).2 h

/-- $\varphi[j + w + y] = \varphi[w] + 2\varphi(j, y)$ for $j \in I_m$, $w \in W$, $y \in I'_m$ (from the matrix
(4.4)). -/
theorem Q_add_add {j w y : V} (hj : j ∈ spanE F e) (hw : w ∈ wSpace Q e f) (hy : y ∈ spanE F f) :
    Q (j + w + y) = Q w + QuadraticMap.polar Q j y := by
  have h1 : Q (j + w + y) = Q (j + w) + Q y + QuadraticMap.polar Q (j + w) y := by
    rw [QuadraticMap.polar]; ring
  have h2 : Q (j + w) = Q j + Q w + QuadraticMap.polar Q j w := by rw [QuadraticMap.polar]; ring
  rw [h1, h2, QuadraticMap.polar_add_left, Q_eq_zero_of_mem_spanE hH hj, Q_eq_zero_of_mem_spanF hH hy,
    polar_wSpace_spanF hw hy, QuadraticMap.polar_comm Q j w, polar_wSpace_spanE hw hj]
  ring

/-- $\varphi[x] = \varphi[x_W] + 2\varphi(x_{I_m}, x_{I'_m})$. -/
theorem Q_eq_decomp (x : V) :
    Q x = Q (projW Q e f x) + QuadraticMap.polar Q (projE Q e f x) (projF Q e f x) := by
  conv_lhs => rw [decomp (Q := Q) (e := e) (f := f) x]
  exact Q_add_add hH (projE_mem x) (projW_mem hH x) (projF_mem x)

end Hyp

/-! ### Elements of $P^J$, $J = I_m$ -/

section Parabolic

variable (hH : IsHypFamily Q e f)
include hH

omit hH in
theorem symm_mem_spanE {α : V ≃ₗ[F] V} (hα : α ∈ parabolicO Q (spanE F e)) {y : V} (hy : y ∈ spanE F e) :
    α.symm y ∈ spanE F e := by
  have h := map_symm_eq hα.2
  rw [← h]; exact ⟨y, hy, rfl⟩

omit hH in
theorem map_mem_spanE {α : V ≃ₗ[F] V} (hα : α ∈ parabolicO Q (spanE F e)) {y : V} (hy : y ∈ spanE F e) :
    α y ∈ spanE F e := by
  rw [← hα.2]; exact ⟨y, hy, rfl⟩

/-- **(4.6)**: $\varepsilon \in P^J$ maps $J^\perp = I_m + W$ into itself (the zero blocks of (4.6)). -/
@[kb "shimura2004" "(4.6), p. 29 (the elements of P^J are block upper triangular)"]
theorem map_perp_le {α : V ≃ₗ[F] V} (hα : α ∈ parabolicO Q (spanE F e)) {x : V}
    (hx : ∀ y ∈ spanE F e, QuadraticMap.polar Q x y = 0) : ∀ y ∈ spanE F e, QuadraticMap.polar Q (α x) y = 0 := by
  intro y hy
  have := polar_map_of_mem_orth hα.1 x (α.symm y)
  rw [LinearEquiv.apply_symm_apply] at this
  rw [this, hx _ (symm_mem_spanE hα hy)]

theorem projF_map_of_mem_wSpace {α : V ≃ₗ[F] V} (hα : α ∈ parabolicO Q (spanE F e)) {w : V}
    (hw : w ∈ wSpace Q e f) : projF Q e f (α w) = 0 :=
  (projF_eq_zero_iff hH _).2 (map_perp_le hH hα fun _ hy => polar_wSpace_spanE hw hy)

theorem projW_map_of_mem_spanE {α : V ≃ₗ[F] V} (hα : α ∈ parabolicO Q (spanE F e)) {y : V}
    (hy : y ∈ spanE F e) : projW Q e f (α y) = 0 :=
  projW_of_mem_spanE hH (map_mem_spanE hα hy)

/-- For $z \in W$: $z\varepsilon - (z\varepsilon)_W \in J$. -/
theorem sub_projW_mem {α : V ≃ₗ[F] V} (hα : α ∈ parabolicO Q (spanE F e)) {w : V} (hw : w ∈ wSpace Q e f) :
    α w - projW Q e f (α w) ∈ spanE F e := by
  have h := decomp (Q := Q) (e := e) (f := f) (α w)
  rw [projF_map_of_mem_wSpace hH hα hw, add_zero] at h
  rw [show α w - projW Q e f (α w) = projE Q e f (α w) from sub_eq_iff_eq_add.2 h]
  exact projE_mem _

/-- The $W$-block of $\varepsilon \in P^J$ as a linear map $W \to W$. -/
def piLin (α : V ≃ₗ[F] V) : wSpace Q e f →ₗ[F] wSpace Q e f :=
  ((projW Q e f ∘ₗ (α : V →ₗ[F] V) ∘ₗ (wSpace Q e f).subtype).codRestrict (wSpace Q e f)
    fun _ => projW_mem hH _)

theorem piLin_apply (α : V ≃ₗ[F] V) (w : wSpace Q e f) :
    ((piLin hH α w : wSpace Q e f) : V) = projW Q e f (α w) := rfl

theorem projW_map_projW {α : V ≃ₗ[F] V} (hα : α ∈ parabolicO Q (spanE F e)) {x : V}
    (hx : ∀ y ∈ spanE F e, QuadraticMap.polar Q x y = 0) :
    projW Q e f (α (projW Q e f x)) = projW Q e f (α x) := by
  have h := decomp (Q := Q) (e := e) (f := f) x
  rw [(projF_eq_zero_iff hH x).2 hx, add_zero] at h
  conv_rhs => rw [h]
  rw [map_add, map_add, projW_map_of_mem_spanE hH hα (projE_mem x), zero_add]

theorem piLin_mul {α β : V ≃ₗ[F] V} (hα : α ∈ parabolicO Q (spanE F e)) (hβ : β ∈ parabolicO Q (spanE F e)) :
    piLin hH (α * β) = piLin hH α ∘ₗ piLin hH β := by
  ext w
  simp only [piLin_apply, LinearMap.comp_apply, LinearEquiv.mul_apply]
  rw [projW_map_projW hH hα]
  exact map_perp_le hH hβ fun _ hy => polar_wSpace_spanE w.2 hy

theorem piLin_one : piLin hH (1 : V ≃ₗ[F] V) = LinearMap.id := by
  ext w
  simp [piLin_apply, projW_of_mem_wSpace hH w.2]

variable (e f) in
/-- **The homomorphism $\pi^J : P^J \to O^\omega(W)$** of (4.7) (Shimura, p. 29), for $J = I_m$:
$\pi^J(\varepsilon) = \beta$ with $z\varepsilon - z\beta \in J$ for every $z \in W$; here
$\beta(z) = (\varepsilon z)_W$. -/
@[kb "shimura2004" "(4.7), p. 29 (π^J : P^J → O^ω, the W-block of ε)"]
def piJ : parabolicO Q (spanE F e) →* (wSpace Q e f ≃ₗ[F] wSpace Q e f) where
  toFun α := LinearEquiv.ofLinearMap (piLin hH (α : V ≃ₗ[F] V)) (piLin hH ((α : V ≃ₗ[F] V)⁻¹))
    (by rw [← piLin_mul hH α.2 (inv_mem α.2), mul_inv_cancel, piLin_one])
    (by rw [← piLin_mul hH (inv_mem α.2) α.2, inv_mul_cancel, piLin_one])
  map_one' := by ext w; simp [piLin_apply, projW_of_mem_wSpace hH w.2]
  map_mul' α β := by
    ext w
    change ((piLin hH ((α : V ≃ₗ[F] V) * β) w : wSpace Q e f) : V) = _
    rw [piLin_mul hH α.2 β.2]; rfl

theorem piJ_apply (α : parabolicO Q (spanE F e)) (w : wSpace Q e f) :
    ((piJ e f hH α w : wSpace Q e f) : V) = projW Q e f ((α : V ≃ₗ[F] V) w) := rfl

/-- The defining property of $\pi^J(\varepsilon)$ (4.7): $z\varepsilon - z\pi^J(\varepsilon) \in J$ for $z \in W$. -/
@[kb "shimura2004" "(4.7), p. 29 (zε − zβ ∈ J for every z ∈ W)"]
theorem piJ_spec (α : parabolicO Q (spanE F e)) (w : wSpace Q e f) :
    (α : V ≃ₗ[F] V) w - (piJ e f hH α w : V) ∈ spanE F e :=
  sub_projW_mem hH α.2 w.2

/-- $\pi^J(\varepsilon)$ is the only $\beta : W \to W$ with $z\varepsilon - z\beta \in J$ for $z \in W$. -/
theorem piJ_unique (α : parabolicO Q (spanE F e)) (β : wSpace Q e f → wSpace Q e f)
    (hβ : ∀ w : wSpace Q e f, (α : V ≃ₗ[F] V) w - (β w : V) ∈ spanE F e) (w : wSpace Q e f) : β w = piJ e f hH α w := by
  apply Subtype.ext
  have h1 := hβ w
  have h2 := piJ_spec hH α w
  have hd : ((piJ e f hH α w : wSpace Q e f) : V) - (β w : V) ∈ spanE F e ⊓ wSpace Q e f := by
    refine ⟨?_, sub_mem (piJ e f hH α w).2 (β w).2⟩
    have := sub_mem h1 h2
    rwa [sub_sub_sub_cancel_left] at this
  have h0 : projW Q e f ((piJ e f hH α w : V) - β w) = 0 := projW_of_mem_spanE hH hd.1
  rw [projW_of_mem_wSpace hH hd.2] at h0
  exact (sub_eq_zero.1 h0).symm

/-- $\pi^J(\varepsilon) \in O^\omega(W)$, $\omega$ the restriction of $\varphi$ to $W$ (4.7). -/
@[kb "shimura2004" "(4.7), p. 29 (π^J takes values in O^ω)"]
theorem piJ_mem_orth (α : parabolicO Q (spanE F e)) : piJ e f hH α ∈ orth (Q.restrict (wSpace Q e f)) := by
  intro w
  simp only [QuadraticMap.restrict_apply]
  rw [piJ_apply]
  have hj := sub_projW_mem hH α.2 w.2
  have hQ := Q_eq_decomp hH ((α : V ≃ₗ[F] V) w)
  rw [projF_map_of_mem_wSpace hH α.2 w.2, QuadraticMap.polar_zero_right, add_zero, α.2.1] at hQ
  exact hQ.symm

/-! ### $Q^J$ and $R^J$ -/

omit hH in
variable (Q e f) in
/-- **$Q^J$ with $e \in O^\omega(W)$**: the isometries $\mathrm{diag}[\hat a, e, a]$ preserving each of $I'_m$, $W$
and $I_m$ (cf. (4.23a), p. 32, which takes $e \in SO^\omega(W)$; that group is `leviQ`). -/
def leviQO : Subgroup (V ≃ₗ[F] V) where
  carrier := {q | q ∈ orth Q ∧ (spanE F e).map (q : V →ₗ[F] V) = spanE F e ∧
    (spanE F f).map (q : V →ₗ[F] V) = spanE F f ∧ (wSpace Q e f).map (q : V →ₗ[F] V) = wSpace Q e f}
  one_mem' := ⟨(orth Q).one_mem, by simp, by simp, by simp⟩
  mul_mem' := by
    rintro α β ⟨hα, h1, h2, h3⟩ ⟨hβ, k1, k2, k3⟩
    refine ⟨(orth Q).mul_mem hα hβ, ?_, ?_, ?_⟩ <;>
    · change Submodule.map ((α : V →ₗ[F] V) ∘ₗ (β : V →ₗ[F] V)) _ = _
      rw [Submodule.map_comp]
      simp only [*]
  inv_mem' := by
    rintro α ⟨hα, h1, h2, h3⟩
    exact ⟨(orth Q).inv_mem hα, map_symm_eq h1, map_symm_eq h2, map_symm_eq h3⟩

omit hH in
theorem leviQO_le : leviQO Q e f ≤ parabolicO Q (spanE F e) := fun _ h => ⟨h.1, h.2.1⟩

omit hH in
variable (Q e f) in
/-- **$R^J = P^J \cap \mathrm{Ker}(\pi^J) \cap \mathrm{Ker}(\lambda^J)$** ((4.23b), p. 32, before intersecting with
$SO^\varphi$): the elements of $P^J$ acting as the identity on $J = I_m$ and on $J^\perp/J \cong W$. Stated with the
explicit conditions; `mem_unipRO_iff` identifies them with the kernels of `piJ` and `lambdaJ`. -/
def unipRO : Subgroup (V ≃ₗ[F] V) where
  carrier := {r | r ∈ parabolicO Q (spanE F e) ∧ (∀ x ∈ spanE F e, r x = x) ∧
    ∀ w ∈ wSpace Q e f, r w - w ∈ spanE F e}
  one_mem' := ⟨(parabolicO Q _).one_mem, fun _ _ => rfl, fun w _ => by simp⟩
  mul_mem' := by
    rintro α β ⟨hα, h1, h2⟩ ⟨hβ, k1, k2⟩
    refine ⟨(parabolicO Q _).mul_mem hα hβ, fun x hx => ?_, fun w hw => ?_⟩
    · simp [LinearEquiv.mul_apply, k1 x hx, h1 x hx]
    · rw [LinearEquiv.mul_apply]
      have hk := k2 w hw
      have : α (β w) - w = α (β w - w) + (α w - w) := by rw [map_sub]; abel
      rw [this, h1 _ hk]
      exact add_mem hk (h2 w hw)
  inv_mem' := by
    rintro α ⟨hα, h1, h2⟩
    refine ⟨(parabolicO Q _).inv_mem hα, fun x hx => ?_, fun w hw => ?_⟩
    · have := h1 _ (symm_mem_spanE hα hx)
      rw [LinearEquiv.apply_symm_apply] at this
      change α.symm x = x
      conv_lhs => rw [← this]
    · change α.symm w - w ∈ spanE F e
      have hk := h2 _ hw
      have h3 := h1 _ hk
      have : α.symm w - w = -(α.symm (α w - w)) := by
        rw [map_sub, LinearEquiv.symm_apply_apply]; abel
      have h4 : α.symm (α w - w) = α w - w := by rw [LinearEquiv.symm_apply_eq]; exact h3.symm
      rw [this, h4]
      exact neg_mem hk

/-- **(4.23b)**: $R^J$ is $P^J \cap \mathrm{Ker}(\pi^J) \cap \mathrm{Ker}(\lambda^J)$, i.e. the elements (4.6) with
$d = 1$ and $e = 1$. -/
@[kb "shimura2004" "(4.23b), p. 32 (R^φ = P^φ ∩ Ker π^φ ∩ Ker λ^φ)"]
theorem mem_unipRO_iff (α : V ≃ₗ[F] V) :
    α ∈ unipRO Q e f ↔ ∃ h : α ∈ parabolicO Q (spanE F e), lambdaJ (spanE F e) ⟨α, h⟩ = 1 ∧ piJ e f hH ⟨α, h⟩ = 1 := by
  constructor
  · rintro ⟨h, h1, h2⟩
    refine ⟨h, ?_, ?_⟩
    · ext x; exact h1 x x.2
    · ext w
      rw [piJ_apply]
      have hd := decomp (Q := Q) (e := e) (f := f) (α w)
      have hk := h2 w w.2
      rw [projF_map_of_mem_wSpace hH h w.2, add_zero] at hd
      have : projW Q e f (α w) - w = (α w - w) - projE Q e f (α w) := by
        generalize projE Q e f (α w) = a at hd ⊢
        generalize projW Q e f (α w) = b at hd ⊢
        rw [hd]; abel
      have hm : projW Q e f (α w) - w ∈ spanE F e ⊓ wSpace Q e f :=
        ⟨this ▸ sub_mem hk (projE_mem _), sub_mem (projW_mem hH _) w.2⟩
      have h0 := projW_of_mem_spanE hH hm.1
      rw [projW_of_mem_wSpace hH hm.2] at h0
      simpa using sub_eq_zero.1 h0
  · rintro ⟨h, h1, h2⟩
    refine ⟨h, fun x hx => ?_, fun w hw => ?_⟩
    · have := congrArg (fun g : spanE F e ≃ₗ[F] spanE F e => (g ⟨x, hx⟩ : V)) h1
      simpa [lambdaJ_apply] using this
    · have hs := piJ_spec hH ⟨α, h⟩ ⟨w, hw⟩
      rw [h2] at hs
      simpa using hs

theorem leviQO_inf_unipRO_aux {q : V ≃ₗ[F] V} (hq : q ∈ leviQO Q e f) (hr : q ∈ unipRO Q e f) (x : V) :
    q x = x := by
  obtain ⟨hqO, hqE, hqF, hqW⟩ := hq
  obtain ⟨_, h1, h2⟩ := hr
  have hmapF : ∀ y ∈ spanE F f, q y ∈ spanE F f := fun y hy => by rw [← hqF]; exact ⟨y, hy, rfl⟩
  have hmapW : ∀ y ∈ wSpace Q e f, q y ∈ wSpace Q e f := fun y hy => by rw [← hqW]; exact ⟨y, hy, rfl⟩
  rw [decomp (Q := Q) (e := e) (f := f) x, map_add, map_add]
  congr 1
  congr 1
  · exact h1 _ (projE_mem x)
  · -- on `W`: `q w - w ∈ J ∩ W = 0`
    have hw := projW_mem hH x
    have hm : q (projW Q e f x) - projW Q e f x ∈ spanE F e ⊓ wSpace Q e f :=
      ⟨h2 _ hw, sub_mem (hmapW _ hw) hw⟩
    have h0 := projW_of_mem_spanE hH hm.1
    rw [projW_of_mem_wSpace hH hm.2] at h0
    exact sub_eq_zero.1 h0
  · -- on `I'_m`: by duality with `I_m`
    have hy := projF_mem (Q := Q) (e := e) (f := f) x
    refine sub_eq_zero.1 (eq_zero_of_polar_spanE hH (sub_mem (hmapF _ hy) hy) fun z hz => ?_)
    rw [QuadraticMap.polar_sub_left]
    have := polar_map_of_mem_orth hqO (projF Q e f x) z
    rw [h1 z hz] at this
    rw [this, sub_self]

/-- **$Q^J \cap R^J = 1$** (§4.7, p. 32): the product $P^J = Q^JR^J$ is semidirect. -/
@[kb "shimura2004" "§4.7, p. 32 (Q^φ ∩ R^φ = 1)"]
theorem leviQO_inf_unipRO : leviQO Q e f ⊓ unipRO Q e f = ⊥ := by
  rw [eq_bot_iff]
  rintro q ⟨hq, hr⟩
  rw [Subgroup.mem_bot]
  ext x
  exact leviQO_inf_unipRO_aux hH hq hr x

/-- $R^J$ is a normal subgroup of $P^J$ (§4.7, p. 32). -/
@[kb "shimura2004" "§4.7, p. 32 (R^φ is a normal subgroup of P^φ)"]
theorem unipRO_normal : ((unipRO Q e f).subgroupOf (parabolicO Q (spanE F e))).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨h, h1, h2⟩ := (mem_unipRO_iff hH _).1 hn
  refine (mem_unipRO_iff hH _).2 ⟨(g * n * g⁻¹).2, ?_, ?_⟩
  · have : (⟨_, (g * n * g⁻¹).2⟩ : parabolicO Q (spanE F e)) = g * ⟨n, h⟩ * g⁻¹ := rfl
    rw [this, map_mul, map_mul, h1, mul_one, map_inv, mul_inv_cancel]
  · have : (⟨_, (g * n * g⁻¹).2⟩ : parabolicO Q (spanE F e)) = g * ⟨n, h⟩ * g⁻¹ := rfl
    rw [this, map_mul, map_mul, h2, mul_one, map_inv, mul_inv_cancel]

/-! ### The Levi factor of an element of $P^J$ -/

/-- The block-diagonal part $\mathrm{diag}[a, e, d]$ of $\varepsilon \in P^J$, as a linear map. -/
def leviLin (α : V ≃ₗ[F] V) : V →ₗ[F] V :=
  (α : V →ₗ[F] V) ∘ₗ projE Q e f + projW Q e f ∘ₗ (α : V →ₗ[F] V) ∘ₗ projW Q e f +
    projF Q e f ∘ₗ (α : V →ₗ[F] V) ∘ₗ projF Q e f

omit hH in
theorem leviLin_apply (α : V ≃ₗ[F] V) (x : V) : leviLin (Q := Q) (e := e) (f := f) α x =
    α (projE Q e f x) + projW Q e f (α (projW Q e f x)) + projF Q e f (α (projF Q e f x)) := rfl

/-- **(4.22)**: the blocks $a$ (on $I'_m$) and $d$ (on $I_m$) of $\varepsilon \in P^J$ are dual:
$\varphi(x a, y d) = \varphi(x, y)$ for $x \in I'_m$, $y \in I_m$. -/
@[kb "shimura2004" "(4.22), p. 32 (φ(xâ, ya) = φ(x, y): the diagonal blocks of (4.6) are dual)"]
theorem polar_projF_map {α : V ≃ₗ[F] V} (hα : α ∈ parabolicO Q (spanE F e)) (x : V) {y : V} (hy : y ∈ spanE F e) :
    QuadraticMap.polar Q (projF Q e f (α x)) (α y) = QuadraticMap.polar Q x y := by
  have hαy := map_mem_spanE hα hy
  have h := decomp (Q := Q) (e := e) (f := f) (α x)
  have key : QuadraticMap.polar Q (α x) (α y) = QuadraticMap.polar Q (projF Q e f (α x)) (α y) := by
    conv_lhs => rw [h]
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_add_left, polar_spanE_spanE hH (projE_mem _) hαy,
      polar_wSpace_spanE (projW_mem hH _) hαy]
    ring
  rw [← key, polar_map_of_mem_orth hα.1]

theorem leviLin_injective {α : V ≃ₗ[F] V} (hα : α ∈ parabolicO Q (spanE F e)) :
    Function.Injective (leviLin (Q := Q) (e := e) (f := f) α) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  rw [leviLin_apply] at hx
  set j := α (projE Q e f x)
  set w := projW Q e f (α (projW Q e f x))
  set y := projF Q e f (α (projF Q e f x))
  have hj : j ∈ spanE F e := map_mem_spanE hα (projE_mem x)
  have hw : w ∈ wSpace Q e f := projW_mem hH _
  have hy : y ∈ spanE F f := projF_mem _
  -- the three components of `j + w + y = 0` vanish
  have hj0 : j = 0 := by
    have := congrArg (projE Q e f) hx
    rwa [map_add, map_add, projE_of_mem_spanE hH hj, projE_of_mem_wSpace hH hw, projE_of_mem_spanF hH hy,
      map_zero, add_zero, add_zero] at this
  have hw0 : w = 0 := by
    have := congrArg (projW Q e f) hx
    rwa [map_add, map_add, projW_of_mem_spanE hH hj, projW_of_mem_wSpace hH hw, projW_of_mem_spanF hH hy,
      map_zero, zero_add, add_zero] at this
  have hy0 : y = 0 := by
    have := congrArg (projF Q e f) hx
    rwa [map_add, map_add, projF_of_mem_spanE hH hj, projF_of_mem_wSpace hH hw, projF_of_mem_spanF hH hy,
      map_zero, zero_add, zero_add] at this
  -- so each component of `x` vanishes
  have hxE : projE Q e f x = 0 := by
    have : α (projE Q e f x) = α 0 := by rw [map_zero]; exact hj0
    exact α.injective this
  have hxW : projW Q e f x = 0 := by
    have hpi : piJ e f hH ⟨α, hα⟩ ⟨_, projW_mem hH x⟩ = 0 := Subtype.ext hw0
    have := (piJ e f hH ⟨α, hα⟩).injective (hpi.trans (map_zero _).symm)
    exact congrArg Subtype.val this
  have hxF : projF Q e f x = 0 := by
    refine eq_zero_of_polar_spanE hH (projF_mem x) fun z hz => ?_
    have h1 := polar_projF_map hH hα (projF Q e f x) hz
    rw [← h1]
    change QuadraticMap.polar Q y _ = 0
    rw [hy0, QuadraticMap.polar_zero_left]
  rw [decomp (Q := Q) (e := e) (f := f) x, hxE, hxW, hxF]
  simp

/-- The Levi factor $\mathrm{diag}[a, e, d]$ of $\varepsilon \in P^J$, as a linear automorphism. -/
def leviPart {α : V ≃ₗ[F] V} (hα : α ∈ parabolicO Q (spanE F e)) : V ≃ₗ[F] V :=
  LinearEquiv.ofInjectiveEndo _ (leviLin_injective hH hα)

theorem leviPart_apply {α : V ≃ₗ[F] V} (hα : α ∈ parabolicO Q (spanE F e)) (x : V) :
    leviPart hH hα x = α (projE Q e f x) + projW Q e f (α (projW Q e f x)) + projF Q e f (α (projF Q e f x)) :=
  rfl

theorem leviPart_mem_orth {α : V ≃ₗ[F] V} (hα : α ∈ parabolicO Q (spanE F e)) : leviPart hH hα ∈ orth Q := by
  intro x
  rw [leviPart_apply, Q_add_add hH (map_mem_spanE hα (projE_mem x)) (projW_mem hH _) (projF_mem _)]
  -- the `W`-part
  have hW : Q (projW Q e f (α (projW Q e f x))) = Q (projW Q e f x) :=
    piJ_mem_orth hH ⟨α, hα⟩ ⟨_, projW_mem hH x⟩
  -- the hyperbolic part, by (4.22)
  have hP : QuadraticMap.polar Q (α (projE Q e f x)) (projF Q e f (α (projF Q e f x))) =
      QuadraticMap.polar Q (projE Q e f x) (projF Q e f x) := by
    rw [QuadraticMap.polar_comm Q, polar_projF_map hH hα _ (projE_mem x), QuadraticMap.polar_comm Q]
  rw [hW, hP, ← Q_eq_decomp hH]

theorem leviPart_map_le {α : V ≃ₗ[F] V} (hα : α ∈ parabolicO Q (spanE F e)) {S : Submodule F V}
    (hS : ∀ x ∈ S, leviPart hH hα x ∈ S) : S.map (leviPart hH hα : V →ₗ[F] V) = S := by
  apply map_eq_of_map_le
  rintro _ ⟨x, hx, rfl⟩
  exact hS x hx

theorem leviPart_mem_leviQO {α : V ≃ₗ[F] V} (hα : α ∈ parabolicO Q (spanE F e)) :
    leviPart hH hα ∈ leviQO Q e f := by
  refine ⟨leviPart_mem_orth hH hα, leviPart_map_le hH hα fun x hx => ?_,
    leviPart_map_le hH hα fun x hx => ?_, leviPart_map_le hH hα fun x hx => ?_⟩
  · rw [leviPart_apply, projE_of_mem_spanE hH hx, projW_of_mem_spanE hH hx, projF_of_mem_spanE hH hx]
    simpa using map_mem_spanE hα hx
  · rw [leviPart_apply, projE_of_mem_spanF hH hx, projW_of_mem_spanF hH hx, projF_of_mem_spanF hH hx]
    simpa using projF_mem _
  · rw [leviPart_apply, projE_of_mem_wSpace hH hx, projW_of_mem_wSpace hH hx, projF_of_mem_wSpace hH hx]
    simpa using projW_mem hH _

theorem leviPart_eq_on_spanE {α : V ≃ₗ[F] V} (hα : α ∈ parabolicO Q (spanE F e)) {x : V} (hx : x ∈ spanE F e) :
    leviPart hH hα x = α x := by
  rw [leviPart_apply, projE_of_mem_spanE hH hx, projW_of_mem_spanE hH hx, projF_of_mem_spanE hH hx]
  simp

theorem projW_leviPart_of_mem_wSpace {α : V ≃ₗ[F] V} (hα : α ∈ parabolicO Q (spanE F e)) {x : V}
    (hx : x ∈ wSpace Q e f) : projW Q e f (leviPart hH hα x) = projW Q e f (α x) := by
  rw [leviPart_apply, projE_of_mem_wSpace hH hx, projW_of_mem_wSpace hH hx, projF_of_mem_wSpace hH hx]
  simp [projW_of_mem_wSpace hH (projW_mem hH _)]

/-- **$P^J = Q^JR^J$** (§4.7, p. 32), with $e \in O^\omega(W)$ in $Q^J$: every $\varepsilon \in P^J$ is
$\varepsilon = qr$ with $q = \mathrm{diag}[a, \pi^J(\varepsilon), \lambda^J(\varepsilon)] \in Q^J$ and $r \in R^J$. -/
@[kb "shimura2004" "§4.7, p. 32 (P^φ = Q^φR^φ, O-version)"]
theorem parabolicO_eq_leviQO_mul_unipRO {α : V ≃ₗ[F] V} (hα : α ∈ parabolicO Q (spanE F e)) :
    ∃ q ∈ leviQO Q e f, ∃ r ∈ unipRO Q e f, α = q * r := by
  set q := leviPart hH hα
  have hq := leviPart_mem_leviQO hH hα
  have hqP : q ∈ parabolicO Q (spanE F e) := leviQO_le hq
  refine ⟨q, hq, q⁻¹ * α, ?_, by group⟩
  have hrP : q⁻¹ * α ∈ parabolicO Q (spanE F e) := mul_mem (inv_mem hqP) hα
  refine (mem_unipRO_iff hH _).2 ⟨hrP, ?_, ?_⟩
  · have hl : lambdaJ (spanE F e) ⟨q, hqP⟩ = lambdaJ (spanE F e) ⟨α, hα⟩ := by
      ext x; exact leviPart_eq_on_spanE hH hα x.2
    have : (⟨q⁻¹ * α, hrP⟩ : parabolicO Q (spanE F e)) = (⟨q, hqP⟩)⁻¹ * ⟨α, hα⟩ := rfl
    rw [this, map_mul, map_inv, hl, inv_mul_cancel]
  · have hp : piJ e f hH ⟨q, hqP⟩ = piJ e f hH ⟨α, hα⟩ := by
      ext w; rw [piJ_apply, piJ_apply]; exact projW_leviPart_of_mem_wSpace hH hα w.2
    have : (⟨q⁻¹ * α, hrP⟩ : parabolicO Q (spanE F e)) = (⟨q, hqP⟩)⁻¹ * ⟨α, hα⟩ := rfl
    rw [this, map_mul, map_inv, hp, inv_mul_cancel]

end Parabolic

end Levi

end QuadFormsKB.Shimura2004
