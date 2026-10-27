/-
# Classification of arbitrary nondegenerate quadratic forms over every completion of a number field

Let $F$ be a number field, $v$ a place of $F$ (`NFPlace F`), and $Q, R$ nondegenerate quadratic forms in $n$ variables
over $F$ (`QuadForm F n`, `Nondegenerate`: $\det H \ne 0$ for the Hessian $H = C + C^{\mathsf T}$). The classification of
`LocalClassificationNF.lean` for diagonal forms extends to $Q$ and $R$:

* **Invariants.** Each nondegenerate $Q$ is isometric over $F$ to a diagonal form $\langle a_0,\dots,a_{n-1}\rangle$ with
  $a_i \in F^\times$ (`FieldGen.exists_isometric_diag`); `LocalClassNF.diagOf Q` is one such choice. Define
  * the discriminant square class at $v$: the class of $\det H_Q$ in $F_v^\times / (F_v^\times)^2$, compared through
    "$\det H_Q / \det H_R$ is a square in $F_v$" (the Hessian determinant is $2^n$ times the Gram determinant, so for
    forms of the same dimension the two conventions give the same condition);
  * Serre's Hasse invariant `NFPlace.hasseSerreForm v Q` $:= \varepsilon_v(\langle a\rangle)$ (and likewise O'Meara's
    `hasseOMearaForm`, Shimura's `hasseShimuraForm`, Cassels' `hasseCasselsForm`, Lam's `hasseLamForm`);
  * the negative index `NFPlace.negIndexForm v Q` $:=$ `negIndex v a` (the number of negative $a_i$ under the real
    embedding at a real place, $0$ elsewhere), with the real-place version `LocalClassNF.realNegIndex`.

  These do not depend on the diagonalization: for every $a$ with $a_i \ne 0$ and $Q \cong \langle a\rangle$ over $F$,
  `hasseSerreForm v Q = v.hasseSerre a` and `negIndexForm v Q = v.negIndex a`
  (`NFPlace.hasseSerreForm_eq_of_isometric`, `NFPlace.negIndexForm_eq_of_isometric`, etc.). Two such diagonalizations
  are isometric over $F$, hence over $F_v$, so the isometry invariance of $\varepsilon_v$ and Sylvester's law of
  inertia apply.
* **Theorem** (`NFPlace.isometric_iff_general`; O'Meara 63:20, Serre IV §2.3 Thm. 7 over $\mathbb{Q}_p$):
  $Q \cong R$ over $F_v$ iff the discriminants lie in the same square class of $F_v$, the Hasse invariants at $v$
  agree, and the negative indices at $v$ agree. Finite (`LocalClassNF.isometric_finite_iff_general`), real
  (`LocalClassNF.isometric_real_iff_general`) and complex (`LocalClassNF.isometric_complex_general`) versions, and the
  same with the other Hasse conventions (`NFPlace.isometric_iff_general_hasseOMeara` etc.).
* **Consistency** (`NFPlace.hasseSerreForm_diag`, `NFPlace.negIndexForm_diag`,
  `LocalClassNF.isSquare_hessian_det_div_diag_iff`): for $Q = \langle a\rangle$ the new invariants are the old ones, so
  `NFPlace.isometric_iff` is the special case of diagonal forms.

**Route.** Replace $Q$ and $R$ by their chosen diagonalizations $\langle a\rangle$, $\langle b\rangle$: isometry over
$F_v$ is unchanged (base change of the $F$-isometries, `FieldGen.isometricIn_of_base`, and transitivity); the Hessian
determinants change by nonzero squares of $F$ ($P^{\mathsf T} H_Q P = H_{\langle a\rangle}$,
`PadicClass.transpose_mul_hessian_mul`), and $\det H_{\langle a\rangle} = 2^n \prod_i a_i$. Then apply
`NFPlace.isometric_iff`.
-/
import QuadFormsKB.Literature.LocalGlobal.LocalClassificationNF

open NumberField IsDedekindDomain

namespace QuadFormsKB

open Finset PadicClass Matrix HasseIsoNF QuadForm

variable {n : ℕ}

namespace LocalClassNF

/-! ### Generic lemmas -/

/-- Scaling by a nonzero square does not change the square class: $c \ne 0 \Rightarrow (c^2 y \in K^2 \iff y \in K^2)$. -/
theorem isSquare_sq_mul_iff {K : Type*} [Field K] {c y : K} (hc : c ≠ 0) : IsSquare (c ^ 2 * y) ↔ IsSquare y := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r / c, ?_⟩
    have : y = (c ^ 2 * y) / c ^ 2 := by field_simp
    rw [this, hr]; field_simp
  · rintro ⟨r, rfl⟩
    exact ⟨c * r, by ring⟩

/-- **The Hessian determinant changes by a nonzero square under isometry over $F$:** if $Q \cong Q'$ over $F$ then
$\det H_{Q'} = s^2 \det H_Q$ with $s \in F^\times$ (here $s = \det P$). -/
theorem hessian_det_of_isometricIn {F : Type*} [Field F] [CharZero F] {Q Q' : QuadForm F n}
    (h : Q.IsometricIn F Q') : ∃ s : F, s ≠ 0 ∧ Q'.hessian.det = s ^ 2 * Q.hessian.det := by
  obtain ⟨P, hPu, hP⟩ := h
  refine ⟨P.det, hPu.ne_zero, ?_⟩
  rw [← transpose_mul_hessian_mul hP, det_mul, det_mul, det_transpose]
  ring

/-- The Hessian determinant of a diagonal form: $\det H_{\langle a\rangle} = 2^n \prod_i a_i$. -/
theorem hessian_det_diag {K : Type*} [Field K] (a : Fin n → K) :
    (QuadForm.diag a).hessian.det = 2 ^ n * ∏ i, a i := by
  unfold hessian QuadForm.diag
  simp only [diagonal_transpose, diagonal_add, det_diagonal]
  simp [← two_mul, prod_mul_distrib]

/-- **Consistency of the discriminant conditions:** for diagonal forms, "$\det H_{\langle a\rangle} /
\det H_{\langle b\rangle}$ is a square" is literally "$\prod a_i / \prod b_i$ is a square" (the factors $2^n$ cancel). -/
theorem hessian_det_div_diag {K : Type*} [Field K] [CharZero K] (a b : Fin n → K) :
    (QuadForm.diag a).hessian.det / (QuadForm.diag b).hessian.det = (∏ i, a i) / ∏ i, b i := by
  rw [hessian_det_diag, hessian_det_diag, mul_div_mul_left _ _ (pow_ne_zero _ two_ne_zero)]

variable {F : Type} [Field F] [NumberField F]

/-! ### A chosen diagonalization -/

open Classical in
/-- **A chosen diagonalization over $F$** of a nondegenerate form $Q$: entries $a_i \in F^\times$ with
$Q \cong \langle a_0,\dots,a_{n-1}\rangle$ over $F$ (`FieldGen.exists_isometric_diag`); the constant $1$ vector for a
degenerate $Q$ (never used). The invariants below do not depend on this choice (`NFPlace.hasseSerreForm_eq_of_isometric`
and the lemmas after it). -/
noncomputable def diagOf (Q : QuadForm F n) : Fin n → F :=
  if hQ : Q.Nondegenerate then Classical.choose (FieldGen.exists_isometric_diag Q hQ) else fun _ => 1

theorem diagOf_spec {Q : QuadForm F n} (hQ : Q.Nondegenerate) :
    (∀ i, diagOf Q i ≠ 0) ∧ Q.IsometricIn F (QuadForm.diag (diagOf Q)) := by
  simp only [diagOf, hQ, ↓reduceDIte]
  exact Classical.choose_spec (FieldGen.exists_isometric_diag Q hQ)

theorem diagOf_ne_zero {Q : QuadForm F n} (hQ : Q.Nondegenerate) (i : Fin n) : diagOf Q i ≠ 0 :=
  (diagOf_spec hQ).1 i

theorem isometricIn_diagOf {Q : QuadForm F n} (hQ : Q.Nondegenerate) :
    Q.IsometricIn F (QuadForm.diag (diagOf Q)) :=
  (diagOf_spec hQ).2

/-- An isometry over $F$ holds over every completion $F_v$. -/
theorem atPlace_isometricIn_of_base (v : NFPlace F) {Q Q' : QuadForm F n} (h : Q.IsometricIn F Q') :
    v.atPlace fun K _ _ => Q.IsometricIn K Q' := by
  cases v <;> exact FieldGen.isometricIn_of_base _ h

/-- **Isometry over $F_v$ is unchanged by passing to $F$-isometric forms.** -/
theorem atPlace_isometricIn_iff_of_base (v : NFPlace F) {Q Q' R R' : QuadForm F n} (hQ : Q.IsometricIn F Q')
    (hR : R.IsometricIn F R') :
    v.atPlace (fun K _ _ => Q.IsometricIn K R) ↔ v.atPlace (fun K _ _ => Q'.IsometricIn K R') := by
  have key : ∀ (K : Type) [Field K] [Algebra F K], Q.IsometricIn K R ↔ Q'.IsometricIn K R' := by
    intro K _ _
    have hQK := FieldGen.isometricIn_of_base K hQ
    have hRK := FieldGen.isometricIn_of_base K hR
    exact ⟨fun h => isometricIn_trans K (isometricIn_trans K (isometricIn_symm K hQK) h) hRK,
      fun h => isometricIn_trans K (isometricIn_trans K hQK h) (isometricIn_symm K hRK)⟩
  cases v <;> exact key _

/-- **The discriminant condition is unchanged by passing to $F$-isometric forms.** -/
theorem atPlace_isSquare_iff_of_base (v : NFPlace F) {Q Q' R R' : QuadForm F n} (hQ : Q.IsometricIn F Q')
    (hR : R.IsometricIn F R') (hQ0 : Q.hessian.det ≠ 0) (hR0 : R.hessian.det ≠ 0) :
    v.atPlace (fun K _ _ => IsSquare (algebraMap F K (Q.hessian.det / R.hessian.det))) ↔
      v.atPlace (fun K _ _ => IsSquare (algebraMap F K (Q'.hessian.det / R'.hessian.det))) := by
  obtain ⟨s, hs, es⟩ := hessian_det_of_isometricIn hQ
  obtain ⟨t, ht, et⟩ := hessian_det_of_isometricIn hR
  have e : Q'.hessian.det / R'.hessian.det = (s / t) ^ 2 * (Q.hessian.det / R.hessian.det) := by
    rw [es, et]; field_simp
  have key : ∀ (K : Type) [Field K] [Algebra F K],
      IsSquare (algebraMap F K (Q.hessian.det / R.hessian.det)) ↔
        IsSquare (algebraMap F K (Q'.hessian.det / R'.hessian.det)) := by
    intro K _ _
    rw [e, map_mul, map_pow, isSquare_sq_mul_iff ((map_ne_zero _).mpr (div_ne_zero hs ht))]
  cases v <;> exact key _

/-- The discriminant condition for $Q, R$ is the product condition for their chosen diagonalizations. -/
theorem atPlace_isSquare_iff_diagOf (v : NFPlace F) {Q R : QuadForm F n} (hQ : Q.Nondegenerate)
    (hR : R.Nondegenerate) :
    v.atPlace (fun K _ _ => IsSquare (algebraMap F K (Q.hessian.det / R.hessian.det))) ↔
      v.atPlace (fun K _ _ => IsSquare (algebraMap F K ((∏ i, diagOf Q i) / ∏ i, diagOf R i))) := by
  rw [atPlace_isSquare_iff_of_base v (isometricIn_diagOf hQ) (isometricIn_diagOf hR) hQ hR, hessian_det_div_diag]

/-- **Consistency (discriminant):** for diagonal forms the new discriminant condition is the old one. -/
theorem isSquare_hessian_det_div_diag_iff (v : NFPlace F) (a b : Fin n → F) :
    v.atPlace (fun K _ _ => IsSquare (algebraMap F K
        ((QuadForm.diag a).hessian.det / (QuadForm.diag b).hessian.det))) ↔
      v.atPlace (fun K _ _ => IsSquare (algebraMap F K ((∏ i, a i) / ∏ i, b i))) := by
  rw [hessian_det_div_diag]

end LocalClassNF

open LocalClassNF

namespace NFPlace

variable {F : Type} [Field F] [NumberField F]

/-! ### The invariants of an arbitrary nondegenerate form -/

/-- **Serre's Hasse invariant of an arbitrary nondegenerate form $Q$ over $F$ at a place $v$:**
$\varepsilon_v(Q) := \prod_{i<j}(a_i,a_j)_v$ for any diagonalization $Q \cong \langle a_0,\dots,a_{n-1}\rangle$ over
$F$ (independent of the choice: `hasseSerreForm_eq_of_isometric`). -/
noncomputable def hasseSerreForm (v : NFPlace F) (Q : QuadForm F n) : ℤ := v.hasseSerre (diagOf Q)

/-- O'Meara's Hasse symbol $S_v(Q) := \prod_{i \le j}(a_i,a_j)_v$ of an arbitrary nondegenerate form. -/
noncomputable def hasseOMearaForm (v : NFPlace F) (Q : QuadForm F n) : ℤ := v.hasseOMeara (diagOf Q)

/-- Shimura's (Hasse's) $\alpha_v(Q)$ of an arbitrary nondegenerate form (= O'Meara's $S_v$). -/
noncomputable def hasseShimuraForm (v : NFPlace F) (Q : QuadForm F n) : ℤ := v.hasseShimura (diagOf Q)

/-- Cassels' $c_v(Q)$ of an arbitrary nondegenerate form (= Serre's $\varepsilon_v$). -/
noncomputable def hasseCasselsForm (v : NFPlace F) (Q : QuadForm F n) : ℤ := v.hasseCassels (diagOf Q)

/-- Lam's $s_v(Q)$ of an arbitrary nondegenerate form (= Serre's $\varepsilon_v$). -/
noncomputable def hasseLamForm (v : NFPlace F) (Q : QuadForm F n) : ℤ := v.hasseLam (diagOf Q)

/-- **The negative index of an arbitrary nondegenerate form $Q$ over $F$ at a place $v$:** `negIndex v a` for any
diagonalization $Q \cong \langle a\rangle$ over $F$ (the negative index of inertia over $F_w \cong \mathbb{R}$ at a real
place $w$, $0$ elsewhere; independent of the choice by Sylvester's law: `negIndexForm_eq_of_isometric`). -/
@[kb "omeara1963" "§61A, p. 155 (negative index ind⁻V)"]
noncomputable def negIndexForm (v : NFPlace F) (Q : QuadForm F n) : ℕ := v.negIndex (diagOf Q)

/-- Two diagonalizations over $F$ of the same form are isometric over every $F_v$. Internal. -/
theorem atPlace_isometric_diagOf (v : NFPlace F) {Q : QuadForm F n} (hQ : Q.Nondegenerate) {a : Fin n → F}
    (hiso : Q.IsometricIn F (QuadForm.diag a)) :
    v.atPlace fun K _ _ => (QuadForm.diag a).IsometricIn K (QuadForm.diag (diagOf Q)) :=
  atPlace_isometricIn_of_base v (isometricIn_trans F (isometricIn_symm F hiso) (isometricIn_diagOf hQ))

/-- **$\varepsilon_v(Q)$ does not depend on the diagonalization:** for every $a$ with $a_i \ne 0$ and
$Q \cong \langle a\rangle$ over $F$, `hasseSerreForm v Q` $= \prod_{i<j}(a_i,a_j)_v$. -/
theorem hasseSerreForm_eq_of_isometric (v : NFPlace F) {Q : QuadForm F n} (hQ : Q.Nondegenerate) {a : Fin n → F}
    (ha : ∀ i, a i ≠ 0) (hiso : Q.IsometricIn F (QuadForm.diag a)) : v.hasseSerreForm Q = v.hasseSerre a :=
  (hasseSerre_isometric v a _ ha (diagOf_ne_zero hQ) (atPlace_isometric_diagOf v hQ hiso)).symm

/-- **The negative index does not depend on the diagonalization** (Sylvester's law of inertia at real places). -/
theorem negIndexForm_eq_of_isometric (v : NFPlace F) {Q : QuadForm F n} (hQ : Q.Nondegenerate) {a : Fin n → F}
    (ha : ∀ i, a i ≠ 0) (hiso : Q.IsometricIn F (QuadForm.diag a)) : v.negIndexForm Q = v.negIndex a :=
  ((isometric_iff v a _ ha (diagOf_ne_zero hQ)).mp (atPlace_isometric_diagOf v hQ hiso)).2.2.symm

/-- **$S_v(Q)$ does not depend on the diagonalization.** -/
@[kb "omeara1963" "§63B, p. 167 (independent of the splitting)"]
theorem hasseOMearaForm_eq_of_isometric (v : NFPlace F) {Q : QuadForm F n} (hQ : Q.Nondegenerate) {a : Fin n → F}
    (ha : ∀ i, a i ≠ 0) (hiso : Q.IsometricIn F (QuadForm.diag a)) : v.hasseOMearaForm Q = v.hasseOMeara a :=
  ((isometric_iff_hasseOMeara v a _ ha (diagOf_ne_zero hQ)).mp (atPlace_isometric_diagOf v hQ hiso)).2.1.symm

/-- **$\alpha_v(Q)$ does not depend on the diagonalization.** -/
theorem hasseShimuraForm_eq_of_isometric (v : NFPlace F) {Q : QuadForm F n} (hQ : Q.Nondegenerate)
    {a : Fin n → F} (ha : ∀ i, a i ≠ 0) (hiso : Q.IsometricIn F (QuadForm.diag a)) :
    v.hasseShimuraForm Q = v.hasseShimura a :=
  hasseOMearaForm_eq_of_isometric v hQ ha hiso

/-- **$c_v(Q)$ does not depend on the diagonalization.** -/
theorem hasseCasselsForm_eq_of_isometric (v : NFPlace F) {Q : QuadForm F n} (hQ : Q.Nondegenerate)
    {a : Fin n → F} (ha : ∀ i, a i ≠ 0) (hiso : Q.IsometricIn F (QuadForm.diag a)) :
    v.hasseCasselsForm Q = v.hasseCassels a :=
  hasseSerreForm_eq_of_isometric v hQ ha hiso

/-- **$s_v(Q)$ does not depend on the diagonalization.** -/
theorem hasseLamForm_eq_of_isometric (v : NFPlace F) {Q : QuadForm F n} (hQ : Q.Nondegenerate) {a : Fin n → F}
    (ha : ∀ i, a i ≠ 0) (hiso : Q.IsometricIn F (QuadForm.diag a)) : v.hasseLamForm Q = v.hasseLam a :=
  hasseSerreForm_eq_of_isometric v hQ ha hiso

/-- **Consistency (Hasse invariant):** for $Q = \langle a\rangle$, $\varepsilon_v(Q) = \prod_{i<j}(a_i,a_j)_v$. -/
theorem hasseSerreForm_diag (v : NFPlace F) (a : Fin n → F) (ha : ∀ i, a i ≠ 0) :
    v.hasseSerreForm (QuadForm.diag a) = v.hasseSerre a :=
  hasseSerreForm_eq_of_isometric v (nondegenerate_diag ha) ha (isometricIn_refl F _)

/-- **Consistency (O'Meara's Hasse symbol):** for $Q = \langle a\rangle$, $S_v(Q) = \prod_{i \le j}(a_i,a_j)_v$. -/
theorem hasseOMearaForm_diag (v : NFPlace F) (a : Fin n → F) (ha : ∀ i, a i ≠ 0) :
    v.hasseOMearaForm (QuadForm.diag a) = v.hasseOMeara a :=
  hasseOMearaForm_eq_of_isometric v (nondegenerate_diag ha) ha (isometricIn_refl F _)

/-- **Consistency (negative index):** for $Q = \langle a\rangle$, the negative index is `negIndex v a`. -/
theorem negIndexForm_diag (v : NFPlace F) (a : Fin n → F) (ha : ∀ i, a i ≠ 0) :
    v.negIndexForm (QuadForm.diag a) = v.negIndex a :=
  negIndexForm_eq_of_isometric v (nondegenerate_diag ha) ha (isometricIn_refl F _)

/-! ### The classification -/

/-- Reduction of the general classification to the chosen diagonalizations. Internal. -/
theorem isometric_iff_diagOf (v : NFPlace F) {Q R : QuadForm F n} (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) :
    v.atPlace (fun K _ _ => Q.IsometricIn K R) ↔
      v.atPlace (fun K _ _ => (QuadForm.diag (diagOf Q)).IsometricIn K (QuadForm.diag (diagOf R))) :=
  atPlace_isometricIn_iff_of_base v (isometricIn_diagOf hQ) (isometricIn_diagOf hR)

/-- **Classification of nondegenerate quadratic forms over every completion of a number field** (O'Meara 63:20;
Serre IV §2.3, Thm. 7, there over $\mathbb{Q}_p$; Sylvester's law at the real places): for a place $v$ of $F$ (real,
complex, or finite including dyadic) and nondegenerate $Q, R$ in $n$ variables over $F$,
$$Q \cong R \text{ over } F_v \iff \frac{\det H_Q}{\det H_R} \in (F_v^\times)^2,\quad
\varepsilon_v(Q) = \varepsilon_v(R),\quad \text{and the negative indices at } v \text{ agree},$$
with $H$ the Hessian, $\varepsilon_v$ Serre's Hasse invariant of any diagonalization over $F$ (`hasseSerreForm`), and
the negative index `negIndexForm`.

Relation to O'Meara 63:20 (p. 170): a generalization. O'Meara treats only a local field at a discrete spot and
states the criterion as $\dim U = \dim V$, $dU = dV$, $S_{\mathfrak p}U = S_{\mathfrak p}V$; here the dimension is fixed
by $n$, the discriminant condition is the square class of the ratio of Hessian determinants, Serre's $\varepsilon_v$
replaces $S_{\mathfrak p}$ (equivalent once the discriminants agree, since $S = \varepsilon\cdot(d,-1)$), and the real
and complex places (Sylvester) are included. -/
@[kb "omeara1963" "§63C, 63:20, p. 170 (generalization: all places; Serre ε for S_p)"]
theorem isometric_iff_general (v : NFPlace F) (Q R : QuadForm F n) (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) :
    v.atPlace (fun K _ _ => Q.IsometricIn K R) ↔
      v.atPlace (fun K _ _ => IsSquare (algebraMap F K (Q.hessian.det / R.hessian.det))) ∧
        v.hasseSerreForm Q = v.hasseSerreForm R ∧ v.negIndexForm Q = v.negIndexForm R := by
  rw [isometric_iff_diagOf v hQ hR, atPlace_isSquare_iff_diagOf v hQ hR]
  exact isometric_iff v _ _ (diagOf_ne_zero hQ) (diagOf_ne_zero hR)

/-- **The general classification with O'Meara's Hasse symbol $S_v$** (O'Meara 63:20, p. 170, stated there with $S_{\mathfrak p}$
at the discrete spots only; the real and complex places are added here). -/
@[kb "omeara1963" "§63C, 63:20, p. 170 (same, with S_p; extended to all places)"]
theorem isometric_iff_general_hasseOMeara (v : NFPlace F) (Q R : QuadForm F n) (hQ : Q.Nondegenerate)
    (hR : R.Nondegenerate) :
    v.atPlace (fun K _ _ => Q.IsometricIn K R) ↔
      v.atPlace (fun K _ _ => IsSquare (algebraMap F K (Q.hessian.det / R.hessian.det))) ∧
        v.hasseOMearaForm Q = v.hasseOMearaForm R ∧ v.negIndexForm Q = v.negIndexForm R := by
  rw [isometric_iff_diagOf v hQ hR, atPlace_isSquare_iff_diagOf v hQ hR]
  exact isometric_iff_hasseOMeara v _ _ (diagOf_ne_zero hQ) (diagOf_ne_zero hR)

/-- **The general classification with Hasse's $\alpha_v$ (Shimura §28.13).** -/
@[kb "shimura2010" "§28.13, p. 160 (classification: derived)"]
theorem isometric_iff_general_hasseShimura (v : NFPlace F) (Q R : QuadForm F n) (hQ : Q.Nondegenerate)
    (hR : R.Nondegenerate) :
    v.atPlace (fun K _ _ => Q.IsometricIn K R) ↔
      v.atPlace (fun K _ _ => IsSquare (algebraMap F K (Q.hessian.det / R.hessian.det))) ∧
        v.hasseShimuraForm Q = v.hasseShimuraForm R ∧ v.negIndexForm Q = v.negIndexForm R :=
  isometric_iff_general_hasseOMeara v Q R hQ hR

/-- **The general classification with Cassels' $c_v$.** -/
@[kb "cassels1978" "Ch. 4, Thm. 1.1, p. 55, and Thm. 1.2, p. 56 (over ℚ_p and ℝ; over F_v derived)"]
theorem isometric_iff_general_hasseCassels (v : NFPlace F) (Q R : QuadForm F n) (hQ : Q.Nondegenerate)
    (hR : R.Nondegenerate) :
    v.atPlace (fun K _ _ => Q.IsometricIn K R) ↔
      v.atPlace (fun K _ _ => IsSquare (algebraMap F K (Q.hessian.det / R.hessian.det))) ∧
        v.hasseCasselsForm Q = v.hasseCasselsForm R ∧ v.negIndexForm Q = v.negIndexForm R :=
  isometric_iff_general v Q R hQ hR

/-- **The general classification with Lam's $s_v$** (Lam VI.2). -/
@[kb "lam2005" "Ch. VI, §2 [unverified]"]
theorem isometric_iff_general_hasseLam (v : NFPlace F) (Q R : QuadForm F n) (hQ : Q.Nondegenerate)
    (hR : R.Nondegenerate) :
    v.atPlace (fun K _ _ => Q.IsometricIn K R) ↔
      v.atPlace (fun K _ _ => IsSquare (algebraMap F K (Q.hessian.det / R.hessian.det))) ∧
        v.hasseLamForm Q = v.hasseLamForm R ∧ v.negIndexForm Q = v.negIndexForm R :=
  isometric_iff_general v Q R hQ hR

end NFPlace

namespace LocalClassNF

variable {F : Type} [Field F] [NumberField F]

/-- **Classification of nondegenerate quadratic forms over $F_{\mathfrak p}$, at every finite place of a number field,
dyadic included** (O'Meara 63:20; Serre IV §2.3, Thm. 7, there over $\mathbb{Q}_p$): $Q \cong R$ over $F_{\mathfrak p}$
iff $\det H_Q / \det H_R$ is a square in $F_{\mathfrak p}$ and $\varepsilon_{\mathfrak p}(Q) = \varepsilon_{\mathfrak p}(R)$.

Relation to O'Meara 63:20 (p. 170): the same statement for the completions of a number field (O'Meara's local fields
also include completions of function fields), with Serre's $\varepsilon_{\mathfrak p}$ in place of O'Meara's $S_{\mathfrak p}$ (equivalent once the discriminants
agree). -/
@[kb "omeara1963" "§63C, 63:20, p. 170 (number-field completions; Serre ε for S_p)"]
theorem isometric_finite_iff_general (v : HeightOneSpectrum (𝓞 F)) (Q R : QuadForm F n) (hQ : Q.Nondegenerate)
    (hR : R.Nondegenerate) :
    Q.IsometricIn (v.adicCompletion F) R ↔
      IsSquare (algebraMap F (v.adicCompletion F) (Q.hessian.det / R.hessian.det)) ∧
        (NFPlace.finite v).hasseSerreForm Q = (NFPlace.finite v).hasseSerreForm R := by
  have h := NFPlace.isometric_iff_general (NFPlace.finite v) Q R hQ hR
  simp only [NFPlace.atPlace] at h
  rw [h]
  exact ⟨fun ⟨a, b, _⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b, rfl⟩⟩

/-- **The negative index of inertia of a nondegenerate form $Q$ over $F$ at a real place $w$:** the number of negative
entries of a diagonalization of $Q$ over $F$ under the real embedding of $w$ (independent of the choice: Sylvester's
law, `NFPlace.negIndexForm_eq_of_isometric`). -/
@[kb "omeara1963" "§61A, p. 155 (negative index ind⁻V)"]
noncomputable def realNegIndex (w : InfinitePlace F) (hw : w.IsReal) (Q : QuadForm F n) : ℕ :=
  realNegCount w hw (diagOf Q)

/-- **Classification of nondegenerate quadratic forms over $F_w$ at a real place $w$ of a number field** (Sylvester's
law of inertia and its converse; Serre IV §2.4 over $\mathbb{R}$ [unverified locator]): $Q \cong R$ over
$F_w \cong \mathbb{R}$ iff they have the same negative index of inertia. -/
@[kb "serre1973" "Ch. IV, §2.4 [unverified]; omeara1963 §61A, 61:1, p. 156 (isometry part)"]
theorem isometric_real_iff_general (w : InfinitePlace F) (hw : w.IsReal) (Q R : QuadForm F n)
    (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) :
    Q.IsometricIn w.Completion R ↔ realNegIndex w hw Q = realNegIndex w hw R := by
  have h := NFPlace.isometric_iff_diagOf (NFPlace.infinite w) hQ hR
  simp only [NFPlace.atPlace] at h
  rw [h]
  exact isometric_real_iff w hw _ _ (diagOf_ne_zero hQ) (diagOf_ne_zero hR)

/-- **The real negative index does not depend on the diagonalization** (Sylvester's law of inertia). -/
theorem realNegIndex_eq_of_isometric (w : InfinitePlace F) (hw : w.IsReal) {Q : QuadForm F n}
    (hQ : Q.Nondegenerate) {a : Fin n → F} (ha : ∀ i, a i ≠ 0) (hiso : Q.IsometricIn F (QuadForm.diag a)) :
    realNegIndex w hw Q = realNegCount w hw a := by
  have := NFPlace.negIndexForm_eq_of_isometric (NFPlace.infinite w) hQ ha hiso
  simpa only [realNegIndex, NFPlace.negIndexForm, NFPlace.negIndex, hw, ↓reduceDIte] using this

/-- **Over $F_w$ at a complex place $w$ of a number field, nondegenerate forms of the same dimension are isometric**
(Lam II.3 [unverified locator]). -/
@[kb "lam2005" "Ch. II, §3 [unverified]; omeara1963 §61B, p. 156 (complex case)"]
theorem isometric_complex_general (w : InfinitePlace F) (hw : w.IsComplex) (Q R : QuadForm F n)
    (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) : Q.IsometricIn w.Completion R := by
  have h := NFPlace.isometric_iff_diagOf (NFPlace.infinite w) hQ hR
  simp only [NFPlace.atPlace] at h
  exact h.mpr (isometric_complex w hw _ _ (diagOf_ne_zero hQ) (diagOf_ne_zero hR))

end LocalClassNF

end QuadFormsKB
