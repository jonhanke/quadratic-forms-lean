/-
# Quaternion algebras $(a,b)_K$: reduced norm, norm forms, local structure

The foundation for Weil's base case $\tau(SO_3) = 2$ (Weil, *Adeles and Algebraic Groups*, 1982,
§3.7(a), p. 63): the special orthogonal group of a ternary form is the projective group
$D^\times/F^\times$ of a quaternion algebra $D$ (`Tamagawa/QuaternionSO3.lean`).

**The algebra.** For a field $K$ and $a, b \in K$ we use Mathlib's
`QuaternionAlgebra K a 0 b`, written `ℍ[K,a,b]`: the $K$-algebra with basis $1, i, j, k$ and
$$i^2 = a, \qquad j^2 = b, \qquad ij = -ji = k$$
(Mathlib's three-parameter algebra `ℍ[K,c₁,c₂,c₃]` with $c_1 = a$, $c_2 = 0$, $c_3 = b$). An element is
$x = x_0 + x_1 i + x_2 j + x_3 k$ with coordinates `x.re, x.imI, x.imJ, x.imK` (0-based: $x_0, \dots, x_3$).

**Contents.**
* `Quat.nrd`: the reduced norm $\operatorname{nrd}(x) = x\bar x = x_0^2 - a x_1^2 - b x_2^2 + ab\, x_3^2$
  (`Quat.mul_star_eq_nrd`), multiplicative (`Quat.nrd_mul`); $x$ is a unit iff $\operatorname{nrd}(x) \ne 0$
  (`Quat.isUnit_iff_nrd_ne_zero`).
* `Quat.nrdForm`: the quaternary norm form $\langle 1, -a, -b, ab \rangle$ as a `QuadForm`, with
  `Quat.evalIn_nrdForm` (its value at the coordinates of $x$ over any $F$-algebra field $K$ is
  $\operatorname{nrd}(x)$ in $(a,b)_K$) and the Mathlib bridge `Quat.toQuadraticForm_nrdForm_apply`.
* `Quat.pureForm`: the ternary form $\langle -a, -b, ab \rangle$, the restriction of $\operatorname{nrd}$ to the
  trace-zero (pure) quaternions $D^0 = K i + K j + K k$ (`Quat.nrd_pure`).
* Local structure: $(a,b)_K = 1$ iff $\operatorname{nrd}$ is isotropic (`Quat.hilbertSymbol_eq_one_iff_exists_nrd_eq_zero`),
  iff $(a,b)_K \cong M_2(K)$ (`Quat.nonempty_algEquiv_matrix_iff`); $(a,b)_K = -1$ iff $(a,b)_K$ is a
  division algebra (`Quat.hilbertSymbol_eq_neg_one_iff_division`).
* Over a number field: the ramified places (where $D_v$ is a division algebra) are exactly the places
  with $(a,b)_v = -1$ (`Quat.isRamifiedAt_iff`), a finite set of even size (`Quat.ramified_finite_even`),
  by Hilbert reciprocity.

Sources: Voight, *Quaternion Algebras* (2021), Ch. 2–5 and 14; Vignéras, *Arithmétique des algèbres de
quaternions* (1980), Ch. I–III; Weil 1982, §3.7(a).
-/
import QuadFormsKB.Equiv.Hilbert
import QuadFormsKB.Equiv.Mathlib
import QuadFormsKB.Witt.Represents
import QuadFormsKB.Literature.LocalGlobal.NumberFieldMain

open Quaternion

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

noncomputable section

namespace QuadFormsKB.Quat

section Basic

variable {K : Type*} [Field K] {a b : K}

/-- **The reduced norm** of $x = x_0 + x_1 i + x_2 j + x_3 k$ in the quaternion algebra
$(a,b)_K$ = `ℍ[K,a,b]` ($i^2 = a$, $j^2 = b$, $ij = -ji = k$):
$$\operatorname{nrd}(x) = x_0^2 - a\, x_1^2 - b\, x_2^2 + ab\, x_3^2 = x \bar x,$$
where $\bar x = x_0 - x_1 i - x_2 j - x_3 k$ is the standard involution (Mathlib's `star`); see
`mul_star_eq_nrd`. (Mathlib defines `normSq` only for Hamilton's $\mathbb{H}[R] = (-1,-1)_R$.)
Coordinates are 0-based: `x.re` $= x_0$, `x.imI` $= x_1$, `x.imJ` $= x_2$, `x.imK` $= x_3$.

Source: Voight 2021, §3.3 (Def. 3.3.1 and (3.3.2)); Vignéras 1980, Ch. I, §1. -/
@[kb "voight2021" "§3.3, (3.3.2)"]
def nrd (x : ℍ[K,a,b]) : K :=
  x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2

theorem nrd_mk (x₀ x₁ x₂ x₃ : K) :
    nrd (⟨x₀, x₁, x₂, x₃⟩ : ℍ[K,a,b]) = x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 := rfl

/-- **$x \bar x = \operatorname{nrd}(x)$** (as a scalar in $(a,b)_K$). -/
@[kb "voight2021" "§3.3"]
theorem mul_star_eq_nrd (x : ℍ[K,a,b]) : x * star x = ((nrd x : K) : ℍ[K,a,b]) := by
  ext <;> simp only [QuaternionAlgebra.re_coe, QuaternionAlgebra.imI_coe, QuaternionAlgebra.imJ_coe,
    QuaternionAlgebra.imK_coe] <;> simp [nrd] <;> ring

/-- **$\bar x x = \operatorname{nrd}(x)$.** -/
theorem star_mul_eq_nrd (x : ℍ[K,a,b]) : star x * x = ((nrd x : K) : ℍ[K,a,b]) := by
  ext <;> simp only [QuaternionAlgebra.re_coe, QuaternionAlgebra.imI_coe, QuaternionAlgebra.imJ_coe,
    QuaternionAlgebra.imK_coe] <;> simp [nrd] <;> ring

/-- **The reduced norm is multiplicative:** $\operatorname{nrd}(xy) = \operatorname{nrd}(x)\operatorname{nrd}(y)$. -/
@[kb "voight2021" "Lemma 3.3.4"]
theorem nrd_mul (x y : ℍ[K,a,b]) : nrd (x * y) = nrd x * nrd y := by
  simp only [nrd, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul]
  ring

@[simp] theorem nrd_one : nrd (1 : ℍ[K,a,b]) = 1 := by simp [nrd]

@[simp] theorem nrd_coe (r : K) : nrd (r : ℍ[K,a,b]) = r ^ 2 := by simp [nrd]

theorem nrd_star (x : ℍ[K,a,b]) : nrd (star x) = nrd x := by simp [nrd]

theorem nrd_smul (r : K) (x : ℍ[K,a,b]) : nrd (r • x) = r ^ 2 * nrd x := by
  simp [nrd]; ring

/-- **Units are the elements of nonzero reduced norm:** $x \in ((a,b)_K)^\times \iff \operatorname{nrd}(x) \ne 0$,
with $x^{-1} = \operatorname{nrd}(x)^{-1} \bar x$. -/
@[kb "voight2021" "Lemma 3.3.5"]
theorem isUnit_iff_nrd_ne_zero (x : ℍ[K,a,b]) : IsUnit x ↔ nrd x ≠ 0 := by
  constructor
  · rintro ⟨u, rfl⟩ h
    have := congrArg nrd u.mul_inv
    rw [nrd_mul, h, zero_mul, nrd_one] at this
    exact zero_ne_one this
  · intro h
    refine ⟨⟨x, ((nrd x)⁻¹ : K) • star x, ?_, ?_⟩, rfl⟩
    · rw [mul_smul_comm, mul_star_eq_nrd, ← QuaternionAlgebra.coe_smul, smul_eq_mul, inv_mul_cancel₀ h]
      rfl
    · rw [smul_mul_assoc, star_mul_eq_nrd, ← QuaternionAlgebra.coe_smul, smul_eq_mul, inv_mul_cancel₀ h]
      rfl

/-- The inverse of a unit: $u^{-1} = \operatorname{nrd}(u)^{-1}\, \bar u$. -/
theorem inv_eq (u : (ℍ[K,a,b])ˣ) : ((u⁻¹ : (ℍ[K,a,b])ˣ) : ℍ[K,a,b]) = ((nrd (u : ℍ[K,a,b]))⁻¹ : K) • star (u : ℍ[K,a,b]) := by
  have hu : nrd (u : ℍ[K,a,b]) ≠ 0 := (isUnit_iff_nrd_ne_zero _).1 u.isUnit
  have h1 : (u : ℍ[K,a,b]) * (((nrd (u : ℍ[K,a,b]))⁻¹ : K) • star (u : ℍ[K,a,b])) = 1 := by
    rw [mul_smul_comm, mul_star_eq_nrd, ← QuaternionAlgebra.coe_smul, smul_eq_mul, inv_mul_cancel₀ hu]
    rfl
  calc ((u⁻¹ : (ℍ[K,a,b])ˣ) : ℍ[K,a,b]) = ((u⁻¹ : (ℍ[K,a,b])ˣ) : ℍ[K,a,b]) * ((u : ℍ[K,a,b]) *
        (((nrd (u : ℍ[K,a,b]))⁻¹ : K) • star (u : ℍ[K,a,b]))) := by rw [h1, mul_one]
    _ = _ := by rw [← mul_assoc, Units.inv_mul, one_mul]

theorem nrd_units_ne_zero (u : (ℍ[K,a,b])ˣ) : nrd (u : ℍ[K,a,b]) ≠ 0 :=
  (isUnit_iff_nrd_ne_zero _).1 u.isUnit

end Basic

/-! ### The norm forms as `QuadForm`s -/

section Forms

variable {F : Type*} [Field F]

/-- **The quaternary norm form** $\langle 1, -a, -b, ab \rangle$ of $(a,b)_F$:
$$\operatorname{nrd}(x_0, x_1, x_2, x_3) = x_0^2 - a\,x_1^2 - b\,x_2^2 + ab\,x_3^2,$$
as a `QuadForm F 4` (0-based coordinates $x_0, \dots, x_3$ along $1, i, j, k$). Its value at the
coordinate vector of $x \in (a,b)_K$ is $\operatorname{nrd}(x)$ (`evalIn_nrdForm`).

Source: Voight 2021, §5.2 (the norm form $\langle 1,-a,-b,ab\rangle$, Ex. 5.2.?) [unverified locator];
Weil 1982, §3.7(a). -/
@[kb "voight2021" "§5.2 [unverified]"]
def nrdForm (a b : F) : QuadForm F 4 := QuadForm.diag ![1, -a, -b, a * b]

/-- **The ternary norm form on the pure quaternions** $\langle -a, -b, ab \rangle$:
$$\operatorname{nrd}(x_1 i + x_2 j + x_3 k) = -a\,x_1^2 - b\,x_2^2 + ab\,x_3^2,$$
as a `QuadForm F 3`. Coordinates are 0-based: the variable $y_0, y_1, y_2$ here is the coefficient
of $i, j, k$ respectively (`nrd_pure`). This is $\operatorname{nrd}$ restricted to the trace-zero
subspace $D^0$; $-\operatorname{nrd}|_{D^0} = \langle a, b, -ab\rangle$ is the other common normalization
(Voight §5.2 uses $\operatorname{nrd}|_{D^0}$).

Source: Voight 2021, §5.2 [unverified locator]; Weil 1982, §3.7(a), p. 63. -/
@[kb "voight2021" "§5.2 [unverified]"]
def pureForm (a b : F) : QuadForm F 3 := QuadForm.diag ![-a, -b, a * b]

variable (K : Type*) [Field K] [Algebra F K]

/-- **Values of the quaternary norm form** over an $F$-algebra field $K$: at the coordinate vector
$v = (x_0, x_1, x_2, x_3) \in K^4$,
$$\langle 1,-a,-b,ab\rangle(v) = \operatorname{nrd}(x_0 + x_1 i + x_2 j + x_3 k),$$
the reduced norm in $(a,b)_K$ (with $a, b$ mapped to $K$). -/
@[kb "voight2021" "§5.2 [unverified]"]
theorem evalIn_nrdForm (a b : F) (v : Fin 4 → K) :
    (nrdForm a b).evalIn K v =
      nrd (⟨v 0, v 1, v 2, v 3⟩ : ℍ[K, algebraMap F K a, algebraMap F K b]) := by
  rw [nrdForm, QuadForm.evalIn_diag, Fin.sum_univ_four, nrd_mk]
  simp
  ring

/-- **Values of the ternary norm form** over an $F$-algebra field $K$: at $y = (y_0, y_1, y_2) \in K^3$,
$\langle -a, -b, ab\rangle(y) = \operatorname{nrd}(y_0 i + y_1 j + y_2 k)$ in $(a,b)_K$. -/
@[kb "voight2021" "§5.2 [unverified]"]
theorem evalIn_pureForm (a b : F) (y : Fin 3 → K) :
    (pureForm a b).evalIn K y =
      nrd (⟨0, y 0, y 1, y 2⟩ : ℍ[K, algebraMap F K a, algebraMap F K b]) := by
  rw [pureForm, QuadForm.evalIn_diag, Fin.sum_univ_three, nrd_mk]
  simp
  ring

/-- **The quaternary norm form contains the ternary one:** $\langle 1,-a,-b,ab\rangle = \langle 1\rangle \perp
\langle -a,-b,ab\rangle$ on values: $\operatorname{nrd}(x_0, y) = x_0^2 + \langle -a,-b,ab\rangle(y)$. -/
theorem evalIn_nrdForm_eq (a b : F) (v : Fin 4 → K) :
    (nrdForm a b).evalIn K v = v 0 ^ 2 + (pureForm a b).evalIn K ![v 1, v 2, v 3] := by
  rw [evalIn_nrdForm, evalIn_pureForm]
  simp [nrd_mk]; ring

/-- A diagonal form with entries $\ne 0$ is nondegenerate when $2 \ne 0$ (no `CharZero` needed). -/
theorem nondegenerate_diag_of_two {n : ℕ} (h2 : (2 : F) ≠ 0) {c : Fin n → F} (hc : ∀ i, c i ≠ 0) :
    (QuadForm.diag c).Nondegenerate := by
  unfold QuadForm.Nondegenerate QuadForm.hessian QuadForm.diag
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_add, Matrix.det_diagonal]
  rw [Finset.prod_ne_zero_iff]
  intro i _
  rw [← two_mul]
  exact mul_ne_zero h2 (hc i)

/-- **The norm form is nondegenerate** for $a, b \ne 0$ and $2 \ne 0$ in $F$. -/
@[kb "voight2021" "§5.2 [unverified]"]
theorem nrdForm_nondegenerate (h2 : (2 : F) ≠ 0) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    (nrdForm a b).Nondegenerate := by
  refine nondegenerate_diag_of_two h2 fun i => ?_
  fin_cases i <;> simp [ha, hb]

/-- **The ternary norm form is nondegenerate** for $a, b \ne 0$ and $2 \ne 0$ in $F$. -/
@[kb "voight2021" "§5.2 [unverified]"]
theorem pureForm_nondegenerate (h2 : (2 : F) ≠ 0) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    (pureForm a b).Nondegenerate := by
  refine nondegenerate_diag_of_two h2 fun i => ?_
  fin_cases i <;> simp [ha, hb]

/-- **Bridge to Mathlib** (`Equiv/Mathlib.lean`): the Mathlib quadratic form of
$\langle 1,-a,-b,ab\rangle$ is $\operatorname{nrd}$ read through Mathlib's coordinate equivalence
`QuaternionAlgebra.equivTuple` $\colon (a,b)_F \simeq F^4$. -/
@[kb "voight2021" "§5.2 [unverified]"]
theorem toQuadraticForm_nrdForm_apply (a b : F) (v : Fin 4 → F) :
    (nrdForm a b).toQuadraticForm v = nrd ((QuaternionAlgebra.equivTuple a 0 b).symm v) := by
  rw [QuadForm.toQuadraticForm_apply]
  have := evalIn_nrdForm F a b v
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at this
  rw [QuadForm.eval, this]
  rfl

end Forms

/-! ### Local structure: split or division, by the Hilbert symbol -/

section Local

variable {K : Type*} [Field K] {a b : K}

/-- **$(a,b)_K$ is split iff the Hilbert symbol is $1$:** for $a, b \in K^\times$ ($2 \ne 0$ in $K$),
$$(a,b)_K = 1 \iff \operatorname{nrd}(x) = 0 \text{ for some } x \ne 0 \text{ in } (a,b)_K,$$
i.e. iff the norm form $\langle 1,-a,-b,ab\rangle$ is isotropic over $K$ (equivalently iff $(a,b)_K$ has a
nonzero non-unit, `isUnit_iff_nrd_ne_zero`).

*Proof.* ($\Rightarrow$) From $a x^2 + b y^2 = 1$ (`hilbertSymbol_eq_one_iff_conic`), $\operatorname{nrd}(1 + x i + y j) = 0$.
($\Leftarrow$) Write $\operatorname{nrd}(r + si + tj + uk) = (r^2 - a s^2) - b(t^2 - a u^2) = 0$. If $w = t^2 - a u^2 \ne 0$,
multiplicativity of the norm form $X^2 - aY^2$ gives $(rt + asu)^2 = a(ru + st)^2 + b w^2$; if $w = 0$, then $a$ is a
square, from $r^2 = a s^2$ or $t^2 = a u^2$.

Source: Voight 2021, Thm. 5.4.4 and Prop. 5.4.? [unverified]; Serre 1973, Ch. III, §1.1. -/
@[kb "voight2021" "§5.4 [unverified]"]
theorem hilbertSymbol_eq_one_iff_exists_nrd_eq_zero (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSymbol K a b = 1 ↔ ∃ x : ℍ[K,a,b], x ≠ 0 ∧ nrd x = 0 := by
  constructor
  · intro h
    obtain ⟨x, y, hxy⟩ := (hilbertSymbol_eq_one_iff_conic K h2 ha hb).1 h
    refine ⟨⟨1, x, y, 0⟩, fun h0 => ?_, ?_⟩
    · have := congrArg QuaternionAlgebra.re h0
      simp at this
    · rw [nrd_mk]; linear_combination -hxy
  · rintro ⟨⟨r, s, t, u⟩, hne, hn⟩
    rw [nrd_mk] at hn
    unfold hilbertSymbol
    split_ifs with hcon
    · rfl
    exfalso
    apply hcon
    by_cases hw : t ^ 2 - a * u ^ 2 = 0
    · have hrs : r ^ 2 = a * s ^ 2 := by linear_combination hn + b * hw
      by_cases hs : s = 0
      · have hr : r = 0 := by
          have : r ^ 2 = 0 := by rw [hrs, hs]; ring
          exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
        by_cases hu : u = 0
        · exfalso
          have ht : t = 0 := by
            have : t ^ 2 = 0 := by linear_combination hw + a * u * hu
            exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
          apply hne
          rw [hr, hs, ht, hu]
          rfl
        · exact ⟨u, 0, t, by simp [hu], by linear_combination hw⟩
      · exact ⟨s, 0, r, by simp [hs], by linear_combination hrs⟩
    · exact ⟨r * u + s * t, t ^ 2 - a * u ^ 2, r * t + a * s * u, by simp [hw],
        by linear_combination (t ^ 2 - a * u ^ 2) * hn⟩

/-- **$(a,b)_K$ is a division algebra iff the Hilbert symbol is $-1$:** for $a, b \in K^\times$ ($2 \ne 0$ in $K$),
$$(a,b)_K = -1 \iff \text{every nonzero } x \in (a,b)_K \text{ is a unit}.$$

Source: Voight 2021, Thm. 5.4.4 [unverified]; Vignéras 1980, Ch. I, Cor. 1.? [unverified]. -/
@[kb "voight2021" "§5.4 [unverified]; omeara1963 §63B, p. 166; §57, 57:9"]
theorem hilbertSymbol_eq_neg_one_iff_division (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSymbol K a b = -1 ↔ ∀ x : ℍ[K,a,b], x ≠ 0 → IsUnit x := by
  have hpm : hilbertSymbol K a b = 1 ∨ hilbertSymbol K a b = -1 := by
    unfold hilbertSymbol; split_ifs <;> simp
  have key := hilbertSymbol_eq_one_iff_exists_nrd_eq_zero h2 ha hb
  constructor
  · intro h x hx
    rw [isUnit_iff_nrd_ne_zero]
    intro h0
    have := key.2 ⟨x, hx, h0⟩
    rw [h] at this
    norm_num at this
  · intro h
    rcases hpm with h1 | h1
    · obtain ⟨x, hx, h0⟩ := key.1 h1
      exact absurd h0 ((isUnit_iff_nrd_ne_zero x).1 (h x hx))
    · exact h1

/-- The basis of $M_2(K)$ realizing $(a,b)_K \cong M_2(K)$ from a solution of $a x^2 + b y^2 = 1$:
$$i \mapsto \begin{pmatrix} xa & yab \\ y & -xa \end{pmatrix}, \quad
j \mapsto \begin{pmatrix} yb & -xab \\ -x & -yb \end{pmatrix}, \quad
k \mapsto \begin{pmatrix} 0 & -ab \\ 1 & 0 \end{pmatrix}.$$ -/
def splitBasis (x y : K) (h : a * x ^ 2 + b * y ^ 2 = 1) :
    QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) K) a 0 b where
  i := !![x * a, y * a * b; y, -(x * a)]
  j := !![y * b, -(x * a * b); -x, -(y * b)]
  k := !![0, -(a * b); 1, 0]
  i_mul_i := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      (first | ring1 | linear_combination h | linear_combination -h | linear_combination a * h | linear_combination -a * h | linear_combination b * h | linear_combination -b * h | linear_combination (a * b) * h | linear_combination -(a * b) * h)
  j_mul_j := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      (first | ring1 | linear_combination h | linear_combination -h | linear_combination a * h | linear_combination -a * h | linear_combination b * h | linear_combination -b * h | linear_combination (a * b) * h | linear_combination -(a * b) * h)
  i_mul_j := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      (first | ring1 | linear_combination h | linear_combination -h | linear_combination a * h | linear_combination -a * h | linear_combination b * h | linear_combination -b * h | linear_combination (a * b) * h | linear_combination -(a * b) * h)
  j_mul_i := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      (first | ring1 | linear_combination h | linear_combination -h | linear_combination a * h | linear_combination -a * h | linear_combination b * h | linear_combination -b * h | linear_combination (a * b) * h | linear_combination -(a * b) * h)

/-- **Split quaternion algebras are matrix algebras:** if $(a,b)_K = 1$ ($a, b \in K^\times$, $2 \ne 0$), then
$(a,b)_K \cong M_2(K)$ as $K$-algebras. Explicitly, from $a x^2 + b y^2 = 1$ the elements of `splitBasis`
satisfy the quaternion relations, so `QuaternionAlgebra.Basis.liftHom` is a $K$-algebra map
$(a,b)_K \to M_2(K)$; it is surjective (explicit preimages) and both sides have dimension $4$.

Source: Voight 2021, Thm. 5.4.4 and Prop. 2.4.? [unverified]. -/
@[kb "voight2021" "§5.4 [unverified]"]
theorem nonempty_algEquiv_matrix_of_hilbertSymbol (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : hilbertSymbol K a b = 1) : Nonempty (ℍ[K,a,b] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨x, y, hxy⟩ := (hilbertSymbol_eq_one_iff_conic K h2 ha hb).1 h
  set φ := (splitBasis x y hxy).liftHom
  have hφ : ∀ q : ℍ[K,a,b], φ q = !![q.re + q.imI * (x * a) + q.imJ * (y * b),
      q.imI * (y * a * b) - q.imJ * (x * a * b) - q.imK * (a * b);
      q.imI * y - q.imJ * x + q.imK, q.re - q.imI * (x * a) - q.imJ * (y * b)] := by
    intro q
    simp only [φ, QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift, splitBasis]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.algebraMap_matrix_apply] <;> ring
  have hsurj : Function.Surjective φ := by
    intro M
    set p := (M 0 0 - M 1 1) / 2
    set q := (M 1 0 + M 0 1 / (a * b)) / 2
    refine ⟨⟨(M 0 0 + M 1 1) / 2, x * p + y * b * q, y * p - x * a * q, (M 1 0 - M 0 1 / (a * b)) / 2⟩, ?_⟩
    rw [hφ]
    ext i j; fin_cases i <;> fin_cases j <;> simp [p, q] <;> field_simp <;>
      (first | linear_combination (M 0 0 - M 1 1) * hxy | linear_combination (M 1 1 - M 0 0) * hxy | linear_combination (M 0 1 + a * b * M 1 0) * hxy | linear_combination -(M 0 1 + a * b * M 1 0) * hxy)
  have hrank : Module.finrank K ℍ[K,a,b] = Module.finrank K (Matrix (Fin 2) (Fin 2) K) := by
    rw [QuaternionAlgebra.finrank_eq_four, Module.finrank_matrix]; simp
  have hinj : Function.Injective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank (f := φ.toLinearMap)).2 hsurj
  exact ⟨AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

/-- **Local structure of a quaternion algebra:** for $a, b \in K^\times$ ($2 \ne 0$ in $K$),
$$(a,b)_K \cong M_2(K) \iff (a,b)_K = 1 \text{ (Hilbert symbol)},$$
and otherwise $(a,b)_K$ is a division algebra (`hilbertSymbol_eq_neg_one_iff_division`). Over a local field
$F_v$ this is the dichotomy "$D_v$ split or ramified" of Weil 1982, §3.7(a).

Source: Voight 2021, Thm. 5.4.4 [unverified]; Weil 1982, §3.7(a), p. 63. -/
@[kb "voight2021" "§5.4 [unverified]"]
theorem nonempty_algEquiv_matrix_iff (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nonempty (ℍ[K,a,b] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) ↔ hilbertSymbol K a b = 1 := by
  refine ⟨fun ⟨e⟩ => ?_, nonempty_algEquiv_matrix_of_hilbertSymbol h2 ha hb⟩
  refine (hilbertSymbol_eq_one_iff_exists_nrd_eq_zero h2 ha hb).2 ⟨e.symm (Matrix.single 0 0 1), ?_, ?_⟩
  · intro h0
    have := congrArg e h0
    rw [AlgEquiv.apply_symm_apply, map_zero] at this
    have := congrFun (congrFun this 0) 0
    simp at this
  · by_contra hn
    obtain ⟨u, hu⟩ := (isUnit_iff_nrd_ne_zero _).2 hn
    have hu' : IsUnit (Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : K)) := by
      have := u.isUnit.map e
      rwa [hu, AlgEquiv.apply_symm_apply] at this
    have := (Matrix.isUnit_iff_isUnit_det _).1 hu'
    simp [Matrix.det_fin_two] at this

end Local

/-! ### Over a number field: the ramified places -/

section NumberField

open NumberField

variable {F : Type} [Field F] [NumberField F]

theorem two_ne_zero_of_algebra (K : Type*) [Field K] [Algebra F K] : (2 : K) ≠ 0 := by
  rw [show (2 : K) = algebraMap F K 2 from (map_ofNat (algebraMap F K) 2).symm]
  exact (map_ne_zero _).2 two_ne_zero

/-- **$D = (a,b)_F$ is ramified at the place $v$:** the completion $D_v = (a,b)_{F_v}$ is a division
algebra, i.e. every nonzero element of $(a,b)_{F_v}$ (with $a, b$ viewed in $F_v$) is a unit. Otherwise
$D_v \cong M_2(F_v)$ (`isRamifiedAt_iff`, `nonempty_algEquiv_matrix_iff`).

Source: Voight 2021, Def. 14.1.? [unverified]; Weil 1982, §3.7(a). -/
@[kb "voight2021" "§14.1 [unverified]"]
def IsRamifiedAt (a b : F) (v : NFPlace F) : Prop :=
  v.atPlace fun K _ _ => ∀ x : ℍ[K, algebraMap F K a, algebraMap F K b], x ≠ 0 → IsUnit x

/-- **Ramification is read off from the Hilbert symbol:** for $a, b \in F^\times$, $D = (a,b)_F$ is ramified at $v$
iff $(a,b)_v = -1$. -/
@[kb "voight2021" "§14.1 [unverified]"]
theorem isRamifiedAt_iff {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (v : NFPlace F) :
    IsRamifiedAt a b v ↔ v.hilbert a b = -1 := by
  cases v with
  | infinite w =>
    exact (hilbertSymbol_eq_neg_one_iff_division (two_ne_zero_of_algebra (F := F) _)
      ((map_ne_zero _).2 ha) ((map_ne_zero _).2 hb)).symm
  | finite v =>
    exact (hilbertSymbol_eq_neg_one_iff_division (two_ne_zero_of_algebra (F := F) _)
      ((map_ne_zero _).2 ha) ((map_ne_zero _).2 hb)).symm

/-- **The ramified places of a quaternion algebra are finite in number, and even in number:** for
$a, b \in F^\times$, the set $\operatorname{Ram}(D)$ of places $v$ of $F$ (finite and infinite) at which
$D = (a,b)_F$ is ramified is finite and $\#\operatorname{Ram}(D)$ is even.

*Proof.* $\operatorname{Ram}(D) = \{v : (a,b)_v = -1\}$ (`isRamifiedAt_iff`); apply Hilbert reciprocity
`hilbert_reciprocity_nf` (proved by Weil's route, no class field theory).

Source: Voight 2021, Thm. 14.6.1 [unverified]; Vignéras 1980, Ch. III, Thm. 3.1 [unverified]. -/
@[kb "voight2021" "Thm. 14.6.1 [unverified]"]
theorem ramified_finite_even {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    {v : NFPlace F | IsRamifiedAt a b v}.Finite ∧ Even {v : NFPlace F | IsRamifiedAt a b v}.ncard := by
  have : {v : NFPlace F | IsRamifiedAt a b v} = {v : NFPlace F | v.hilbert a b = -1} := by
    ext v; exact isRamifiedAt_iff ha hb v
  rw [this]
  exact hilbert_reciprocity_nf a b ha hb

end NumberField

end QuadFormsKB.Quat
