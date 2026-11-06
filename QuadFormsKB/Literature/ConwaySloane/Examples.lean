/-
# Conway–Sloane, Ch. 15, §10.1 and §11: Minkowski reduction for ternary forms and the worked examples

**Source.** J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §10.1
(pp. 395–397, inequalities (45)–(49), Table 15.6, p. 398) and §11 (pp. 403–405, matrix (50), forms (51))
(`conwaysloane1999`; printed page = PDF page of the chapter file + 351).

**Conventions.** A ternary form is the Gram matrix $\begin{pmatrix} a & b & h\\ b & c & f\\ h & f & g\end{pmatrix}$
(the book's table entry "$a_b\,c_f\,g_h$", with $h$ omitted when $0$); `Tern` has the six fields `a b c f g h`.
The book's $a_{11}, a_{22}, a_{33}, a_{12}, a_{23}, a_{13}$ are `a c g b f h` (0-based: $a_{00}, a_{11}, a_{22}, a_{01},
a_{12}, a_{02}$).

**Defines**
* `Tern`, `Tern.mat`, `Tern.det`;
* `Tern.IsReducedPrinted`: the inequalities (46), (47), (48) *exactly as printed* (with absolute values);
* `Tern.IsMinkowski`: (46), (47) and the *four one-sided* inequalities that (48) really encodes.

**Proves**
* `Tern.isMinkowskiReduced_iff`: for a ternary integral form, the library's `Reduction.IsMinkowskiReduced`
  (Cassels, Ch. 12; condition (45) of the book) holds iff `Tern.IsMinkowski` (via Cassels' Lemma 1.2,
  `Reduction.lemma_1_2`, which is Minkowski's theorem quoted on p. 397);
* `Tern.IsReducedPrinted.isMinkowski`, `not_isReducedPrinted_of_isMinkowski`: the printed (48) is strictly stronger than
  Minkowski reduction (**erratum**, below);
* (50): the matrix $M$ transforms the first Dickson–Ross form into the second (`dicksonRoss_equiv`); the library's
  `Siegel.ex2_properIntEquiv` (Cassels, Ch. 11, Ex. 2) is the same statement for another matrix;
* (51): both forms have determinant $-128$, and (a) is equivalent to $\mathrm{diag}(-1, 64, 2)$ (`form51_det`,
  `form51a_equiv_diag`);
* Table 15.6: each listed form has the listed determinant, is positive definite and satisfies the printed
  (46)–(48) after reordering/changing signs of the basis vectors (`table156_correct`, by `decide +kernel`; the table lists
  forms with $h = 0$ where possible, e.g. $2_1\,7_1\,2$ has $c > g$, so not in the order (46)). All 100 or so entries
  agree with the printed determinants. Also (50) as a polynomial identity (`dicksonRoss_poly`) and (51b) as the Gram
  matrix of the rational basis $3e_0, e_1/3, e_2$ of (51a) (`form51b_rational_basis`).

**Not formalized.** (49) (the quaternary inequalities); that Table 15.6 lists *all* indecomposable reduced forms and
only those (completeness and indecomposability); Table 15.7 (indefinite forms, by spinor genera).

**Erratum.** (48) is printed as $2\lvert a_{rs} \pm a_{rt} \pm a_{st}\rvert
\le a_{rr} + a_{ss}$. The derivation (the vectors $v = e_t - \sum \epsilon_s e_s$, $\epsilon_s = \pm1$) gives, for
$S = \{r, s\}$, only the four *one-sided* inequalities $a_{rr} + a_{ss} + 2(\epsilon_r\epsilon_s a_{rs} - \epsilon_r a_{rt}
- \epsilon_s a_{st}) \ge 0$: the absolute value is justified in (47) ($S = \{s\}$) but not in (48) (nor in (49)). The form
with Gram matrix $\begin{pmatrix} 2&1&1\\1&2&1\\1&1&2\end{pmatrix}$ is Minkowski reduced but violates the printed (48)
(`counterexample_printed48`). The printed system therefore describes a subset of the reduced forms (still containing a
representative of every class up to changing signs of the basis vectors, which is how the table is used).
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Cassels.Ch12.LemmaOneTwo

namespace QuadFormsKB
namespace ConwaySloane
namespace Examples

open Matrix

/-- **A ternary integral form by its Gram matrix** $\begin{pmatrix} a & b & h\\ b & c & f\\ h & f & g\end{pmatrix}$
(the book's table entry $a_b\,c_f\,g_h$, Conway–Sloane, §10.1, p. 397). -/
@[kb "conwaysloane1999" "Ch. 15, §10.1, p. 397 (notation of Tables 15.6, 15.7)"]
structure Tern where
  /-- The entry $a_{00}$. -/
  a : ℤ
  /-- The entry $a_{01} = a_{10}$. -/
  b : ℤ
  /-- The entry $a_{11}$. -/
  c : ℤ
  /-- The entry $a_{12} = a_{21}$. -/
  f : ℤ
  /-- The entry $a_{22}$. -/
  g : ℤ
  /-- The entry $a_{02} = a_{20}$ (omitted from the book's tables when $0$). -/
  h : ℤ
  deriving DecidableEq, Repr

/-- The Gram matrix. -/
def Tern.mat (t : Tern) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![t.a, t.b, t.h; t.b, t.c, t.f; t.h, t.f, t.g]

/-- The determinant (as an explicit polynomial, so that it can be evaluated by `decide`). -/
def Tern.det (t : Tern) : ℤ :=
  t.a * (t.c * t.g - t.f ^ 2) - t.b * (t.b * t.g - t.f * t.h) + t.h * (t.b * t.f - t.c * t.h)

theorem Tern.det_mat (t : Tern) : t.mat.det = t.det := by
  simp [Tern.mat, Matrix.det_fin_three, Tern.det]
  ring

/-- **Inequalities (46), (47), (48) as printed** (Conway–Sloane, §10.1, pp. 396–397), for $n = 3$ with
$a_{11}, a_{22}, a_{33}, a_{12}, a_{23}, a_{13} = a, c, g, b, f, h$:
(46) $0 < a \le c \le g$; (47) $2\lvert a_{st}\rvert \le a_{ss}$ ($s < t$), i.e. $2\lvert b\rvert \le a$, $2\lvert h\rvert \le a$,
$2\lvert f\rvert \le c$; (48) $2\lvert b \pm h \pm f\rvert \le a + c$ (all four sign choices).
See the module docstring: (48) with absolute values is stronger than Minkowski reduction. -/
@[kb "conwaysloane1999" "Ch. 15, §10.1, (46)–(48), pp. 396–397"]
def Tern.IsReducedPrinted (t : Tern) : Prop :=
  0 < t.a ∧ t.a ≤ t.c ∧ t.c ≤ t.g ∧
  2 * |t.b| ≤ t.a ∧ 2 * |t.h| ≤ t.a ∧ 2 * |t.f| ≤ t.c ∧
  2 * |t.b + t.h + t.f| ≤ t.a + t.c ∧ 2 * |t.b + t.h - t.f| ≤ t.a + t.c ∧
  2 * |t.b - t.h + t.f| ≤ t.a + t.c ∧ 2 * |t.b - t.h - t.f| ≤ t.a + t.c

/-- **Minkowski reduction for ternary forms in the book's inequalities, one-sided form of (48):** (46), (47) and
$a + c + 2(\epsilon_r\epsilon_s b - \epsilon_r h' \dots) \ge 0$ for the four sign patterns, i.e. $f(x e_0 + y e_1 + e_2)
\ge f(e_2)$ for $x, y = \pm1$. -/
@[kb "conwaysloane1999" "Ch. 15, §10.1, (46)–(48), pp. 396–397 (one-sided form of (48))"]
def Tern.IsMinkowski (t : Tern) : Prop :=
  0 < t.a ∧ t.a ≤ t.c ∧ t.c ≤ t.g ∧
  2 * |t.b| ≤ t.a ∧ 2 * |t.h| ≤ t.a ∧ 2 * |t.f| ≤ t.c ∧
  0 ≤ t.a + t.c + 2 * (t.b + t.h + t.f) ∧ 0 ≤ t.a + t.c + 2 * (-t.b + t.h - t.f) ∧
  0 ≤ t.a + t.c + 2 * (-t.b - t.h + t.f) ∧ 0 ≤ t.a + t.c + 2 * (t.b - t.h - t.f)

instance (t : Tern) : Decidable t.IsReducedPrinted := by unfold Tern.IsReducedPrinted; infer_instance
instance (t : Tern) : Decidable t.IsMinkowski := by unfold Tern.IsMinkowski; infer_instance

/-- The printed (48) implies the one-sided form. -/
theorem Tern.IsReducedPrinted.isMinkowski {t : Tern} (h : t.IsReducedPrinted) : t.IsMinkowski := by
  unfold Tern.IsReducedPrinted at h
  unfold Tern.IsMinkowski
  simp only [Int.abs_eq_natAbs] at h ⊢
  omega

/-- **Erratum:** the form with Gram matrix $\begin{pmatrix} 2&1&1\\1&2&1\\1&1&2\end{pmatrix}$ ($a_1\,c_1\,g_1$ with $h = 1$)
satisfies the one-sided inequalities but violates (48) as printed ($2\lvert 1 + 1 + 1\rvert = 6 > 4$). -/
@[kb "conwaysloane1999" "Ch. 15, §10.1, (48), p. 397 (printed absolute value too strong)"]
theorem counterexample_printed48 :
    (⟨2, 1, 2, 1, 2, 1⟩ : Tern).IsMinkowski ∧ ¬ (⟨2, 1, 2, 1, 2, 1⟩ : Tern).IsReducedPrinted := by
  decide

/-! ### Comparison with the library's Minkowski reduction -/

/-- The real matrix of a ternary form. -/
noncomputable abbrev Tern.realMat (t : Tern) : Matrix (Fin 3) (Fin 3) ℝ := t.mat.map (Int.cast : ℤ → ℝ)

/-- The integral value of the form at $(x, y, z)$. -/
def Tern.valZ (t : Tern) (x y z : ℤ) : ℤ :=
  t.a * x ^ 2 + t.c * y ^ 2 + t.g * z ^ 2 + 2 * t.b * x * y + 2 * t.h * x * z + 2 * t.f * y * z

theorem Tern.val_cast (t : Tern) (x y z : ℤ) :
    Reduction.val t.realMat (Reduction.cast ![x, y, z]) = ((t.valZ x y z : ℤ) : ℝ) := by
  simp [Reduction.val, Reduction.cast, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Tern.mat, Tern.valZ]
  ring

theorem Tern.isSymm (t : Tern) : t.realMat.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Tern.mat]

theorem tv0 {s : Fin 3 → ℤ} (hs : s ∈ Reduction.minkowskiTestVectors (0 : Fin 3)) : s = ![1, 0, 0] := by
  obtain ⟨-, h2, h3⟩ := hs
  funext i
  fin_cases i
  · simpa using h2
  · simpa using h3 1 (by decide)
  · simpa using h3 2 (by decide)

theorem tv1 {s : Fin 3 → ℤ} (hs : s ∈ Reduction.minkowskiTestVectors (1 : Fin 3)) :
    ∃ x : ℤ, (x = 0 ∨ x = 1 ∨ x = -1) ∧ s = ![x, 1, 0] := by
  obtain ⟨h1, h2, h3⟩ := hs
  refine ⟨s 0, h1 0 (by decide), ?_⟩
  funext i
  fin_cases i
  · rfl
  · simpa using h2
  · simpa using h3 2 (by decide)

theorem tv2 {s : Fin 3 → ℤ} (hs : s ∈ Reduction.minkowskiTestVectors (2 : Fin 3)) :
    ∃ x y : ℤ, (x = 0 ∨ x = 1 ∨ x = -1) ∧ (y = 0 ∨ y = 1 ∨ y = -1) ∧ s = ![x, y, 1] := by
  obtain ⟨h1, h2, -⟩ := hs
  refine ⟨s 0, s 1, h1 0 (by decide), h1 1 (by decide), ?_⟩
  funext i
  fin_cases i
  · rfl
  · rfl
  · simpa using h2

theorem mem_tv1 (x : ℤ) (hx : x = 0 ∨ x = 1 ∨ x = -1) :
    (![x, 1, 0] : Fin 3 → ℤ) ∈ Reduction.minkowskiTestVectors (1 : Fin 3) := by
  refine ⟨fun i hi => ?_, rfl, fun i hi => ?_⟩
  · fin_cases i
    · simpa using hx
    · simp at hi
    · simp at hi
  · fin_cases i <;> simp at hi ⊢

theorem mem_tv2 (x y : ℤ) (hx : x = 0 ∨ x = 1 ∨ x = -1) (hy : y = 0 ∨ y = 1 ∨ y = -1) :
    (![x, y, 1] : Fin 3 → ℤ) ∈ Reduction.minkowskiTestVectors (2 : Fin 3) := by
  refine ⟨fun i hi => ?_, rfl, fun i hi => ?_⟩
  · fin_cases i
    · simpa using hx
    · simpa using hy
    · simp at hi
  · fin_cases i <;> simp at hi

/-- **Minkowski reduction for ternary forms** (Conway–Sloane, §10.1, p. 397, for $n = 3$; Cassels, Ch. 12,
Lemma 1.2): a ternary integral form is Minkowski reduced in the sense of the library's
`Reduction.IsMinkowskiReduced` (condition (45)) iff (46), (47) and the one-sided (48) hold. -/
@[kb "conwaysloane1999" "Ch. 15, §10.1, (45)–(48), pp. 396–397"]
theorem Tern.isMinkowskiReduced_iff (t : Tern) :
    Reduction.IsMinkowskiReduced t.realMat ↔ t.IsMinkowski := by
  rw [Reduction.lemma_1_2 (by norm_num) t.isSymm]
  have e00 : t.realMat 0 0 = (t.a : ℝ) := by simp [Tern.mat]
  have e11 : t.realMat 1 1 = (t.c : ℝ) := by simp [Tern.mat]
  have e22 : t.realMat 2 2 = (t.g : ℝ) := by simp [Tern.mat]
  unfold Tern.IsMinkowski
  simp only [Int.abs_eq_natAbs]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have ha : 0 < (t.a : ℝ) := by have := h1 0 rfl; rwa [e00] at this
    have hac : (t.a : ℝ) ≤ t.c := by have := h2 0 1 (by decide); rwa [e00, e11] at this
    have hcg : (t.c : ℝ) ≤ t.g := by have := h2 1 2 (by decide); rwa [e11, e22] at this
    have s1 : ∀ x : ℤ, (x = 0 ∨ x = 1 ∨ x = -1) → t.c ≤ t.valZ x 1 0 := by
      intro x hx
      have := h3 1 _ (mem_tv1 x hx)
      rw [Tern.val_cast, e11] at this
      exact_mod_cast this
    have s2 : ∀ x y : ℤ, (x = 0 ∨ x = 1 ∨ x = -1) → (y = 0 ∨ y = 1 ∨ y = -1) → t.g ≤ t.valZ x y 1 := by
      intro x y hx hy
      have := h3 2 _ (mem_tv2 x y hx hy)
      rw [Tern.val_cast, e22] at this
      exact_mod_cast this
    have a1 := s1 1 (by simp)
    have a2 := s1 (-1) (by simp)
    have b1 := s2 1 0 (by simp) (by simp)
    have b2 := s2 (-1) 0 (by simp) (by simp)
    have c1 := s2 0 1 (by simp) (by simp)
    have c2 := s2 0 (-1) (by simp) (by simp)
    have d1 := s2 1 1 (by simp) (by simp)
    have d2 := s2 1 (-1) (by simp) (by simp)
    have d3 := s2 (-1) 1 (by simp) (by simp)
    have d4 := s2 (-1) (-1) (by simp) (by simp)
    simp only [Tern.valZ] at a1 a2 b1 b2 c1 c2 d1 d2 d3 d4
    norm_num at a1 a2 b1 b2 c1 c2 d1 d2 d3 d4
    have ha' : 0 < t.a := by exact_mod_cast ha
    have hac' : t.a ≤ t.c := by exact_mod_cast hac
    have hcg' : t.c ≤ t.g := by exact_mod_cast hcg
    refine ⟨ha', hac', hcg', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  · intro H
    obtain ⟨ha, hac, hcg, hb, hh, hf, p1, p2, p3, p4⟩ := H
    refine ⟨fun i hi => ?_, fun i j hij => ?_, fun j s hs => ?_⟩
    · have : i = 0 := Fin.ext hi
      subst this
      rw [e00]; exact_mod_cast ha
    · fin_cases i <;> fin_cases j <;> simp [e00, e11, e22] at hij ⊢ <;>
        first | exact_mod_cast hac | exact_mod_cast hcg | exact_mod_cast (hac.trans hcg)
    · have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
      rcases hj with rfl | rfl | rfl
      · rw [tv0 hs, e00, Tern.val_cast]
        have : t.valZ 1 0 0 = t.a := by simp [Tern.valZ]
        rw [this]
      · obtain ⟨x, hx, rfl⟩ := tv1 hs
        rw [e11, Tern.val_cast]
        have : (t.c : ℝ) ≤ ((t.valZ x 1 0 : ℤ) : ℝ) := by
          exact_mod_cast (by rcases hx with rfl | rfl | rfl <;> simp [Tern.valZ] <;> omega : t.c ≤ t.valZ x 1 0)
        exact this
      · obtain ⟨x, y, hx, hy, rfl⟩ := tv2 hs
        rw [e22, Tern.val_cast]
        have : (t.g : ℝ) ≤ ((t.valZ x y 1 : ℤ) : ℝ) := by
          exact_mod_cast (by
            rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp [Tern.valZ] <;> omega :
              t.g ≤ t.valZ x y 1)
        exact this

/-! ### §11: the Dickson–Ross example, (50) -/

/-- The negative of the first Dickson–Ross form $x^2 - 3y^2 - 2yz - 23z^2$, in the variables $(y, z, x)$: Gram matrix
$\begin{pmatrix} 3&1&0\\1&23&0\\0&0&-1\end{pmatrix}$ (Conway–Sloane, §11, p. 403). -/
@[kb "conwaysloane1999" "Ch. 15, §11, p. 403 (the first Dickson–Ross form, negated)"]
def dicksonRossA : Matrix (Fin 3) (Fin 3) ℤ := !![3, 1, 0; 1, 23, 0; 0, 0, -1]

/-- The negative of the second Dickson–Ross form $x^2 - 7y^2 - 6yz - 11z^2$, in the variables $(y, z, x)$: Gram matrix
$\begin{pmatrix} 7&3&0\\3&11&0\\0&0&-1\end{pmatrix}$ (Conway–Sloane, §11, p. 403). -/
@[kb "conwaysloane1999" "Ch. 15, §11, p. 403 (the second Dickson–Ross form, negated)"]
def dicksonRossB : Matrix (Fin 3) (Fin 3) ℤ := !![7, 3, 0; 3, 11, 0; 0, 0, -1]

/-- **The unimodular matrix $M$ of (50)** (Conway–Sloane, §11, p. 404). -/
@[kb "conwaysloane1999" "Ch. 15, §11, (50), p. 404"]
def dicksonRossM : Matrix (Fin 3) (Fin 3) ℤ := !![-3, 2, 10; -2, 3, 14; -1, 1, 5]

/-- $M$ is unimodular: $\det M = -1$. -/
@[kb "conwaysloane1999" "Ch. 15, §11, (50), p. 404"]
theorem dicksonRossM_det : dicksonRossM.det = -1 := by
  simp [dicksonRossM, Matrix.det_fin_three]

/-- **(50): $M$ transforms the first Dickson–Ross form into the second**, in the book's convention (4):
$B = M A M^{\mathrm t}$. (The library's `Siegel.ex2_properIntEquiv`, Cassels Ch. 11 Ex. 2, proves integral equivalence
of the same two forms with a different matrix.) -/
@[kb "conwaysloane1999" "Ch. 15, §11, (50), p. 404"]
theorem dicksonRoss_equiv : dicksonRossM * dicksonRossA * dicksonRossMᵀ = dicksonRossB := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dicksonRossM, dicksonRossA, dicksonRossB, Matrix.mul_apply, Fin.sum_univ_three]

/-- (50) as an identity of polynomials: with $w = u M$, i.e. $w_0 = -3u_0 - 2u_1 - u_2$, $w_1 = 2u_0 + 3u_1 + u_2$,
$w_2 = 10u_0 + 14u_1 + 5u_2$, one has $3w_0^2 + 2w_0w_1 + 23w_1^2 - w_2^2 = 7u_0^2 + 6u_0u_1 + 11u_1^2 - u_2^2$
(the first form at $uM$ equals the second form at $u$; $(u_0, u_1, u_2) = (y, z, x)$ up to the sign of the forms). -/
@[kb "conwaysloane1999" "Ch. 15, §11, (50), p. 404"]
theorem dicksonRoss_poly (u₀ u₁ u₂ : ℤ) :
    3 * (-3 * u₀ - 2 * u₁ - u₂) ^ 2 + 2 * (-3 * u₀ - 2 * u₁ - u₂) * (2 * u₀ + 3 * u₁ + u₂)
        + 23 * (2 * u₀ + 3 * u₁ + u₂) ^ 2 - (10 * u₀ + 14 * u₁ + 5 * u₂) ^ 2 =
      7 * u₀ ^ 2 + 6 * u₀ * u₁ + 11 * u₁ ^ 2 - u₂ ^ 2 := by
  ring

/-! ### §11: the two ternary forms (51) -/

/-- **(51a)**: $\begin{pmatrix} -1&1&0\\1&63&0\\0&0&2\end{pmatrix}$ (Conway–Sloane, §11, p. 404). -/
@[kb "conwaysloane1999" "Ch. 15, §11, (51a), p. 404"]
def form51a : Matrix (Fin 3) (Fin 3) ℤ := !![-1, 1, 0; 1, 63, 0; 0, 0, 2]

/-- **(51b)**: $\begin{pmatrix} -9&1&0\\1&7&0\\0&0&2\end{pmatrix}$ (Conway–Sloane, §11, p. 404). -/
@[kb "conwaysloane1999" "Ch. 15, §11, (51b), p. 404"]
def form51b : Matrix (Fin 3) (Fin 3) ℤ := !![-9, 1, 0; 1, 7, 0; 0, 0, 2]

/-- Both forms (51) have determinant $-128$, as in the text. -/
@[kb "conwaysloane1999" "Ch. 15, §11, (51), p. 404"]
theorem form51_det : form51a.det = -128 ∧ form51b.det = -128 := by
  constructor <;> simp [form51a, form51b, Matrix.det_fin_three]

/-- (51a) is integrally equivalent to $\mathrm{diag}(-1, 64, 2)$ (the basis $e_0, e_0 + e_1, e_2$ is diagonal), by an
explicit unimodular matrix: $P A P^{\mathrm t} = \mathrm{diag}(-1, 64, 2)$, $\det P = 1$. -/
@[kb "conwaysloane1999" "Ch. 15, §11, (51a), p. 405"]
theorem form51a_equiv_diag :
    (!![1, 0, 0; 1, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ).det = 1 ∧
      (!![1, 0, 0; 1, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ) * form51a *
          (!![1, 0, 0; 1, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ)ᵀ = Matrix.diagonal ![-1, 64, 2] := by
  constructor
  · simp [Matrix.det_fin_three]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [form51a, Matrix.mul_apply, Fin.sum_univ_three]

/-- (51b) is the Gram matrix of the rational basis $3e_0, e_1/3, e_2$ of the lattice of (51a): $Q A Q^{\mathrm t} = B$ with
$Q = \mathrm{diag}(3, 1/3, 1)$ (the gluing of §11: the lattices $L$, $M$ meet in an index-3 sublattice of each). -/
@[kb "conwaysloane1999" "Ch. 15, §11, (51b), pp. 404–405"]
theorem form51b_rational_basis :
    Matrix.diagonal ![(3 : ℚ), 1 / 3, 1] * form51a.map (Int.cast : ℤ → ℚ) * Matrix.diagonal ![(3 : ℚ), 1 / 3, 1] =
      form51b.map (Int.cast : ℤ → ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [form51a, form51b, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply] <;> norm_num

/-! ### §10.1: Table 15.6 -/

/-- Build a ternary form from the book's table notation $a_b\,c_f\,g_h$ (with $h$ defaulting to $0$). -/
def mk (a b c f g : ℤ) (h : ℤ := 0) : Tern := ⟨a, b, c, f, g, h⟩

/-- Positive definiteness by leading principal minors. -/
def Tern.IsPosDef (t : Tern) : Prop := 0 < t.a ∧ 0 < t.a * t.c - t.b ^ 2 ∧ 0 < t.det

instance (t : Tern) : Decidable t.IsPosDef := by unfold Tern.IsPosDef; infer_instance

/-- Reorder the basis by $p$ and change the signs of the basis vectors by $e$: the Gram matrix $e_ie_j a_{p(i)p(j)}$. -/
def Tern.transform (t : Tern) (p : Fin 3 → Fin 3) (e : Fin 3 → ℤ) : Tern :=
  ⟨e 0 * e 0 * t.mat (p 0) (p 0), e 0 * e 1 * t.mat (p 0) (p 1), e 1 * e 1 * t.mat (p 1) (p 1),
    e 1 * e 2 * t.mat (p 1) (p 2), e 2 * e 2 * t.mat (p 2) (p 2), e 0 * e 2 * t.mat (p 0) (p 2)⟩

/-- The six reorderings of a basis. -/
def basisOrders : List (Fin 3 → Fin 3) := [![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]]

/-- The eight sign changes of the basis vectors. -/
def basisSigns : List (Fin 3 → ℤ) :=
  [![1, 1, 1], ![1, 1, -1], ![1, -1, 1], ![1, -1, -1], ![-1, 1, 1], ![-1, 1, -1], ![-1, -1, 1], ![-1, -1, -1]]

/-- A ternary form is *reduced in some basis* if reordering and changing signs of the basis vectors gives a form that
satisfies the printed (46)–(48). (The forms of Table 15.6 are listed with $h = 0$ where possible, not in the order
$a \le c \le g$.) -/
def Tern.IsReducedInSomeBasis (t : Tern) : Prop :=
  ∃ p ∈ basisOrders, ∃ e ∈ basisSigns, (t.transform p e).IsReducedPrinted

instance (t : Tern) : Decidable t.IsReducedInSomeBasis := by unfold Tern.IsReducedInSomeBasis; infer_instance

/-- **Table 15.6**: the indecomposable reduced positive definite ternary forms of determinant $d \le 50$, as
printed (entry $a_b\,c_f\,g_h$ is `mk a b c f g h`). -/
@[kb "conwaysloane1999" "Ch. 15, §10.1, Table 15.6, p. 398"]
def table156 : List (ℕ × List Tern) := [
  (4, [mk 2 1 2 1 2]),
  (7, [mk 2 1 2 1 3]),
  (8, [mk 2 1 3 1 2]),
  (10, [mk 2 1 2 1 4]),
  (12, [mk 2 1 4 1 2, mk 3 1 2 1 3]),
  (13, [mk 2 1 2 1 5, mk 2 1 3 1 3]),
  (16, [mk 2 1 5 1 2, mk 2 1 2 1 6, mk 3 1 3 1 3 (-1)]),
  (17, [mk 3 1 2 1 4]),
  (18, [mk 2 1 3 1 4]),
  (19, [mk 2 1 2 1 7, mk 2 1 4 1 3]),
  (20, [mk 2 1 4 2 4, mk 3 1 3 1 3 1]),
  (21, [mk 3 1 3 1 3]),
  (22, [mk 2 1 2 1 8, mk 3 1 2 1 5]),
  (23, [mk 2 1 3 1 5]),
  (24, [mk 2 1 7 1 2, mk 4 1 2 1 4, mk 3 1 3 1 4 (-1)]),
  (25, [mk 2 1 2 1 9, mk 2 1 5 1 3]),
  (26, [mk 2 1 4 1 4]),
  (27, [mk 3 1 2 1 6, mk 2 1 4 2 5]),
  (28, [mk 2 1 8 1 2, mk 2 1 2 1 10, mk 2 1 3 1 6, mk 2 1 5 2 4, mk 3 1 3 1 4 1]),
  (29, [mk 3 1 3 1 4]),
  (30, [mk 3 1 4 1 3]),
  (31, [mk 2 1 2 1 11, mk 4 1 2 1 5]),
  (32, [mk 2 1 9 1 2, mk 3 1 2 1 7, mk 3 1 3 1 5 (-1), mk 3 1 4 2 4, mk 4 2 4 2 4]),
  (33, [mk 2 1 3 1 7, mk 2 1 4 1 5]),
  (34, [mk 2 1 2 1 12, mk 2 1 5 1 4, mk 2 1 4 2 6]),
  (35, [mk 3 1 4 1 4 (-1)]),
  (36, [mk 2 1 10 1 2, mk 2 1 6 2 4, mk 2 1 5 1 5 (-1), mk 3 1 3 1 5 1, mk 4 1 4 1 4 (-2)]),
  (37, [mk 2 1 2 1 13, mk 2 1 7 1 3, mk 3 1 2 1 8, mk 2 1 5 2 5, mk 3 1 3 1 5]),
  (38, [mk 2 1 3 1 8, mk 4 1 2 1 6]),
  (39, [mk 3 1 5 1 3, mk 3 1 4 1 4 1]),
  (40, [mk 2 1 11 1 2, mk 2 1 2 1 14, mk 2 1 4 1 6, mk 5 1 2 1 5, mk 3 1 3 1 6 (-1), mk 4 1 3 1 4]),
  (41, [mk 2 1 4 2 7, mk 3 1 4 1 4]),
  (42, [mk 3 1 2 1 9]),
  (43, [mk 2 1 2 1 15, mk 2 1 8 1 3, mk 2 1 3 1 9, mk 2 1 5 1 5, mk 3 1 4 2 5]),
  (44, [mk 2 1 12 1 2, mk 2 1 7 2 4, mk 3 1 3 1 6 1, mk 3 1 5 2 4, mk 4 1 4 2 4, mk 4 2 4 2 5]),
  (45, [mk 4 1 2 1 7, mk 2 1 5 1 6 (-1), mk 3 1 3 1 6]),
  (46, [mk 2 1 2 1 16, mk 2 1 5 2 6, mk 3 1 4 1 5 (-1)]),
  (47, [mk 3 1 2 1 10, mk 2 1 4 1 7, mk 2 1 6 2 5]),
  (48, [mk 2 1 13 1 2, mk 2 1 3 1 10, mk 2 1 4 2 8, mk 2 1 6 3 6, mk 3 1 6 1 3, mk 3 1 3 1 7 (-1),
    mk 4 1 5 1 4 (-2), mk 4 2 5 2 4]),
  (49, [mk 2 1 2 1 17, mk 2 1 9 1 3, mk 5 1 2 1 6, mk 5 1 3 1 5 (-2)]),
  (50, [mk 2 1 7 1 4, mk 3 1 5 1 4 1, mk 4 1 4 1 4 (-1)])]

/-- **Table 15.6 checked entry by entry:** every listed form has the listed determinant, is positive definite, and is
(after reordering/changing signs of the basis) reduced in the sense of the printed (46)–(48). (That the table is
complete and that its forms are indecomposable is not checked.) -/
@[kb "conwaysloane1999" "Ch. 15, §10.1, Table 15.6, p. 398"]
theorem table156_correct :
    ∀ e ∈ table156, ∀ t ∈ e.2, t.det = (e.1 : ℤ) ∧ t.IsPosDef ∧ t.IsReducedInSomeBasis := by
  decide +kernel

end Examples
end ConwaySloane
end QuadFormsKB
