/-
# Cassels, Chapter 11, Example 6 (i), (iii): the genus of $x^2 + y^2 + 16z^2$ has exactly two classes

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, Example 6 (p. 252): the genus of
$f = x^2 + y^2 + 16z^2$ consists of the classes of $f$ and of $g = (x - y)^2 + (x + y + z)^2 + 4z^2$. Variables
$x, y, z$ are $x_0, x_1, x_2$.

**Proved (unconditionally).** `ex6Classes_holds : Ex6Classes`, the named statement of `Ch11Examples4.lean`; with it
`ex6_primRep_iff` and `ex6_primRep_exactly_one` (Example 6 (iv)) become unconditional.

**Route** (the "heroic" enumeration of the hint, with the reduction theory of Chapter 12):
* $g$ is a $3$-neighbour of $f$ (a kernel-checked neighbour certificate), hence in the genus of $f$ (`ex6_sameGenus`;
  `NbCert.sameGenus`, the neighbour of a lattice is in its genus).
* A form $Q'$ of the genus is positive definite with $\det H_{Q'} = 128$; Minkowski reduction makes it equivalent to
  $a x_0^2 + b x_1^2 + c x_2^2 + h x_0x_1 + g x_0x_2 + f x_1x_2$ with the reduction conditions and $4abc \le 128$, so
  $a \le 3$, $b \le 5$ (`ex6_bounds`), and a kernel check (`ex6_chk`) shows that the sextuple $(a, b, c, h, g, f)$ is one of
  $28$ explicit ones (`Ex6Data.cands`; they represent the $9$ classes of positive definite ternary forms with
  $\det H = 128$).
* Of these, $1$ is equivalent to $f$ and $4$ to $g$ (equivalence certificates), and the other $23$ represent a residue
  modulo $2$, $4$ or $8$ that $f$ does not represent or vice versa, so they are not in the genus of $f$ (`ex6_ver`).
* Since $f \not\sim g$ (`ex6_not_intEquiv`), the genus has exactly two classes.

The certificates were produced by a script (enumeration of reduced forms, an equivalence search and the neighbour
construction of `Siegel/KneserGen.lean`); Lean re-checks all of them with `decide`.
-/
import QuadFormsKB.Literature.Cassels.Ch11Ex6ClassesReduction

open Matrix QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser

set_option linter.style.longLine false

namespace QuadFormsKB.Cassels.Ch11Ex4

namespace Ex6Data

/-- The sextuple of $f = x_0^2 + x_1^2 + 16x_2^2$. -/
def fT : Tup := (1, 1, 16, 0, 0, 0)

/-- The sextuple of $g = 2x_0^2 + 2x_1^2 + 5x_2^2 + 2x_0x_2 + 2x_1x_2$. -/
def gT : Tup := (2, 2, 5, 0, 2, 2)

/-- **The reduced sextuples of determinant $128$** (all sextuples $(a, b, c, h, g, f)$ with the reduction conditions,
$\det H = 128$ and $4abc \le 128$; generator output). -/
def cands : List Tup := [(1, 1, 16, 0, 0, 0), (1, 2, 8, 0, 0, 0), (1, 4, 5, 0, 0, -4), (1, 4, 4, 0, 0, 0), (1, 4, 5, 0, 0, 4), (2, 2, 6, -2, -2, 0), (2, 2, 6, -2, -2, 2), (2, 2, 6, -2, 0, -2), (2, 2, 6, -2, 0, 2), (2, 2, 6, -2, 2, -2), (2, 2, 6, -2, 2, 0), (2, 2, 5, 0, -2, -2), (2, 2, 5, 0, -2, 2), (2, 2, 4, 0, 0, 0), (2, 2, 5, 0, 2, -2), (2, 2, 5, 0, 2, 2), (2, 2, 6, 2, -2, -2), (2, 2, 6, 2, -2, 0), (2, 2, 6, 2, 0, -2), (2, 2, 6, 2, 0, 2), (2, 2, 6, 2, 2, 0), (2, 2, 6, 2, 2, 2), (2, 3, 3, 0, 0, -2), (2, 3, 3, 0, 0, 2), (3, 3, 3, -2, -2, -2), (3, 3, 3, -2, 2, 2), (3, 3, 3, 2, -2, 2), (3, 3, 3, 2, 2, -2)]

/-- **Equivalence certificates from $f$** to the reduced sextuples in the class of $f$ (generator output). -/
def isoF : List (Tup × IsoCert 3) := [((1, 1, 16, 0, 0, 0), ⟨!![-1, 0, 0; 0, -1, 0; 0, 0, -1], !![-1, 0, 0; 0, -1, 0; 0, 0, -1]⟩)]

/-- **Equivalence certificates from $g$** to the reduced sextuples in the class of $g$ (generator output). -/
def isoG : List (Tup × IsoCert 3) := [((2, 2, 5, 0, -2, -2), ⟨!![-1, 0, 0; 0, -1, 0; 0, 0, 1], !![-1, 0, 0; 0, -1, 0; 0, 0, 1]⟩), ((2, 2, 5, 0, -2, 2), ⟨!![-1, 0, 0; 0, -1, -1; 0, 0, 1], !![-1, 0, 0; 0, -1, -1; 0, 0, 1]⟩), ((2, 2, 5, 0, 2, -2), ⟨!![-1, 0, -1; 0, -1, 0; 0, 0, 1], !![-1, 0, -1; 0, -1, 0; 0, 0, 1]⟩), ((2, 2, 5, 0, 2, 2), ⟨!![-1, 0, -1; 0, -1, -1; 0, 0, 1], !![-1, 0, -1; 0, -1, -1; 0, 0, 1]⟩)]

/-- **Separating residues** $(t, N, m)$: the residue $m \bmod N$ is represented by exactly one of $f$ and the form of
$t$ (generator output). -/
def seps : List (Tup × ℕ × ℤ) := [((1, 2, 8, 0, 0, 0), 4, 3), ((1, 4, 5, 0, 0, -4), 8, 2), ((1, 4, 4, 0, 0, 0), 4, 2), ((1, 4, 5, 0, 0, 4), 8, 2), ((2, 2, 6, -2, -2, 0), 2, 1), ((2, 2, 6, -2, -2, 2), 2, 1), ((2, 2, 6, -2, 0, -2), 2, 1), ((2, 2, 6, -2, 0, 2), 2, 1), ((2, 2, 6, -2, 2, -2), 2, 1), ((2, 2, 6, -2, 2, 0), 2, 1), ((2, 2, 4, 0, 0, 0), 2, 1), ((2, 2, 6, 2, -2, -2), 2, 1), ((2, 2, 6, 2, -2, 0), 2, 1), ((2, 2, 6, 2, 0, -2), 2, 1), ((2, 2, 6, 2, 0, 2), 2, 1), ((2, 2, 6, 2, 2, 0), 2, 1), ((2, 2, 6, 2, 2, 2), 2, 1), ((2, 3, 3, 0, 0, -2), 4, 3), ((2, 3, 3, 0, 0, 2), 4, 3), ((3, 3, 3, -2, -2, -2), 4, 1), ((3, 3, 3, -2, 2, 2), 4, 1), ((3, 3, 3, 2, -2, 2), 4, 1), ((3, 3, 3, 2, 2, -2), 4, 1)]

/-- **A $3$-neighbour certificate** for $g$ as the Gram form of the $3$-neighbour $L(\vec v)$, $\vec v = (1, 1, 1)$, of
$(\mathbb Z^3, f)$ (generator output; see `NbCert`). -/
def nbCert : NbCert 3 := ⟨![1, 1, 1], !![-3, -1, -6; 3, -1, -3; 0, -1, 0], ![0, 2, 0], ![2, 0, 0], !![1, 2, 21; 0, 0, -3; 1, 1, 22], ![-2, 0, -2], ![0, -1, 0], !![-1, 2, -1; 0, 0, -9; -1, -1, 2]⟩

end Ex6Data

open Ex6Data

/-- Helper: $f = x_0^2 + x_1^2 + 16x_2^2$ is the form of the sextuple $(1, 1, 16, 0, 0, 0)$. -/
theorem ex6f_eq_tupForm : ex6f = tupForm fT := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ex6f, tupForm, tf, fT, QuadForm.diag, QuadForm.ofUpper]

/-- Helper: $g = 2x_0^2 + 2x_1^2 + 5x_2^2 + 2x_0x_2 + 2x_1x_2$ is the form of the sextuple $(2, 2, 5, 0, 2, 2)$. -/
theorem ex6g_eq_tupForm : ex6g = tupForm gT := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ex6g, tupForm, tf, gT, QuadForm.ofUpper]

/-- Helper: $f = x_0^2 + x_1^2 + 16x_2^2$ is positive definite. -/
theorem ex6f_posDef : IntQF.PosDef ex6f := by
  intro x hx
  rw [eval_ex6f]
  have : x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx (funext fun i => by fin_cases i <;> simp [hc.1, hc.2.1, hc.2.2])
  rcases this with h | h | h <;> positivity

/-- Helper: the reduction conditions with $4abc \le 128$ force $a \le 3$ and $b \le 5$. -/
theorem ex6_bounds : ∀ a b c : ℤ, 0 < a → a ≤ b → b ≤ c → 4 * a * b * c ≤ 128 → a ≤ 3 ∧ b ≤ 5 := by
  intro a b c ha hab hbc h
  have h1 : a * a ≤ a * b := by nlinarith
  have h2 : a * a * a ≤ a * b * c := by nlinarith
  have h3 : b * b ≤ a * b * c := by nlinarith
  constructor
  · by_contra hc
    have h4 : 4 ≤ a := by omega
    have : 64 ≤ a * a * a := by nlinarith
    linarith
  · by_contra hc
    have h4 : 6 ≤ b := by omega
    have : 36 ≤ b * b := by nlinarith
    linarith

/-- **The finite check for determinant $128$** (kernel evaluation): every reduced sextuple of determinant $128$ with
$4abc \le 128$, $a \le 3$, $b \le 5$ is in `Ex6Data.cands`. -/
theorem ex6_chk : chkAll 128 3 5 cands = true := by decide +kernel

/-- **The verdicts for determinant $128$** (kernel evaluation): each sextuple of `Ex6Data.cands` is equivalent to $f$ or
$g$ by a certificate, or separated from $f$ by a residue modulo $2$, $4$ or $8$. -/
theorem ex6_ver : cands.all (verdict fT gT isoF isoG seps) = true := by decide +kernel

/-- **$g$ is in the genus of $f$** (Example 6): $g$ is the Gram form of a $3$-neighbour of $(\mathbb Z^3, f)$
(certificate `Ex6Data.nbCert`), and $3 \nmid \det H_f = 128$. -/
@[kb "cassels1978" "Ch. 11, Ex. 6, p. 252 (g is in the genus of f)"]
theorem ex6_sameGenus : SameGenus ex6f ex6g :=
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  NbCert.sameGenus (p := 3) (c := nbCert) (by norm_num) (by rw [hessian_det_ex6f]; norm_num)
    (by rw [ex6f_eq_tupForm, ex6g_eq_tupForm]; decide)

/-- **Every form in the genus of $f = x_0^2 + x_1^2 + 16x_2^2$ is equivalent to $f$ or to $g$** (Example 6), by
Minkowski reduction and the finite checks `ex6_chk`, `ex6_ver`. -/
@[kb "cassels1978" "Ch. 11, Ex. 6 (i), (iii), p. 252 (the classes of the genus)"]
theorem ex6_classify (Q' : QuadForm ℤ 3) (h : SameGenus ex6f Q') : IntEquiv ex6f Q' ∨ IntEquiv ex6g Q' := by
  rw [ex6f_eq_tupForm] at h ⊢
  rw [ex6g_eq_tupForm]
  exact classify_of_checks fT gT 128 3 5 cands isoF isoG seps (ex6f_eq_tupForm ▸ ex6f_posDef)
    (by rw [← ex6f_eq_tupForm, hessian_det_ex6f]) ex6_bounds ex6_chk ex6_ver Q' h

/-- **Cassels, Ch. 11, Example 6 (i), (iii)** (p. 252), the class content: $g$ is in the genus of
$f = x^2 + y^2 + 16z^2$ and this genus has exactly two classes, those of $f$ and of $g = (x - y)^2 + (x + y + z)^2 +
4z^2$. Unconditional: `ex6_sameGenus`, `ex6_classify` and $f \not\sim g$ (`ex6_not_intEquiv`). -/
@[kb "cassels1978" "Ch. 11, Ex. 6 (i), (iii), p. 252 (proof)"]
theorem ex6Classes_holds : Ex6Classes :=
  ⟨ex6_sameGenus, ncard_genusClasses_eq_two ex6_sameGenus ex6_not_intEquiv ex6_classify⟩

/-- **Cassels, Ch. 11, Example 6 (iv)** (p. 252), unconditional: an odd square $m^2$, $m > 0$, is primitively
represented by $f$ iff $m \equiv 1 \pmod 4$ and by $g$ iff $m \equiv 3 \pmod 4$ (`ex6_primRep_iff` with
`ex6Classes_holds`). -/
@[kb "cassels1978" "Ch. 11, Ex. 6 (iv), p. 252 (unconditional)"]
theorem ex6_primRep_iff' (m : ℤ) (hm0 : 0 < m) (hm2 : m % 2 = 1) :
    ((∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ ex6f.eval x = m ^ 2) ↔ m % 4 = 1) ∧
      ((∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ ex6g.eval x = m ^ 2) ↔ m % 4 = 3) :=
  ex6_primRep_iff ex6Classes_holds m hm0 hm2

end QuadFormsKB.Cassels.Ch11Ex4
