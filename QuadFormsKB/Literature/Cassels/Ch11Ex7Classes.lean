/-
# Cassels, Chapter 11, Example 7 (i): the genus of $x^2 + xy + y^2 + 9z^2$ has exactly two classes

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, Example 7 (p. 252): the genus of
$f = x^2 + xy + y^2 + 9z^2$ consists of the classes of $f$ and of $g = x^2 + 3(y^2 + yz + z^2)$. Variables $x, y, z$
are $x_0, x_1, x_2$.

**Proved (unconditionally).** `ex7Classes_holds : Ex7Classes`, the named statement of `Ch11Examples4.lean`; with it
`ex7_primRep_iff` (the existence halves of Example 7 (ii), (iii)) becomes unconditional (`ex7_primRep_iff'`).

**Route** (as for Example 6, `Ch11Ex6Classes.lean`):
* $g$ is a $5$-neighbour of $f$ (kernel-checked certificate; $5 \nmid \det H_f = 54$), hence in the genus of $f$
  (`ex7_sameGenus`).
* A form of the genus has $\det H = 54$; Minkowski reduction and $4abc \le 54$ give $a \le 2$, $b \le 3$
  (`ex7_bounds`), and a kernel check (`ex7_chk`) lists the $16$ reduced sextuples (`Ex7Data.cands`; they represent the
  $5$ classes of positive definite ternary forms with $\det H = 54$).
* Of these, $2$ are equivalent to $f$, $2$ to $g$, and the other $12$ represent a residue modulo $3$ that $f$ does not
  represent, or vice versa (`ex7_ver`). With $f \not\sim g$ (`ex7_not_intEquiv`) the genus has exactly two classes.
-/
import QuadFormsKB.Literature.Cassels.Ch11Ex6ClassesReduction

open Matrix QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser

set_option linter.style.longLine false

namespace QuadFormsKB.Cassels.Ch11Ex4

namespace Ex7Data

/-- The sextuple of $f = x_0^2 + x_0x_1 + x_1^2 + 9x_2^2$. -/
def fT : Tup := (1, 1, 9, 1, 0, 0)

/-- The sextuple of $g = x_0^2 + 3x_1^2 + 3x_2^2 + 3x_1x_2$. -/
def gT : Tup := (1, 3, 3, 0, 0, 3)

/-- **The reduced sextuples of determinant $54$** (all sextuples $(a, b, c, h, g, f)$ with the reduction conditions,
$\det H = 54$ and $4abc \le 54$; generator output). -/
def cands : List Tup := [(1, 1, 9, -1, 0, 0), (1, 1, 7, 0, -1, 0), (1, 1, 7, 0, 0, -1), (1, 1, 7, 0, 0, 1), (1, 1, 7, 0, 1, 0), (1, 1, 9, 1, 0, 0), (1, 2, 4, -1, 0, -1), (1, 2, 4, -1, 0, 1), (1, 2, 4, 1, 0, -1), (1, 2, 4, 1, 0, 1), (1, 3, 3, 0, 0, -3), (1, 3, 3, 0, 0, 3), (2, 2, 2, -1, -1, 1), (2, 2, 2, -1, 1, -1), (2, 2, 2, 1, -1, -1), (2, 2, 2, 1, 1, 1)]

/-- **Equivalence certificates from $f$** to the reduced sextuples in the class of $f$ (generator output). -/
def isoF : List (Tup × IsoCert 3) := [((1, 1, 9, -1, 0, 0), ⟨!![-1, 0, 0; 0, 1, 0; 0, 0, -1], !![-1, 0, 0; 0, 1, 0; 0, 0, -1]⟩), ((1, 1, 9, 1, 0, 0), ⟨!![-1, -1, 0; 0, 1, 0; 0, 0, -1], !![-1, -1, 0; 0, 1, 0; 0, 0, -1]⟩)]

/-- **Equivalence certificates from $g$** to the reduced sextuples in the class of $g$ (generator output). -/
def isoG : List (Tup × IsoCert 3) := [((1, 3, 3, 0, 0, -3), ⟨!![-1, 0, 0; 0, -1, 0; 0, 0, 1], !![-1, 0, 0; 0, -1, 0; 0, 0, 1]⟩), ((1, 3, 3, 0, 0, 3), ⟨!![-1, 0, 0; 0, -1, -1; 0, 0, 1], !![-1, 0, 0; 0, -1, -1; 0, 0, 1]⟩)]

/-- **Separating residues** $(t, N, m)$: the residue $m \bmod N$ is represented by exactly one of $f$ and the form of
$t$ (generator output). -/
def seps : List (Tup × ℕ × ℤ) := [((1, 1, 7, 0, -1, 0), 3, 2), ((1, 1, 7, 0, 0, -1), 3, 2), ((1, 1, 7, 0, 0, 1), 3, 2), ((1, 1, 7, 0, 1, 0), 3, 2), ((1, 2, 4, -1, 0, -1), 3, 2), ((1, 2, 4, -1, 0, 1), 3, 2), ((1, 2, 4, 1, 0, -1), 3, 2), ((1, 2, 4, 1, 0, 1), 3, 2), ((2, 2, 2, -1, -1, 1), 3, 1), ((2, 2, 2, -1, 1, -1), 3, 1), ((2, 2, 2, 1, -1, -1), 3, 1), ((2, 2, 2, 1, 1, 1), 3, 1)]

/-- **A $5$-neighbour certificate** for $g$ as the Gram form of the $5$-neighbour $L(\vec v)$, $\vec v = (5, 1, 4)$, of
$(\mathbb Z^3, f)$ (generator output; see `NbCert`). -/
def nbCert : NbCert 3 := ⟨![5, 1, 4], !![0, -10, -5; 4, 5, -2; 1, 0, 2], ![4, 0, 3], ![1, 0, 0], !![-4, -2, -27; 4, 3, 28; 2, 1, 16], ![2, -2, -1], ![2, -1, 1], !![2, 4, 9; -2, 1, -4; -1, -2, 8]⟩

end Ex7Data

open Ex7Data

/-- Helper: $f = x_0^2 + x_0x_1 + x_1^2 + 9x_2^2$ is the form of the sextuple $(1, 1, 9, 1, 0, 0)$. -/
theorem ex7f_eq_tupForm : ex7f = tupForm fT := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ex7f, tupForm, tf, fT, QuadForm.ofUpper]

/-- Helper: $g = x_0^2 + 3x_1^2 + 3x_2^2 + 3x_1x_2$ is the form of the sextuple $(1, 3, 3, 0, 0, 3)$. -/
theorem ex7g_eq_tupForm : ex7g = tupForm gT := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ex7g, tupForm, tf, gT, QuadForm.ofUpper]

/-- Helper: $f = x_0^2 + x_0x_1 + x_1^2 + 9x_2^2$ is positive definite
($4f = (2x_0 + x_1)^2 + 3x_1^2 + 36x_2^2$). -/
theorem ex7f_posDef : IntQF.PosDef ex7f := by
  intro x hx
  rw [eval_ex7f]
  have : x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx (funext fun i => by fin_cases i <;> simp [hc.1, hc.2.1, hc.2.2])
  have e : 4 * (x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2 + 9 * x 2 ^ 2) = (2 * x 0 + x 1) ^ 2 + 3 * x 1 ^ 2 + 36 * x 2 ^ 2 := by
    ring
  have : 0 < (2 * x 0 + x 1) ^ 2 + 3 * x 1 ^ 2 + 36 * x 2 ^ 2 := by
    rcases this with h | h | h
    · by_cases h1 : x 1 = 0
      · have : 2 * x 0 + x 1 ≠ 0 := by rw [h1]; omega
        positivity
      · positivity
    · positivity
    · positivity
  linarith

/-- Helper: the reduction conditions with $4abc \le 54$ force $a \le 2$ and $b \le 3$. -/
theorem ex7_bounds : ∀ a b c : ℤ, 0 < a → a ≤ b → b ≤ c → 4 * a * b * c ≤ 54 → a ≤ 2 ∧ b ≤ 3 := by
  intro a b c ha hab hbc h
  have h1 : a * a ≤ a * b := by nlinarith
  have h2 : a * a * a ≤ a * b * c := by nlinarith
  have h3 : b * b ≤ a * b * c := by nlinarith
  constructor
  · by_contra hc
    have h4 : 3 ≤ a := by omega
    have : 27 ≤ a * a * a := by nlinarith
    linarith
  · by_contra hc
    have h4 : 4 ≤ b := by omega
    have : 16 ≤ b * b := by nlinarith
    linarith

/-- **The finite check for determinant $54$** (kernel evaluation): every reduced sextuple of determinant $54$ with
$4abc \le 54$, $a \le 2$, $b \le 3$ is in `Ex7Data.cands`. -/
theorem ex7_chk : chkAll 54 2 3 cands = true := by decide +kernel

/-- **The verdicts for determinant $54$** (kernel evaluation): each sextuple of `Ex7Data.cands` is equivalent to $f$ or
$g$ by a certificate, or separated from $f$ by a residue modulo $3$. -/
theorem ex7_ver : cands.all (verdict fT gT isoF isoG seps) = true := by decide +kernel

/-- **$g$ is in the genus of $f$** (Example 7): $g$ is the Gram form of a $5$-neighbour of $(\mathbb Z^3, f)$
(certificate `Ex7Data.nbCert`), and $5 \nmid \det H_f = 54$. -/
@[kb "cassels1978" "Ch. 11, Ex. 7, p. 252 (g is in the genus of f)"]
theorem ex7_sameGenus : SameGenus ex7f ex7g :=
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  NbCert.sameGenus (p := 5) (c := nbCert) (by norm_num) (by rw [hessian_det_ex7f]; norm_num)
    (by rw [ex7f_eq_tupForm, ex7g_eq_tupForm]; decide)

/-- **Every form in the genus of $f = x_0^2 + x_0x_1 + x_1^2 + 9x_2^2$ is equivalent to $f$ or to $g$** (Example 7),
by Minkowski reduction and the finite checks `ex7_chk`, `ex7_ver`. -/
@[kb "cassels1978" "Ch. 11, Ex. 7 (i), p. 252 (the classes of the genus)"]
theorem ex7_classify (Q' : QuadForm ℤ 3) (h : SameGenus ex7f Q') : IntEquiv ex7f Q' ∨ IntEquiv ex7g Q' := by
  rw [ex7f_eq_tupForm] at h ⊢
  rw [ex7g_eq_tupForm]
  exact classify_of_checks fT gT 54 2 3 cands isoF isoG seps (ex7f_eq_tupForm ▸ ex7f_posDef)
    (by rw [← ex7f_eq_tupForm, hessian_det_ex7f]) ex7_bounds ex7_chk ex7_ver Q' h

/-- **Cassels, Ch. 11, Example 7 (i)** (p. 252), the class content: $g = x^2 + 3(y^2 + yz + z^2)$ is in the genus of
$f = x^2 + xy + y^2 + 9z^2$ and this genus has exactly two classes, those of $f$ and $g$. Unconditional:
`ex7_sameGenus`, `ex7_classify` and $f \not\sim g$ (`ex7_not_intEquiv`). -/
@[kb "cassels1978" "Ch. 11, Ex. 7 (i), p. 252 (proof)"]
theorem ex7Classes_holds : Ex7Classes :=
  ⟨ex7_sameGenus, ncard_genusClasses_eq_two ex7_sameGenus ex7_not_intEquiv ex7_classify⟩

/-- **Cassels, Ch. 11, Example 7 (ii), (iii)** (p. 252), unconditional: for $m > 0$ odd with $3 \nmid m$, $4m^2$ is
primitively represented by $f$ iff $m \equiv 2 \pmod 3$ and by $g$ iff $m \equiv 1 \pmod 3$ (`ex7_primRep_iff` with
`ex7Classes_holds`). -/
@[kb "cassels1978" "Ch. 11, Ex. 7 (ii), (iii), p. 252 (unconditional)"]
theorem ex7_primRep_iff' (m : ℤ) (hm0 : 0 < m) (hm2 : m % 2 = 1) (hm3 : m % 3 ≠ 0) :
    ((∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ ex7f.eval x = 4 * m ^ 2) ↔ m % 3 = 2) ∧
      ((∃ x : Fin 3 → ℤ, Finset.univ.gcd x = 1 ∧ ex7g.eval x = 4 * m ^ 2) ↔ m % 3 = 1) :=
  ex7_primRep_iff ex7Classes_holds m hm0 hm2 hm3

end QuadFormsKB.Cassels.Ch11Ex4
