/-
# Cassels, Appendix B: cited results stated as named statements

Cassels, *Rational Quadratic Forms* (1978), Appendix B (*Analytic methods*), pp. 368–390. Cassels gives no proofs in
this appendix ("for the proofs … the reader must consult the appropriate texts", p. 383). The results below are not in
the library; they are stated here as named `Prop` structures, never assumed by a theorem except where said.

| Cassels | Lean |
|---|---|
| §3, p. 377: Magnus: finitely many one-class genera in $n \ge 3$ variables; every genus with $n \ge 35$ has two classes | `MagnusOneClassGenera` (named), `MagnusOneClassGenera.two_le_encard` |
| §5, p. 386: Witt: the genus of determinant-$1$ improperly primitive forms in $16$ variables has two classes | `WittTwoClassesSixteen` (named), `WittTwoClassesSixteen.ncard` |
| §5, p. 387, (5.27): canonical Euler products; such forms span $M(k, N, \varepsilon)$ (Hecke) | `HasCanonicalEulerProduct`, `HeckeEulerBasisLevelOne` (named, level one) |

**Layer.** Integer-valued forms `QuadForm ℤ n` with genus `Siegel.SameGenus` and classes `Siegel.genusClasses`
(classes for $\mathrm{GL}_n(\mathbb Z)$; the number of classes of a genus is unchanged by scaling a form, so Cassels'
classically integral and the integer-valued settings give the same statements). Modular forms of level one: Mathlib
`ModularForm 𝒮ℒ k` and its $q$-expansion `UpperHalfPlane.qExpansion 1`.
-/
import QuadFormsKB.Literature.Cassels.AppA.Watson
import QuadFormsKB.Literature.Cassels.AppBSec5

open ModularForm
open scoped MatrixGroups

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels

open Siegel Lattices

/-! ### §3: Magnus on one-class genera -/

/-- **A primitive form:** no integer $d$ other than $\pm1$ divides every value $Q(x)$, $x \in \mathbb Z^n$ (for an
integer-valued form this is: the coefficients have no common factor). -/
def IsPrimitiveValues {n : ℕ} (Q : QuadForm ℤ n) : Prop := ∀ d : ℤ, (∀ x, d ∣ Q.eval x) → IsUnit d

/-- **Magnus (1937), as quoted by Cassels** (App. B, §3, p. 377; named statement): *there are only finitely many genera
of primitive integral forms in $n \ge 3$ variables which contain only one class, and in particular every genus with
$n \ge 35$ contains at least two classes.* Fields: (`finite`) a finite set `S` of positive definite forms (with their
numbers of variables) such that every primitive positive definite form in $n \ge 3$ variables whose genus consists of one
class is in the genus of a member of `S`; (`two_le`) for $n \ge 35$ every genus of positive definite forms has at least two
classes (by scaling, primitivity is irrelevant here). Magnus's proof uses Siegel's mass formula and lower bounds of the
mass (cf. (3.9), `Siegel.MagnusAsymptotic`); not in the library. Compare Watson's $n > 11$ (`DefiniteForms.WatsonTwoClasses`,
Appendix A). -/
@[kb "cassels1978" "App. B, §3, p. 377 (Magnus: finitely many one-class genera for n ≥ 3; two classes for n ≥ 35)"]
structure MagnusOneClassGenera : Prop where
  /-- Finitely many one-class genera of primitive positive definite forms in at least three variables. -/
  finite : ∃ S : Finset (Σ n : ℕ, QuadForm ℤ n), ∀ (n : ℕ) (Q : QuadForm ℤ n), 3 ≤ n → IntQF.PosDef Q →
    IsPrimitiveValues Q → genusClasses Q = {classOf Q} →
      ∃ P ∈ S, ∃ h : P.1 = n, SameGenus (h ▸ P.2) Q
  /-- Every genus of positive definite forms in $n \ge 35$ variables has at least two classes. -/
  two_le : ∀ (n : ℕ) (Q : QuadForm ℤ n), 35 ≤ n → IntQF.PosDef Q → (2 : ℕ∞) ≤ (genusClasses Q).encard

/-- **From `MagnusOneClassGenera`:** for $n \ge 35$ the genus of a positive definite form `Q` is not a single class.
Arguments: `h` the named statement, `hn : 35 ≤ n`, `hQ` positive definiteness. -/
@[kb "cassels1978" "App. B, §3, p. 377 (Magnus: every genus with n ≥ 35 contains at least two classes)"]
theorem MagnusOneClassGenera.genusClasses_ne_singleton (h : MagnusOneClassGenera) {n : ℕ} (hn : 35 ≤ n)
    {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) : genusClasses Q ≠ {classOf Q} := by
  intro h1
  have := h.two_le n Q hn hQ
  rw [h1, Set.encard_singleton] at this
  exact absurd this (by norm_num)

/-! ### §5: Witt's two classes in sixteen variables -/

/-- **Witt (1941), as quoted by Cassels** (App. B, §5, p. 386; named statement): *the genus of improperly primitive forms
of determinant $1$ in $16$ variables contains two classes* (then $N = 1$, $\varepsilon = 1$, there are no non-trivial cusp
forms of weight $8$, and the two forms have the same theta series: `Lattices.witt_sixteen`, proved). The genus is that of
$2\Gamma_8 = E_8 \perp E_8$ (`Lattices.twoE8`), and its two classes are those of $2\Gamma_8$ and $\Gamma_{16}$
(`Lattices.gamma16`): they lie in the genus (`gamma16_sameGenus`) and are distinct (`gamma16_not_isometric`), both
proved; what is assumed here is that there is no third class. A proof needs the classification of even unimodular
lattices of rank $16$ (Witt; e.g. via Kneser's neighbour method or the mass formula
$\mathrm{mass} = 1/|O(2E_8)| + 1/|O(D_{16}^+)|$). -/
@[kb "cassels1978" "App. B, §5, p. 386 (Witt: the genus of determinant 1 in 16 variables has two classes)"]
structure WittTwoClassesSixteen : Prop where
  /-- The classes of the genus of $2\Gamma_8$ are the classes of $2\Gamma_8$ and $\Gamma_{16}$. -/
  classes : genusClasses twoE8 = {classOf twoE8, classOf gamma16}

/-- **From `WittTwoClassesSixteen`:** the genus of $2\Gamma_8$ has exactly two classes (they are distinct by
`gamma16_not_isometric`). Argument: `h` the named statement. -/
@[kb "cassels1978" "App. B, §5, p. 386 (Witt: the genus of determinant 1 in 16 variables has two classes)"]
theorem WittTwoClassesSixteen.ncard (h : WittTwoClassesSixteen) : (genusClasses twoE8).ncard = 2 := by
  rw [h.classes, Set.ncard_pair]
  intro he
  exact gamma16_not_isometric (IsometricGL.symm (Quotient.exact he))

/-! ### §5: canonical Euler products (Hecke) -/

/-- **A canonical Euler product** (Cassels, App. B, §5, (5.27), p. 387): the formal Dirichlet series
$\sum_{m \ge 1}a_m m^{-s}$ of a coefficient sequence $a$ equals $\prod_p(1 - a_pp^{-s} + \varepsilon(p)p^{k-1-2s})^{-1}$.
Expanding the product, this is the identity of coefficients: $a_1 = 1$, $a$ is multiplicative, and
$a_{p^{j+2}} = a_p a_{p^{j+1}} - \varepsilon(p)p^{k-1}a_{p^j}$ for every prime $p$ and $j \ge 0$. Arguments: `a` the
coefficients ($a_0$, the constant term, plays no role), `k` the weight, `ε` the character values at primes. -/
@[kb "cassels1978" "App. B, §5, (5.27), p. 387 (canonical Euler product)"]
def HasCanonicalEulerProduct (a : ℕ → ℂ) (k : ℤ) (ε : ℕ → ℂ) : Prop :=
  a 1 = 1 ∧ (∀ m m' : ℕ, Nat.Coprime m m' → a (m * m') = a m * a m') ∧
    ∀ p : ℕ, p.Prime → ∀ j : ℕ, a (p ^ (j + 2)) = a p * a (p ^ (j + 1)) - ε p * (p : ℂ) ^ (k - 1) * a (p ^ j)

/-- **Hecke's theorem as quoted by Cassels, level one** (App. B, §5, p. 387; named statement): *the forms with a
canonical Euler product (5.27) span $M(k, N, \varepsilon)$*; here $N = 1$, $\varepsilon = 1$: the modular forms of weight
$k$ for $\mathrm{SL}_2(\mathbb Z)$ whose $q$-expansion coefficients have a canonical Euler product span
`ModularForm 𝒮ℒ k`. A proof needs the Hecke operators $T_p$ on level-one forms, their commutativity and
self-adjointness for the Petersson product (Mathlib has neither). Cassels states it for every $M(k, N, \varepsilon)$;
for $N > 1$ the precise statement needs the theory of newforms (Atkin–Lehner). -/
@[kb "cassels1978" "App. B, §5, p. 387 (Hecke: forms with a canonical Euler product span M(k, N, ε); here N = 1)"]
structure HeckeEulerBasisLevelOne (k : ℤ) : Prop where
  /-- The span of the forms with a canonical Euler product is everything. -/
  span_eq_top : Submodule.span ℂ {f : ModularForm 𝒮ℒ k |
    HasCanonicalEulerProduct (fun m => (UpperHalfPlane.qExpansion 1 f).coeff m) k (fun _ => 1)} = ⊤

end QuadFormsKB.Cassels
