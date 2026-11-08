/-
# Watson (1963), Theorem 1 for $n \ge 12$, unconditional

G. L. Watson, *The class-number of a positive quadratic form*, Proc. London Math. Soc. (3) 13 (1963) 549–576,
Theorem 1, first case of (1.1): $c_n \ge 2$ for $n \ge 12$; Cassels, *Rational Quadratic Forms*, App. A, §3, p. 364:
every genus of positive definite forms in $n > 11$ variables has at least two classes.

The two $2$-adic inputs of `Final.lean` are proved: `watsonLocalProbesTwo_holds` (Watson's Lemma 2 at $p = 2$,
`ProbesTwo.lean`) and `watsonPhi4SplitTwo_holds` (Lemma 14 at $q = 2$, `Phi4Main.lean`), both from the $2$-adic
square-freeness of minimal forms (`SqFree.lean`). Hence the named input `WatsonMinimalTwoClasses` (Cassels App. A,
`AppA/WatsonTwoClasses.lean`) and the named statement `WatsonTwoClasses` hold, with standard axioms only, and so do
their consumers (`two_le_encard_genusClasses`, `magnus_two_le`).

*Not covered:* Watson's case $n = 11$ of (1.1) ($c_{11} \ge 2$), which uses his Lemma 13 and the case analysis of §10
beyond the bootstrap formalized here (Lemma 14 needs $n - 4 \ge 8$).
-/
import QuadFormsKB.Literature.Watson1963.Phi4Main
import QuadFormsKB.Literature.Cassels.AppB.StatementsAround

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms

/-- **Cassels, App. A, §3, p. 364, for the reduced genera (Watson 1963, (10.1)), unconditional:** every
Watson-minimal positive definite form in $n > 11$ variables has at least two classes in its genus
(`WatsonMinimalTwoClasses`). -/
@[kb "watson1963" "§10, (10.1), p. 567 (c(f) ≥ 2 for minimal f, n ≥ 12; unconditional)"]
theorem watsonMinimalTwoClasses_holds : WatsonMinimalTwoClasses :=
  watsonMinimalTwoClasses_of_twoAdic watsonLocalProbesTwo_holds watsonPhi4SplitTwo_holds

/-- **Watson's theorem (Watson 1963, Theorem 1 for $n \ge 12$; Cassels, App. A, §3, p. 364), unconditional:** every
genus of positive definite forms in $n > 11$ variables has at least two classes (`WatsonTwoClasses`). -/
@[kb "watson1963" "Theorem 1, (1.1), p. 549 (c_n ≥ 2 for n ≥ 12; unconditional)"]
theorem watsonTwoClasses_holds : WatsonTwoClasses :=
  watsonTwoClasses_of_minimal watsonMinimalTwoClasses_holds

/-- **Every genus of a positive definite integer-valued form in $n > 11$ variables has at least two classes**
(Cassels, App. A, §3, p. 364), unconditional. Arguments: `hn : 11 < n`, `hQ` positive definiteness. -/
@[kb "cassels1978" "App. A, §3, p. 364 (Watson: every genus in n > 11 variables has at least 2 classes; proved)"]
theorem two_le_encard_genusClasses {n : ℕ} (hn : 11 < n) {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) :
    (2 : ℕ∞) ≤ (genusClasses Q).encard :=
  watsonTwoClasses_holds.two_le_encard hn hQ

/-- **The second half of Magnus' statement** (Cassels, App. B, §3, p. 377), unconditional: every genus of positive
definite forms in $n \ge 35$ variables has at least two classes. -/
@[kb "cassels1978" "App. B, §3, p. 377 (every genus with n ≥ 35 has two classes; proved via Watson)"]
theorem magnus_two_le :
    ∀ (n : ℕ) (Q : QuadForm ℤ n), 35 ≤ n → IntQF.PosDef Q → (2 : ℕ∞) ≤ (genusClasses Q).encard :=
  Cassels.WatsonTwoClasses.magnus_two_le watsonTwoClasses_holds

end QuadFormsKB.Watson1963
