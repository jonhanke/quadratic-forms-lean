/-
# Cassels, Chapter 10, Theorem 7.1: the named statement is proved

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Ch. 10, §7, Theorem 7.1 (p. 186) and its proof (pp. 187–190).

**Proves** `spinStrongApproximation_holds : SpinStrongApproximation` (`Ch10/Thm71.lean`), unconditionally, following Cassels'
own proof:
* $n = 3$: `Thm71Ternary.spinStrongApproximation_three` (p. 188: the even Clifford algebra and the quaternary norm form, with
  Lemma 7.1);
* $n \ge 4$: `Thm71Five.spinStrongApproximation_four_le` (pp. 189–190: the first stage, products of approximated vectors with
  $\prod\phi(a_j) = 1$, `Thm71Five.firstStage`; the second stage, Lemma 3.4 and Lemma 7.2, `Thm71Five.lemma72`).
Lemma 7.1 (p. 187) is `Thm71Approx.lemma71` (from Ch. 9, Theorem 1.5, `Siegel.exists_rep_approx`).
(`Thm71Five.spinStrongApproximation_five` is the shorter proof for $n \ge 5$, where the second stage alone suffices.)
-/
import QuadFormsKB.Literature.Cassels.Ch10.Thm71FourFinal

open CliffordAlgebra TensorProduct

namespace QuadFormsKB.Cassels

/-- **Cassels, Ch. 10, Theorem 7.1** (Strong Approximation Theorem for the Spin Group, p. 186): the named statement
`SpinStrongApproximation` holds. Proof: Cassels' (module docstring). -/
@[kb "cassels1978" "Ch. 10, Thm. 7.1, p. 186; proof pp. 187–190"]
theorem spinStrongApproximation_holds : SpinStrongApproximation := by
  refine ⟨fun V _ _ _ Q hn hQ hind Λ hfg hspan U hne hopen hcof => ?_⟩
  rcases Nat.lt_or_ge (Module.finrank ℚ V) 4 with h | h
  · exact Thm71Ternary.spinStrongApproximation_three V Q (by omega) hQ hind Λ hfg hspan U hne hopen hcof
  · exact Thm71Five.spinStrongApproximation_four_le Q h hQ hind Λ hfg hspan U hne hopen hcof

end QuadFormsKB.Cassels
