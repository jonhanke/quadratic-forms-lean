/-
# Shimura 2004, Theorem 10.5 split by the dimension of the core subspace

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Theorem 10.5 (printed p. 96);
the core subspace of §6.1 (a maximal anisotropic subspace $Z$ in a Witt decomposition $V = Z \oplus
\sum_i(Fe_i + Ff_i)$).

**Why.** Theorem 10.5 (`Theorem10_5`) is the only input left in Shimura's Theorem 11.6 and (13.18)
(`Theorem116.lean`). Its proof is by the structure of a $\mathfrak g$-maximal lattice
$L = M \oplus \sum_i(\mathfrak g e_i + \mathfrak g f_i)$ with $M$ the maximal lattice of the core subspace $Z$
(the structure theory of maximal lattices in the book's §§6–8), and depends on
$t = \dim Z = n - 2\,\mathrm{ind}\,V$, which over a
nonarchimedean local field is $0, 1, 2, 3$ or $4$. This file splits the input into one statement per value of $t$,
so that each can be proved (or cited) separately.

**Defines** `Theorem10_5Core t`: Theorem 10.5 for the spaces whose core subspace has dimension $t$
(`finrank V - 2 * QuadraticForm.wittIndex Q = t`, the library's Witt index of `Witt/Decomposition.lean`), and the
named inputs `LocalTheorem10_5Core t` (structures).

**Proves** (standard axioms only) `localTheorem10_5_of_cores`: the five statements $t = 0, 1, 2, 3$ and $t \ge 4$
give `LocalTheorem10_5` (Theorem 10.5 in general). (Over a nonarchimedean local field every space of dimension
$\ge 5$ is isotropic, so the case $t \ge 5$ is empty; it is kept inside the last statement so that no bound on $t$ has
to be proved here.)
-/
import QuadFormsKB.Literature.Shimura2004.Fundamental.Local
import QuadFormsKB.Witt.Decomposition
import QuadFormsKB.Citation

open Module QuadraticMap

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.OMeara

/-- **Theorem 10.5 for core dimension $t$** (Shimura 2004, p. 96): the statement `Theorem10_5` restricted to the
spaces $(V, \varphi)$ over the completion $F_v$ of a number field whose core subspace has dimension $t$, i.e.
$\dim V - 2\,\mathrm{ind}\,V = t$ (`QuadraticForm.wittIndex`), with the corrected exceptional clause of `Theorem10_5`.
*Proved* (`theorem10_5Core_holds`, `Fundamental/Theorem105.lean`). -/
@[kb "shimura2004" "Thm. 10.5, p. 96 (spaces with core subspace of dimension t)"]
def Theorem10_5Core (t : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (V : Type) [AddCommGroup V] [Module (v.adicCompletion K) V] [FiniteDimensional (v.adicCompletion K) V]
    [Module (v.adicCompletionIntegers K) V] [IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) V]
    (_ : Invertible (2 : v.adicCompletion K))
    (Q : QuadraticForm (v.adicCompletion K) V), (QuadraticMap.associated Q).Nondegenerate →
    finrank (v.adicCompletion K) V - 2 * QuadraticForm.wittIndex Q = t →
    1 < finrank (v.adicCompletion K) V → Cond81 (v.adicCompletionIntegers K) Q →
    ∀ L : Submodule (v.adicCompletionIntegers K) V, IsMaximal Q 1 L →
    ∀ h k : V, Q h = Q k → Q h ≠ 0 → phiIdeal Q h L = phiIdeal Q k L →
      let exceptional : Prop := finrank (v.adicCompletion K) V = 2 ∧ (∃ x ≠ 0, Q x = 0) ∧
        ∃ y ∈ L, Valued.v (Q h) < Valued.v (2 * bil Q h y) ^ 2
      (¬ exceptional → ∃ γ ∈ orthLatPlus Q L, γ h = k) ∧
      (exceptional → ∃ α ∈ orthLat Q L, α h = k)

/-- **Theorem 10.5 for core dimension $t$** (`Theorem10_5Core t`), as a named structure (formerly a cited input;
proved: `localTheorem10_5Core_holds`, `Fundamental/Theorem105.lean`). -/
@[kb "shimura2004" "Thm. 10.5, p. 96 (core dimension t, as an input)"]
structure LocalTheorem10_5Core (t : ℕ) : Prop where
  holds : Theorem10_5Core t

/-- **Theorem 10.5 from its five core-dimension cases**: the statements for $t = 0, 1, 2, 3$ and for every
$t \ge 4$ give `LocalTheorem10_5`. -/
theorem localTheorem10_5_of_cores (h0 : LocalTheorem10_5Core 0) (h1 : LocalTheorem10_5Core 1)
    (h2 : LocalTheorem10_5Core 2) (h3 : LocalTheorem10_5Core 3) (h4 : ∀ t, 4 ≤ t → LocalTheorem10_5Core t) :
    LocalTheorem10_5 := by
  refine ⟨fun K _ _ v V _ _ _ _ _ inst Q hnd => ?_⟩
  have hall : ∀ t, LocalTheorem10_5Core t := fun t => by
    rcases Nat.lt_or_ge t 4 with ht | ht
    · interval_cases t
      · exact h0
      · exact h1
      · exact h2
      · exact h3
    · exact h4 t ht
  exact (hall _).holds K v V inst Q hnd rfl

/-- **Theorem 10.5 for each core dimension** $t$, proved (a special case of `theorem10_5_holds`). -/
theorem theorem10_5Core_holds (t : ℕ) : Theorem10_5Core t :=
  fun K _ _ v V _ _ _ _ _ inst Q hnd _ hn1 h81 L hL h k hQ hQ0 hφ =>
    theorem10_5_holds K v V inst Q hnd hn1 h81 L hL h k hQ hQ0 hφ

/-- **The named structure `LocalTheorem10_5Core t` holds** for every $t$. -/
@[kb "shimura2004" "Thm. 10.5, p. 96 (core dimension t; proved)"]
theorem localTheorem10_5Core_holds (t : ℕ) : LocalTheorem10_5Core t := ⟨theorem10_5Core_holds t⟩

end QuadFormsKB.Shimura2004
