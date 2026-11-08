/-
# Watson (1963): the remaining local inputs, narrowed

`Main.lean` derives `WatsonMinimalTwoClasses` from two named inputs, `WatsonLocalProbes` and `WatsonQuaternarySplit`.
This file proves both from narrower named inputs that are purely local statements about $\mathbb Z_2$ and about
local splittings:

* `WatsonLocalProbes` holds at every odd prime (`localProbes_odd`, from the diagonal form of minimal forms at odd
  $p$, `exists_diag_of_minimal_odd`); what remains is the prime $2$: `WatsonLocalProbesTwo`.
* `WatsonQuaternarySplit` follows from the genus splitting theorem (`exists_sameGenus_orthSum`, Watson's Lemma 1)
  once the quaternary $g$ exists and splits off over every $\mathbb Z_p$: `WatsonQuaternaryLocal`.

Hence `watsonMinimalTwoClasses_of_reduced`: `WatsonLocalProbesTwo` and `WatsonQuaternaryLocal` imply
`WatsonMinimalTwoClasses` and so Watson's theorem `WatsonTwoClasses`.
-/
import QuadFormsKB.Literature.Watson1963.Main
import QuadFormsKB.Literature.Watson1963.Splitting
import QuadFormsKB.Literature.Watson1963.ProbesOdd

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms

/-- **Watson 1963, Lemma 2, local part ((4.12), (4.15)–(4.16), pp. 555–556), at $p = 2$, for the perfect forms of
§8** (named input): a Watson-minimal positive definite form $f$ in $n \ge 12$ variables represents over
$\mathbb Z_2$ the forms $A_5$, $\Phi_5$ if $r_2(f) \ge 6$; $A_6$, $\Phi_6$ if $r_2(f) \ge 7$; $E_7$ if $r_2(f) \ge 8$;
$E_8$ if $r_2(f) \ge 9$; $\Phi_9$ if $r_2(f) \ge 10$. (The odd primes are proved: `localProbes_odd`.) Proved in
`ProbesTwo.lean` (`watsonLocalProbesTwo_holds`), from the $2$-adic square-freeness of minimal forms (`SqFree.lean`)
and the classification of even unimodular $\mathbb Z_2$-forms. -/
@[kb "watson1963" "§4, Lemma 2, (4.12), (4.15)–(4.16), pp. 555–556 (local representations at p = 2)"]
structure WatsonLocalProbesTwo : Prop where
  /-- The representations over $\mathbb Z_2$, for Watson-minimal positive definite `f` in `n ≥ 12` variables. -/
  rep : ∀ (n : ℕ) (f : QuadForm ℤ n), IntQF.PosDef f → IsWatsonMinimal f → 12 ≤ n →
      (6 ≤ rankModP 2 f → RepOver ℤ_[2] f (phiA 5) ∧ RepOver ℤ_[2] f (phiD 4)) ∧
      (7 ≤ rankModP 2 f → RepOver ℤ_[2] f (phiA 6) ∧ RepOver ℤ_[2] f (phiD 5)) ∧
      (8 ≤ rankModP 2 f → RepOver ℤ_[2] f formE7) ∧
      (9 ≤ rankModP 2 f → RepOver ℤ_[2] f formE8) ∧
      (10 ≤ rankModP 2 f → RepOver ℤ_[2] f (phiD 8))

/-- **`WatsonLocalProbes` from its case $p = 2$** (the odd primes are `localProbes_odd`). -/
theorem watsonLocalProbes_of_two (h : WatsonLocalProbesTwo) : WatsonLocalProbes := by
  refine ⟨fun n f hf hmin hn p hp => ?_⟩
  by_cases h2 : p = 2
  · subst h2
    exact h.rep n f hf hmin hn
  · exact localProbes_odd hf hmin hn p h2

/-- **Watson 1963, Lemmas 9, 10, 14, local part (pp. 559–565)** (named input): let $f$ be a Watson-minimal positive
definite form in $4 + m$ variables, $m \ge 8$, with $r_{p_0}(f) \le 9$ for a prime $p_0$. Then there is a positive
definite quaternary form $g$ (Watson's $g(4, p_0^2)$, Lemma 9) with $r_p(g) \ge 2$ for every prime $p$, whose reduction
modulo $2$ vanishes on the radical of its polar form (Watson's (4.1)), such that over every $\mathbb Z_p$,
$f \cong g \perp \psi_p$ for some form $\psi_p$ over $\mathbb Z_p$ (Lemma 14: the local conditions (4.2)–(4.4) of
Lemma 1). The passage from these local splittings to a global $\psi$ is proved (`exists_sameGenus_orthSum`). Not
proved here: the construction of $g(4, p_0^2)$ and the local splittings (the $p$-adic invariants of §3). -/
@[kb "watson1963" "§7, Lemmas 9, 10, and §9, Lemma 14, pp. 559–565 (g(4, p²) splits off locally)"]
structure WatsonQuaternaryLocal : Prop where
  /-- The quaternary `g` and the local splittings, for Watson-minimal positive definite `f` in `4 + m` variables,
  `m ≥ 8`, and a prime `p₀` with `rankModP p₀ f ≤ 9`. -/
  split : ∀ (m : ℕ) (f : QuadForm ℤ (4 + m)), IntQF.PosDef f → IsWatsonMinimal f → 8 ≤ m →
    ∀ (p₀ : ℕ) [Fact p₀.Prime], rankModP p₀ f ≤ 9 →
      ∃ g : QuadForm ℤ 4, IntQF.PosDef g ∧
        (∀ (p : ℕ) [Fact p.Prime], 2 ≤ rankModP p g) ∧
        (∀ x : Fin 4 → ZMod 2, (∀ z, x ⬝ᵥ (g.hessian.map (algebraMap ℤ (ZMod 2)) *ᵥ z) = 0) →
          g.evalIn (ZMod 2) x = 0) ∧
        ∀ (p : ℕ) [Fact p.Prime], ∃ ψp : QuadForm ℤ_[p] m,
          IsometricGL (f.map (Int.castRingHom ℤ_[p])) (QuadForm.orthSum (g.map (Int.castRingHom ℤ_[p])) ψp)

/-- **`WatsonQuaternarySplit` from the local splittings** (Watson's Lemma 1: `exists_sameGenus_orthSum`). -/
theorem watsonQuaternarySplit_of_local (h : WatsonQuaternaryLocal) : WatsonQuaternarySplit := by
  refine ⟨fun n f hf hmin hn p₀ _ hr => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 + m := ⟨n - 4, by omega⟩
  obtain ⟨g, hg, hg2, hgrad, hloc⟩ := h.split m f hf hmin (by omega) p₀ hr
  obtain ⟨ψ, -, hgen⟩ := exists_sameGenus_orthSum hf hg hloc
  exact ⟨g, m, ψ, hg, hg2, hgrad, fun p _ => hgen.isoOver_padic p, hgen.isoOver_real⟩

/-- **Watson's theorem for the reduced genera, from the narrowed local inputs** (Cassels, App. A, §3, p. 364;
Watson 1963, Theorem 1 for $n \ge 12$): `WatsonLocalProbesTwo` and `WatsonQuaternaryLocal` imply
`WatsonMinimalTwoClasses`. -/
@[kb "watson1963" "§10, (10.1), p. 567 (c(f) ≥ 2 for n ≥ 12; minimal forms; narrowed inputs)"]
theorem watsonMinimalTwoClasses_of_reduced (h2 : WatsonLocalProbesTwo) (hq : WatsonQuaternaryLocal) :
    WatsonMinimalTwoClasses :=
  watsonMinimalTwoClasses_of_local (watsonLocalProbes_of_two h2) (watsonQuaternarySplit_of_local hq)

/-- **Watson's theorem from the narrowed local inputs:** every genus of positive definite forms in $n > 11$ variables
has at least two classes (Cassels, App. A, §3, p. 364), conditional on `WatsonLocalProbesTwo` and
`WatsonQuaternaryLocal`. -/
@[kb "watson1963" "Theorem 1, (1.1), p. 549 (c_n ≥ 2 for n ≥ 12; narrowed inputs)"]
theorem watsonTwoClasses_of_reduced (h2 : WatsonLocalProbesTwo) (hq : WatsonQuaternaryLocal) : WatsonTwoClasses :=
  watsonTwoClasses_of_minimal (watsonMinimalTwoClasses_of_reduced h2 hq)

end QuadFormsKB.Watson1963
