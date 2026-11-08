/-
# Watson (1963): what remains is the prime 2

`Reduced.lean` derives Watson's theorem from `WatsonLocalProbesTwo` and `WatsonQuaternaryLocal`. Here
`WatsonQuaternaryLocal` is proved except for one case: Watson's $g(4, p_0^2)$ exists for every prime $p_0$
(`exists_quaternary`), it splits off a minimal form over every $\mathbb Z_p$ with $p$ odd (`quaternary_split_odd`)
and over $\mathbb Z_2$ when $p_0$ is odd (`quaternary_split_two`). The remaining case $p_0 = p = 2$, where
$g = \Phi_4$ ($D_4$), is the named input `WatsonPhi4SplitTwo`.

So Watson's theorem (`watsonTwoClasses_of_twoAdic`) is conditional on two statements about $\mathbb Z_2$ only:
`WatsonLocalProbesTwo` and `WatsonPhi4SplitTwo`, both consequences of the $2$-adic structure of minimal forms
(Watson 1963, §3, including the case (3.3)).
-/
import QuadFormsKB.Literature.Watson1963.Reduced
import QuadFormsKB.Literature.Watson1963.Quaternary
import QuadFormsKB.Literature.Watson1963.QuaternaryOdd
import QuadFormsKB.Literature.Watson1963.TwoAdicSplit

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms

/-- **Watson 1963, Lemma 14 at $p = q = 2$ (Lemmas 1, 9: $g(4, 4) = \Phi_4$, p. 560)** (named input): a Watson-minimal
positive definite form $f$ in $4 + m$ variables, $m \ge 8$, with $r_2(f) \le 9$ splits off $\Phi_4$ (`phiD 3`, the
root lattice $D_4$) over $\mathbb Z_2$: $f \cong \Phi_4 \perp \psi_2$. Proved in `Phi4Main.lean`
(`watsonPhi4SplitTwo_holds`), from the $2$-adic square-freeness of minimal forms. -/
@[kb "watson1963" "§9, Lemma 14 with q = 2 (g(4,4) = Φ₄ splits off over ℤ₂), pp. 560, 565"]
structure WatsonPhi4SplitTwo : Prop where
  /-- The splitting over $\mathbb Z_2$, for Watson-minimal positive definite `f` in `4 + m` variables, `m ≥ 8`, with
  `rankModP 2 f ≤ 9`. -/
  split : ∀ (m : ℕ) (f : QuadForm ℤ (4 + m)), IntQF.PosDef f → IsWatsonMinimal f → 8 ≤ m → rankModP 2 f ≤ 9 →
    ∃ ψ : QuadForm ℤ_[2] m,
      IsometricGL (f.map (Int.castRingHom ℤ_[2])) (QuadForm.orthSum ((phiD 3).map (Int.castRingHom ℤ_[2])) ψ)

/-- Helper: $r_p(\Phi_4) \ge 2$ for every prime $p$ ($\det H = 4$; $r_2 = 2$). -/
theorem two_le_rankModP_phiD3 (p : ℕ) [hp : Fact p.Prime] : 2 ≤ rankModP p (phiD 3) := by
  by_cases h2 : p = 2
  · subst h2; rw [rankModP_two_phiD3]
  · rw [rankModP_eq_of_det p (d := 4) (by rw [phiD_hessian_det]; rfl) ?_]
    · norm_num
    · intro hd
      have : p ∣ 2 * 2 := hd
      rcases (Nat.Prime.dvd_mul hp.out).mp this with h | h <;>
        exact h2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)

/-- **`WatsonQuaternaryLocal` from its case $p_0 = p = 2$:** Watson's $g(4, p_0^2)$ (`exists_quaternary`, and
$\Phi_4$ for $p_0 = 2$) splits off over every $\mathbb Z_p$ by `quaternary_split_odd` ($p$ odd) and
`quaternary_split_two` ($p = 2$, $p_0$ odd); the case $p_0 = p = 2$ is the input. -/
theorem watsonQuaternaryLocal_of_phi4 (h : WatsonPhi4SplitTwo) : WatsonQuaternaryLocal := by
  refine ⟨fun m f hf hmin hm p₀ _ hr => ?_⟩
  by_cases h2 : p₀ = 2
  · subst h2
    refine ⟨phiD 3, phiD_posDef 3 (by norm_num), fun p _ => two_le_rankModP_phiD3 p, phiD3_rad2, fun p _ => ?_⟩
    by_cases hp : p = 2
    · subst hp
      exact h.split m f hf hmin hm hr
    · exact quaternary_split_odd hf hmin hm hr (by rw [phiD_hessian_det]; norm_num) rankModP_two_phiD3 p hp
  · obtain ⟨g, hg, hdet, hgq, hg2, hrad⟩ := exists_quaternary p₀
    refine ⟨g, hg, hg2, hrad, fun p _ => ?_⟩
    by_cases hp : p = 2
    · subst hp
      refine quaternary_split_two hf hmin hm ?_
      rw [hdet]
      intro hd
      have h2' : (2 : ℤ) ∣ (p₀ : ℤ) := Int.prime_two.dvd_of_dvd_pow hd
      have : (2 : ℕ) ∣ p₀ := by exact_mod_cast h2'
      exact h2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out)).mp this).symm
    · exact quaternary_split_odd hf hmin hm hr hdet hgq p hp

/-- **Watson's theorem for the reduced genera, conditional on $2$-adic statements only** (Cassels, App. A, §3,
p. 364; Watson 1963, Theorem 1 for $n \ge 12$): `WatsonLocalProbesTwo` and `WatsonPhi4SplitTwo` imply
`WatsonMinimalTwoClasses`. -/
@[kb "watson1963" "§10, (10.1), p. 567 (c(f) ≥ 2 for n ≥ 12; minimal forms; inputs at p = 2 only)"]
theorem watsonMinimalTwoClasses_of_twoAdic (h2 : WatsonLocalProbesTwo) (h4 : WatsonPhi4SplitTwo) :
    WatsonMinimalTwoClasses :=
  watsonMinimalTwoClasses_of_reduced h2 (watsonQuaternaryLocal_of_phi4 h4)

/-- **Watson's theorem, conditional on $2$-adic statements only:** every genus of positive definite forms in $n > 11$
variables has at least two classes (Cassels, App. A, §3, p. 364), from `WatsonLocalProbesTwo` and
`WatsonPhi4SplitTwo`. -/
@[kb "watson1963" "Theorem 1, (1.1), p. 549 (c_n ≥ 2 for n ≥ 12; inputs at p = 2 only)"]
theorem watsonTwoClasses_of_twoAdic (h2 : WatsonLocalProbesTwo) (h4 : WatsonPhi4SplitTwo) : WatsonTwoClasses :=
  watsonTwoClasses_of_minimal (watsonMinimalTwoClasses_of_twoAdic h2 h4)

end QuadFormsKB.Watson1963
