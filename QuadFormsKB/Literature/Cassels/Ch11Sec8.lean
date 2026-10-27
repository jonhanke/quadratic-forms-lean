/-
# Cassels, Chapter 11, §8: spinor genera and equivalence away from one prime (Theorem 8.3)

**Layer:** $V = F^n$ over a number field $F$ with the form $Q$ = `Q : QuadForm F n` (Cassels: $F = \mathbb Q$);
lattices `Lat F n`, their localizations `loc v L.1`; the proper spinor genus `SameProperSpinorGenus` (Cassels'
spinor genus); strong approximation for the spinor kernel away from a prime $\mathfrak q$ at which $V$ is isotropic
(`strongApproximationSpinAt`, unconditional; Cassels' Theorem 8.2).

**Proves** Cassels' Theorem 8.3 (p. 232) in the language of lattices: if $L$, $M$ are in the same (proper) spinor
genus, $n \ge 3$, and $V$ is isotropic at the finite prime $\mathfrak q$, then there is a rotation $\sigma \in O^+(V)$
with $\sigma L_\mathfrak p = M_\mathfrak p$ at every finite prime $\mathfrak p \ne \mathfrak q$
(`exists_soSub_locAct_eq_of_sameProperSpinorGenus`). Over $\mathbb Q$ this says that the $\mathbb Z[1/q]$-lattices
$L[1/q]$ and $M[1/q]$ are properly equivalent (a $\mathbb Z[1/q]$-lattice is determined by its localizations at the
primes $p \ne q$), i.e. Cassels' "$f$, $g$ are properly equivalent over $\mathbb Z^{(q)}$".
-/
import QuadFormsKB.Literature.OMeara.Sec102
import QuadFormsKB.Lattices.SATernaryAway

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- **Cassels, Theorem 8.3** (Ch. 11, p. 232): *let $f, g$ be two integral forms in the same spinor genus and in
$n \ge 3$ variables. Suppose that they are isotropic over $\mathbb Q_q$ for some prime $q$. Then they are properly
equivalent over $\mathbb Z^{(q)}$.* In the language of lattices, over a number field: for $L$, $M$ in the same proper
spinor genus and $V_\mathfrak q$ isotropic there is $\sigma \in O^+(V)$ with $\sigma L_\mathfrak p = M_\mathfrak p$
for every finite prime $\mathfrak p \ne \mathfrak q$. *Proof* (Cassels: "as for Theorem 1.4 but using Theorem 8.2"):
$M = \gamma kL$ with $\gamma \in O^+(V)$ and $k$ in the adelic spinor kernel; strong approximation away from
$\mathfrak q$ gives $\alpha$ in the spinor kernel of $O(V)$ with $(\alpha^{-1}k)_\mathfrak pL_\mathfrak p =
L_\mathfrak p$ for $\mathfrak p \ne \mathfrak q$; take $\sigma = \gamma\alpha$. Integrality of the forms is not needed. -/
@[kb "cassels1978" "Ch. 11, Thm. 8.3, p. 232 (lattice form, over a number field)"]
theorem exists_soSub_locAct_eq_of_sameProperSpinorGenus (hn : 3 ≤ n) (hQ : Q.Nondegenerate)
    (q : HeightOneSpectrum (𝓞 F)) (hq : Q.IsotropicIn (q.adicCompletion F)) {L M : Lat F n}
    (h : SameProperSpinorGenus Q L M) :
    ∃ σ ∈ Tamagawa.soSub Q F, ∀ w : HeightOneSpectrum (𝓞 F), w ≠ q →
      locAct w ((orthMap Q (w.adicCompletion F) σ : orthGroup Q _) : GL (Fin n) _) (loc w L.1) = loc w M.1 := by
  obtain ⟨γ, hγ, k, hk, rfl⟩ := (sameProperSpinorGenus_iff Q).mp h
  obtain ⟨α, hα, hαL⟩ := strongApproximationSpinAt.approx Q hn hQ q hq L k hk
  refine ⟨γ * α, (Tamagawa.soSub Q F).mul_mem hγ (spinorKernel_le_soSub Q F hα), fun w hw => ?_⟩
  have hkw : locAct w (((k w : orthGroup Q _)) : GL (Fin n) _) (loc w L.1) =
      locAct w ((orthMap Q (w.adicCompletion F) α : orthGroup Q _) : GL (Fin n) _) (loc w L.1) := by
    have e := hαL w hw
    have hsplit : (((diagF Q α)⁻¹ * k) w : orthGroup Q _) = (orthMap Q _ α)⁻¹ * k w := rfl
    rw [hsplit, Subgroup.coe_mul, locAct_mul, Subgroup.coe_inv] at e
    have e' := congrArg (locAct w ((orthMap Q (w.adicCompletion F) α : orthGroup Q _) : GL (Fin n) _)) e
    rwa [← locAct_mul, mul_inv_cancel, locAct_one] at e'
  rw [loc_latSMul, loc_latSMul, hkw, ← locAct_mul, map_mul, Subgroup.coe_mul]
  rfl

end QuadFormsKB.Lattices
