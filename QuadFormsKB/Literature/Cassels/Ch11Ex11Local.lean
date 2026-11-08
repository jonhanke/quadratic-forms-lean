/-
# Cassels, Chapter 11, Example 11: the faithful (local) reading, a named statement

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, Example 11 (p. 253). Layer as in
`Ch11Ex11.lean`: $V = \mathbb Q^3$ with the form `Q : QuadForm ℚ 3`, the lattice $\Lambda$ = `L`, primes
`v : HeightOneSpectrum (𝓞 ℚ)`, $\Lambda_p$ = `loc v L.1`, $p\Lambda_p$ = `pLat v L`.

**The reading.** The printed congruence "$\alpha b \equiv \eta_p b \pmod{p\Lambda}$ (all $p \in P^*$)" is to be read in $\Lambda_p$:
$\alpha b - \eta_p b \in p\Lambda_p$. The global reading (`Ex11Statement`, `Ch11Examples3.lean`) is **false**
(`not_ex11Statement`, `Ch11Ex11Counter.lean`): it forces one rational vector $\alpha b$ to be close to $+b$ and to $-b$ at two
primes, which fails for $x_0^2 + x_1^2 + 57x_2^2$, $P^* = \{3, 19\}$. The local reading is the one used in the hint to Example 12.

**Status.** `Ex11StatementLocal` (the printed hypotheses, local congruence) is a *named statement*. It is proved under the
additional hypothesis (iii) of Chapter 10, Example 3 (every $p$-adic unit is a spinor norm of $O^+(\Lambda_p)$, for every $p$):
`Lattices.ex11_of_units` (`Ch11Ex11.lean`) has exactly the conclusion of `Ex11StatementLocal` under the hypotheses of
`Ex11StatementLocal` plus (iii). Whether (iii) can be dropped is open: the proof needs a global spinor norm $t$ that lies in
$\theta(O^+(\Lambda_w))$ at the finitely many primes $w \notin P^* \cup \{q\}$ dividing $2\det\Lambda$, and without (iii) these local
conditions together with those at $P^*$ need not be compatible with a global $t$ (only $q$ is free).
-/
import QuadFormsKB.Literature.Cassels.Ch11Ex11

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-- Helper (file-local): as in `Ch11Ex11.lean`, the library's algebra structure on $\mathbb Q_p$. -/
local instance (priority := high) algAdicEx11L (w : HeightOneSpectrum (𝓞 ℚ)) :
    Algebra ℚ (w.adicCompletion ℚ) := algAdicEx3 ℚ w

/-- **Cassels, Ch. 11, Example 11, local reading** (p. 253), a named statement. Field `holds`: for a regular ternary form
`Q` (`hQ`), a lattice `L` on which `Q` is integer-valued (`hint`), a prime `q` at which `Q` is isotropic (`hq`), a set `Pstar`
of odd primes (`h2`) at which `Q` is anisotropic (`hani`) and the determinant of $\Lambda_p$ has valuation exactly $1$ (`hdet`,
via a basis $\gamma$ of $\Lambda_p$), a vector $b \in \Lambda$ (`hb`) with $|Q(b)|_p = p^{-1}$ for $p \in P^*$ (`hbv`) and signs
$\eta_p = \pm 1$ (`hη`), there is a rotation $\alpha \in O^+(V)$ with $\alpha b - \eta_pb \in p\Lambda_p$ for $p \in P^*$ and
$\alpha\Lambda_w = \Lambda_w$ for every $w \ne q$. Proved under (iii) of Ch. 10, Ex. 3 by `ex11_of_units`. -/
@[kb "cassels1978" "Ch. 11, Ex. 11, p. 253 (local reading of the congruence)"]
structure Ex11StatementLocal : Prop where
  /-- Example 11, local reading. -/
  holds : ∀ (Q : QuadForm ℚ 3), Q.Nondegenerate → ∀ (L : Lat ℚ 3), (∀ x ∈ L.1, ∃ z : ℤ, Q.eval x = z) →
    ∀ (q : HeightOneSpectrum (𝓞 ℚ)), Q.IsotropicIn (q.adicCompletion ℚ) →
    ∀ (Pstar : Set (HeightOneSpectrum (𝓞 ℚ))),
      (∀ v ∈ Pstar, (2 : 𝓞 ℚ) ∉ v.asIdeal) →
      (∀ v ∈ Pstar, ¬ Q.IsotropicIn (v.adicCompletion ℚ)) →
      (∀ v ∈ Pstar, ∃ γ : GL (Fin 3) (v.adicCompletion ℚ), loc v L.1 = locAct v γ (std v) ∧
        Valued.v (locGram Q v γ).det = exp (-1 : ℤ)) →
      ∀ b : Fin 3 → ℚ, b ∈ L.1 →
      (∀ v ∈ Pstar, Valued.v (Q.evalIn (v.adicCompletion ℚ) (locVec v b)) = exp (-1 : ℤ)) →
      ∀ η : HeightOneSpectrum (𝓞 ℚ) → ℚ, (∀ v ∈ Pstar, η v = 1 ∨ η v = -1) →
      ∃ α ∈ Tamagawa.soSub Q ℚ,
        (∀ v ∈ Pstar, ((orthMap Q (v.adicCompletion ℚ) α : orthGroup Q _) : GL (Fin 3) (v.adicCompletion ℚ)).val *ᵥ
            locVec v b - algebraMap ℚ (v.adicCompletion ℚ) (η v) • locVec v b ∈ pLat v L) ∧
        ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ q →
          locAct w ((orthMap Q (w.adicCompletion ℚ) α : orthGroup Q _) : GL (Fin 3) (w.adicCompletion ℚ))
            (loc w L.1) = loc w L.1

/-- **Example 11 (local reading) for lattices with all unit spinor norms** (Cassels, Ch. 11, Ex. 11 with hypothesis (iii) of
Ch. 10, Ex. 3): the conclusion of `Ex11StatementLocal` for every `Q`, `L` satisfying, besides its hypotheses, `hU` (every
$p$-adic unit is a spinor norm of $O^+(\Lambda_p)$). This is `ex11_of_units`, restated with the arguments of
`Ex11StatementLocal`. -/
@[kb "cassels1978" "Ch. 11, Ex. 11, p. 253 (local reading, with (iii) of Ch. 10, Ex. 3)"]
theorem ex11Local_of_units (Q : QuadForm ℚ 3) (hQ : Q.Nondegenerate) (L : Lat ℚ 3)
    (hint : ∀ x ∈ L.1, ∃ z : ℤ, Q.eval x = z)
    (q : HeightOneSpectrum (𝓞 ℚ)) (hq : Q.IsotropicIn (q.adicCompletion ℚ))
    (hU : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v (u : v.adicCompletion ℚ) = 1 → u ∈ localSpinorNormGroup Q hQ v L)
    (Pstar : Set (HeightOneSpectrum (𝓞 ℚ)))
    (h2 : ∀ v ∈ Pstar, (2 : 𝓞 ℚ) ∉ v.asIdeal)
    (hani : ∀ v ∈ Pstar, ¬ Q.IsotropicIn (v.adicCompletion ℚ))
    (hdet : ∀ v ∈ Pstar, ∃ γ : GL (Fin 3) (v.adicCompletion ℚ), loc v L.1 = locAct v γ (std v) ∧
      Valued.v (locGram Q v γ).det = exp (-1 : ℤ))
    (b : Fin 3 → ℚ) (hb : b ∈ L.1)
    (hbv : ∀ v ∈ Pstar, Valued.v (Q.evalIn (v.adicCompletion ℚ) (locVec v b)) = exp (-1 : ℤ))
    (η : HeightOneSpectrum (𝓞 ℚ) → ℚ) (hη : ∀ v ∈ Pstar, η v = 1 ∨ η v = -1) :
    ∃ α ∈ Tamagawa.soSub Q ℚ,
      (∀ v ∈ Pstar, ((orthMap Q (v.adicCompletion ℚ) α : orthGroup Q _) : GL (Fin 3) (v.adicCompletion ℚ)).val *ᵥ
          locVec v b - algebraMap ℚ (v.adicCompletion ℚ) (η v) • locVec v b ∈ pLat v L) ∧
      ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ q →
        locAct w ((orthMap Q (w.adicCompletion ℚ) α : orthGroup Q _) : GL (Fin 3) (w.adicCompletion ℚ))
          (loc w L.1) = loc w L.1 :=
  ex11_of_units Q hQ L hint q hq hU Pstar h2 hani hdet b hb hbv η hη

end QuadFormsKB.Lattices
