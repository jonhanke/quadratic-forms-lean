/-
# Siegel's formula for one number as a Tamagawa integral

**Layer:** number fields, definite case; the Tamagawa measure $\mu_{\mathbb A}$ on $SO(V)(\mathbb A)$ and the frame identity.

**Proves**
* `setLIntegral_repCount_frame`: for $Q_0$ totally positive definite over $\mathcal O_F$ in $N = n + 1 \ge 4$ variables, $m$
  totally positive, an adapted frame $Q_0\circ g = \langle m\rangle\perp Q_0'$ with the local orbital identity at every prime
  (the named input `OrbitalLocalIdentityAt`, the hypothesis of `two_mul_tamagawaK_mul_repMass_frame`), and any
  fundamental
  domain $D$ of $SO(V)(F)$ in $SO(V)(\mathbb A)$:
  $$\int_D r_{g_fL}(m)\,d\mu_{\mathbb A}(g) = \tau(SO(Q_0'))\cdot S(L, m).$$
  The left side is Weil's unfolded integral (Lemma 2.4.2, p. 26) computed adelically in `setLIntegral_repCount_one`
  ($= 2\,\mu_{\mathrm{Tam}}(K_{SO})\,\mathrm{repMass}$), with no reference to classes or orbit counting in its statement; the
  right side is the frame identity. This is a cross-check: the adelic reading of the left side of
  `two_mul_tamagawaK_mul_repMass_frame` agrees with the library's combinatorial one.

*Scope.* The right side is still derived through the library's lattice route. An adelic derivation of the right side
(fibring $SO(V)(\mathbb A)$ over the orbit of $\xi$ with fibre $SO(Q_0')(\mathbb A)$, Weil's Theorem 2.4.3) needs Haar measures on
$G/H$ for non-normal $H$, which Mathlib lacks; it is not attempted here.
-/
import QuadFormsKB.Tamagawa.Measure.AdelicRepMass
import QuadFormsKB.Tamagawa.SiegelAllRanks

open MeasureTheory
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa.ArchSOMeasure

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

/-- **Siegel's formula for one number as a Tamagawa integral** (cross-check of the adelic unfolding with the frame
identity): $\int_{SO(V)(F)\backslash SO(V)(\mathbb A)} r_{g_f\mathcal O_F^N}(m)\,d\mu_{\mathbb A} = \tau(SO(Q_0'))\cdot S(\mathcal O_F^N, m)$. -/
@[kb "weil1982" "§2.4, Lemma 2.4.2, p. 26; §4.5, p. 100 (Siegel's theorem, one number) [unverified]"]
theorem setLIntegral_repCount_frame (Q₀ : QuadForm (𝓞 F) (n + 1)) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (HilbertModular.formF Q₀)) (hn : 3 ≤ n) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < HilbertModular.realEmb F v (algebraMap (𝓞 F) F m))
    (fr : AdaptedFrame (HilbertModular.formF Q₀) (algebraMap (𝓞 F) F m))
    (hgli : ∀ v, OrbitalLocalIdentityAt v Q₀ fr)
    {D : Set (ArchSOProd (realQ Q₀) × SOAf Q₀)}
    (hD : IsFundamentalDomain (GammaSO Q₀) D (muAdele Q₀ hQ hpd fun _ => 1)) :
    ∫⁻ x in D, (repCount (HilbertModular.formF Q₀)
        (latSMul (HilbertModular.formF Q₀) (x.2 : OAf (HilbertModular.formF Q₀)) (stdLat F (n + 1)))
          (algebraMap (𝓞 F) F m) : ℝ≥0∞) ∂(muAdele Q₀ hQ hpd fun _ => 1) =
      ENNReal.ofReal (tauSO fr.Q' * siegelProduct Q₀ m) := by
  rw [setLIntegral_repCount_one Q₀ hQ (by omega) hpd (HilbertModular.isIntegral_stdLat Q₀) _ hD,
    two_mul_tamagawaK_mul_repMass_frame Q₀ hpd hn hm fr hgli]

end QuadFormsKB.Tamagawa.Measure
