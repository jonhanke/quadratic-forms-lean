/-
# O'Meara §71A: a finite extension is unramified almost everywhere (71:7)

**Setting.** $H/F$ a finite extension of number fields (`[Algebra F H]`), with rings of integers $\mathcal O_F$,
$\mathcal O_H$. For a prime $\mathfrak P$ of $\mathcal O_H$ (`HeightOneSpectrum (𝓞 H)`), the ramification index
$e(\mathfrak P \mid \mathfrak p)$ over the prime $\mathfrak p = \mathfrak P \cap \mathcal O_F$ below it is Mathlib's
`Ideal.ramificationIdx 𝔓 (𝓞 F)`. O'Meara calls $H/F$ *unramified at* $\mathfrak P$ if $H_\mathfrak P/F_\mathfrak p$ is an
unramified extension of local fields, i.e. $e(\mathfrak P \mid \mathfrak p) = 1$ (the residue fields are finite, so
separability is automatic).

**Proves**
* `finite_setOf_ramificationIdx_ne_one` (**71:7**): $e(\mathfrak P \mid \mathfrak p) = 1$ for all but finitely many primes
  $\mathfrak P$ of $\mathcal O_H$.

**Proof notes.** The book uses the discriminant of a primitive element and Proposition 32:6. Here: if $\mathfrak P$ lies
over a rational prime $p \nmid \operatorname{disc} H$, then $p$ is unramified in $\mathcal O_H$
(`NumberField.not_dvd_discr_iff_isUnramifiedIn`), so $e(\mathfrak P \mid p) = 1$, and by the tower formula
$e(\mathfrak P \mid p) = e(\mathfrak p \mid p)\,e(\mathfrak P \mid \mathfrak p)$ also $e(\mathfrak P \mid \mathfrak p) = 1$.
Only finitely many primes $\mathfrak P$ lie over the finitely many $p \mid \operatorname{disc} H$.
-/
import Mathlib
import QuadFormsKB.Citation

open NumberField IsDedekindDomain

noncomputable section

namespace QuadFormsKB.OMeara

/-- **Proposition 71:7** (O'Meara 1963, p. 192): a finite extension $H/F$ of algebraic number fields is unramified at
almost all discrete spots $\mathfrak P$ of $H$: the ramification index $e(\mathfrak P \mid \mathfrak P \cap \mathcal O_F)$
is $1$ for all but finitely many nonzero primes $\mathfrak P$ of $\mathcal O_H$. -/
@[kb "omeara1963" "§71A, 71:7, p. 192"]
theorem finite_setOf_ramificationIdx_ne_one (F H : Type*) [Field F] [NumberField F] [Field H] [NumberField H]
    [Algebra F H] :
    {P : HeightOneSpectrum (𝓞 H) | P.asIdeal.ramificationIdx (𝓞 F) ≠ 1}.Finite := by
  classical
  set D := discr H
  -- the primes of `𝓞 H` over the rational primes dividing the discriminant
  have hfin : (⋃ p ∈ (D.natAbs.primeFactors : Set ℕ),
      {P : HeightOneSpectrum (𝓞 H) | P.asIdeal ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 H)}).Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun p hp => ?_
    have hp' : p.Prime := (Nat.mem_primeFactors.mp (Finset.mem_coe.mp hp)).1
    have : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp').irreducible
    exact ((IsDedekindDomain.primesOver_finite (Ideal.span {(p : ℤ)}) (𝓞 H)).preimage
      fun P _ Q _ h => HeightOneSpectrum.ext h)
  refine hfin.subset fun P hP => ?_
  simp only [Set.mem_ofPred_eq] at hP
  -- the rational prime below `P`
  have hbot : P.asIdeal.under ℤ ≠ ⊥ := mt Ideal.eq_bot_of_under_eq_bot P.ne_bot
  have hprime : (P.asIdeal.under ℤ).IsPrime := Ideal.IsPrime.under ℤ P.asIdeal
  set g := Submodule.IsPrincipal.generator (P.asIdeal.under ℤ)
  have hg : Prime g := Submodule.IsPrincipal.prime_generator_of_isPrime _ hbot
  have hspan : Ideal.span {g} = P.asIdeal.under ℤ := Ideal.span_singleton_generator _
  have hspan' : Ideal.span {((g.natAbs : ℕ) : ℤ)} = P.asIdeal.under ℤ := by
    rw [← hspan]
    exact (Ideal.span_singleton_eq_span_singleton.mpr (Int.associated_natAbs g)).symm
  have hp : g.natAbs.Prime := Int.prime_iff_natAbs_prime.mp hg
  have hpZ : Prime ((g.natAbs : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hlies : P.asIdeal.LiesOver (Ideal.span {((g.natAbs : ℕ) : ℤ)}) := ⟨hspan'⟩
  -- if `p ∤ disc H`, then `e(P | p) = 1`, hence `e(P | 𝔭) = 1`
  have hdvd : ((g.natAbs : ℕ) : ℤ) ∣ D := by
    by_contra hnd
    have hunr := (NumberField.not_dvd_discr_iff_isUnramifiedIn H (𝓞 H) hpZ).mp hnd
    have h1 : P.asIdeal.ramificationIdx ℤ = 1 := hunr.ramificationIdx_eq_one hlies
    have htow := Ideal.ramificationIdx_tower (R := ℤ) (P.asIdeal.under (𝓞 F)) P.asIdeal
    rw [h1] at htow
    exact hP (Nat.eq_one_of_mul_eq_one_left htow.symm)
  refine Set.mem_biUnion (x := g.natAbs) ?_ ⟨P.isPrime, hlies⟩
  simp only [Finset.mem_coe, Nat.mem_primeFactors]
  exact ⟨hp, Int.natCast_dvd.mp hdvd, Int.natAbs_ne_zero.mpr (discr_ne_zero H)⟩

end QuadFormsKB.OMeara
