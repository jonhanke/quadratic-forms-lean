/-
# Conway–Sloane Ch. 15, §9.7: unit square classes at small odd primes

Proves `isSquare_or_isSquare_neg_of_three_mod_four` (at $p \equiv 3 \pmod 4$ every $p$-adic unit is a square
or minus a square, since $-1$ is a non-residue mod $p$) and `isSquare_or_isSquare_two_mul_of_five` (at $p = 5$
every unit is a square or twice a square, since $2$ is a non-residue mod $5$). Both come from the general
`isSquare_or_isSquare_intCast_mul`: at an odd prime of $\mathbb Q$, if an integer $c$ is a non-residue then
every unit is a square or $c$ times a square (residue-field quadratic character plus Hensel lifting,
`exists_sq_of_residue_isSquare`). Used in the proofs of Thm. 20 (b) and Cor. 22.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.SphericalLocal
import QuadFormsKB.LocalDensity.NFLocal
import QuadFormsKB.LocalDensity.NFBridge
import QuadFormsKB.LocalDensity.NFLocalGeneral
import QuadFormsKB.Literature.Cassels.Ch11Thm13Int

open NumberField IsDedekindDomain

noncomputable section

namespace QuadFormsKB.ConwaySloane

/-- The residue field of the completion at a prime of $\mathbb Q$ has $p$ elements. -/
theorem card_residueField_rat (v : HeightOneSpectrum (𝓞 ℚ)) [Fintype (IsLocalRing.ResidueField
    (v.adicCompletionIntegers ℚ))] :
    Fintype.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) =
      Rat.HeightOneSpectrum.natGenerator v := by
  rw [← Nat.card_eq_fintype_card, HN.card_residueField, LocalDensity.NF.absNorm_rat]

/-- **Non-residue trick.** At an odd prime $p$ of $\mathbb Q$ (`natGenerator v ≠ 2`), if an integer $c$ is not a
square modulo $p$, then every $p$-adic unit $u$ is a square or $c$ times a square. -/
theorem isSquare_or_isSquare_intCast_mul (v : HeightOneSpectrum (𝓞 ℚ))
    (hp2 : Rat.HeightOneSpectrum.natGenerator v ≠ 2) (c : ℤ)
    (hc : ¬ IsSquare ((c : ℤ) : IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)))
    (u : (v.adicCompletion ℚ)ˣ) (hu : Valued.v (u : v.adicCompletion ℚ) = 1) :
    IsSquare (u : v.adicCompletion ℚ) ∨ IsSquare ((c : v.adicCompletion ℚ) * (u : v.adicCompletion ℚ)) := by
  classical
  have h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal := by
    rw [QuadFormsKB.Lattices.two_mem_iff_natGenerator]; exact hp2
  have hπ : ¬ LocalDensity.NF.π v ∣ 2 := LocalDensity.NF.π_not_dvd_two v h2
  let o : v.adicCompletionIntegers ℚ :=
    ⟨(u : v.adicCompletion ℚ), (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hu.le⟩
  have hoU : IsUnit o :=
    (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one (a := o)).mpr hu
  have ho0 : IsLocalRing.residue (v.adicCompletionIntegers ℚ) o ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit o).mpr hoU
  have hc0 : ((c : ℤ) : IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) ≠ 0 :=
    fun h => hc (h ▸ IsSquare.zero)
  have hcU : IsUnit ((c : ℤ) : v.adicCompletionIntegers ℚ) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_intCast]; exact hc0
  by_cases hs : IsSquare (IsLocalRing.residue (v.adicCompletionIntegers ℚ) o)
  · left
    obtain ⟨a, -, ha⟩ := LocalZeta.exists_sq_of_residue_isSquare v hπ hoU hs
    refine ⟨(a : v.adicCompletion ℚ), ?_⟩
    have := congrArg (fun x : v.adicCompletionIntegers ℚ => (x : v.adicCompletion ℚ)) ha
    simpa [sq] using this
  · right
    have hno : IsUnit ((c : ℤ) * o) := hcU.mul hoU
    have hsq : IsSquare (IsLocalRing.residue (v.adicCompletionIntegers ℚ) ((c : ℤ) * o)) := by
      rw [map_mul, map_intCast]
      have h1 := quadraticChar_neg_one_iff_not_isSquare.mpr hs
      have h2' := quadraticChar_neg_one_iff_not_isSquare.mpr hc
      refine (quadraticChar_one_iff_isSquare (mul_ne_zero hc0 ho0)).mp ?_
      rw [map_mul, h1, h2']; norm_num
    obtain ⟨a, -, ha⟩ := LocalZeta.exists_sq_of_residue_isSquare v hπ hno hsq
    refine ⟨(a : v.adicCompletion ℚ), ?_⟩
    have := congrArg (fun x : v.adicCompletionIntegers ℚ => (x : v.adicCompletion ℚ)) ha
    simpa [sq] using this

/-- At a prime $p \equiv 3 \pmod 4$ of $\mathbb Q$, every $p$-adic unit $u$ is a square or minus a square
(the unit square classes are $\{1, -1\}$). -/
@[kb "conwaysloane1999" "Ch. 15, §9.7, proof of Thm. 20 (b), p. 394 (-1 is a non-residue mod p)"]
theorem isSquare_or_isSquare_neg_of_three_mod_four (v : HeightOneSpectrum (𝓞 ℚ))
    (hp : Rat.HeightOneSpectrum.natGenerator v % 4 = 3) (u : (v.adicCompletion ℚ)ˣ)
    (hu : Valued.v (u : v.adicCompletion ℚ) = 1) :
    IsSquare (u : v.adicCompletion ℚ) ∨ IsSquare (-(u : v.adicCompletion ℚ)) := by
  classical
  have hm1 : ¬ IsSquare (-1 : IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) := by
    rw [FiniteField.isSquare_neg_one_iff, card_residueField_rat]; omega
  have := isSquare_or_isSquare_intCast_mul v (by omega) (-1) (by simpa using hm1) u hu
  simpa using this

/-- At $p = 5$ every $5$-adic unit $u$ is a square or twice a square ($2$ is a non-residue mod $5$). -/
@[kb "conwaysloane1999" "Ch. 15, §9.7, proof of Cor. 22, p. 395 (2 is a non-residue mod 5)"]
theorem isSquare_or_isSquare_two_mul_of_five (v : HeightOneSpectrum (𝓞 ℚ))
    (hp : Rat.HeightOneSpectrum.natGenerator v = 5) (u : (v.adicCompletion ℚ)ˣ)
    (hu : Valued.v (u : v.adicCompletion ℚ) = 1) :
    IsSquare (u : v.adicCompletion ℚ) ∨ IsSquare (2 * (u : v.adicCompletion ℚ)) := by
  classical
  have h2 : ¬ IsSquare (2 : IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) := by
    rw [FiniteField.isSquare_two_iff, card_residueField_rat, hp]; omega
  have := isSquare_or_isSquare_intCast_mul v (by omega) 2 (by simpa using h2) u hu
  simpa using this

end QuadFormsKB.ConwaySloane
