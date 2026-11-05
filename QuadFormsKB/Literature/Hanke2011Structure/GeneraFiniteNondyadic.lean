/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Mathlib
import QuadFormsKB.Literature.Hanke2011Structure.RationalityNondyadicSeries
import QuadFormsKB.Literature.Hanke2011Structure.RationalityTwoFinite
import QuadFormsKB.Literature.Hanke2011Structure.BinaryMassTable

/-!
# Finiteness of the local genera of given determinant at $\mathfrak p \nmid 2$; Lemma 7.8 and Thm. 7.11 for $n = 2$

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), §4 (the local sums $A^*_{\mathfrak p;n}$, $B^*_{\mathfrak p;n}$ are finite sums),
Lemma 7.8 (p. 32) and Thm. 7.11 (p. 33).

* `genera_finite_nd`: for a finite prime $\mathfrak p \nmid 2$ of a number field $F$, every rank $n$ and every
  $S \in \mathrm{SqCl}(F_{\mathfrak p}^\times, \mathcal O_{\mathfrak p}^\times)$, the set of nondegenerate local genera
  $G$ of rank $n$ with $\det_H G = S$ is finite.  *Proof:* every such genus is the genus of a diagonal form
  $\operatorname{diag}(\pi^{z_i}\operatorname{rep}(x_i))$ (`exists_genND`) with $\sum_iz_i = \operatorname{ord}(S)$
  (`det_genND_iff`), and there are finitely many such $(z, x)$ (O'Meara 92:2, the paper's p. 23).
* `BinaryDyadicGeneraFinite F`: the named input `BinaryLocalGeneraFinite F` restricted to the dyadic primes
  $\mathfrak p \mid 2$ (the remaining open part); `binaryLocalGeneraFinite_of_dyadic` recovers the full input.
* `binaryLocalGeneraFinite_rat`: over $\mathbb Q$ the input holds (odd primes here, $p = 2$ by Conway–Sloane's 2-adic
  Jordan decompositions, `RatTwo.admGen_finite_two`).
* So **Lemma 7.8 for $n = 2$ over $\mathbb Q$ is unconditional** (`lemma_7_8_two_rat`), Lemma 7.8 and Thm. 7.11 over a
  totally real $F$ are conditional only on the dyadic part (`lemma_7_8_two_dyadic`, `theorem_7_11_two_dyadic`), and
  Thm. 7.11 over $\mathbb Q$ only on the tables (`theorem_7_11_two_rat`).

Indices are 0-based.
-/

open Finset Matrix IsDedekindDomain NumberField

namespace QuadFormsKB.Hanke2011Structure.RatND

open QuadFormsKB QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.Hanke2011Structure
  QuadFormsKB.Hanke2011Structure.RatOdd QuadFormsKB.ConwaySloane QuadFormsKB.Odd7 QuadFormsKB.Siegel

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

section NF

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

local notation "𝔬" => v.adicCompletionIntegers F

/-- **The nondegenerate local genera of given determinant at $\mathfrak p \nmid 2$ are finitely many** (every rank
$n$, every number field). -/
@[kb "omeara1963" "§92, 92:2, p. 247 (finitely many local integral classes of given discriminant, p ∤ 2)"]
theorem genera_finite_nd (hv : (2 : 𝓞 F) ∉ v.asIdeal) (n : ℕ) (S : LocalSqCl v) :
    {G : LocGenus v n | G.Nondeg ∧ G.det = S}.Finite := by
  obtain ⟨c, hcU, hc⟩ := exists_nonres_nf hv
  by_cases hne : {G : LocGenus v n | G.Nondeg ∧ G.det = S}.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hne; rw [hne]; exact Set.finite_empty
  obtain ⟨G₁, hN₁, hd₁⟩ := hne
  obtain ⟨z₁, x₁, rfl⟩ := exists_genND hv hcU hc G₁ hN₁
  set N := ∑ i, z₁ i
  let f : (Fin n → Fin (N + 1)) × (Fin n → ℤˣ) → LocGenus v n := fun p => genND v c (fun i => (p.1 i : ℕ)) p.2
  refine (Set.finite_range f).subset ?_
  rintro G ⟨hN, hd⟩
  obtain ⟨z, x, rfl⟩ := exists_genND hv hcU hc G hN
  have hd' : (genND v c z x).det = sqNF (LocalDensity.NF.π v ^ N * detUnitND v c x₁) := by
    rw [hd, ← hd₁, det_genND_eq hv hcU]
  have hsum := ((det_genND_iff hv hcU hc z x (isUnit_detUnitND hv hcU x₁) N).1 hd').1
  have hle : ∀ i, z i < N + 1 := fun i => by
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (z j)) (Finset.mem_univ i)
    omega
  exact ⟨(fun i => ⟨z i, hle i⟩, x), rfl⟩

end NF

end

end QuadFormsKB.Hanke2011Structure.RatND

namespace QuadFormsKB.Hanke2011Structure

open QuadFormsKB.Hanke2011Structure.RatND
open IsDedekindDomain NumberField QuadFormsKB.Siegel QuadFormsKB.Lattices QuadFormsKB.HilbertModular
open QuadFormsKB.NFEuler QuadFormsKB.RegProd QuadFormsKB.Hanke2011Ternary.NF

variable {F : Type} [Field F] [NumberField F]

/-- **Named input: finiteness of the binary local genera of given determinant at the dyadic primes.**  For every
finite prime $\mathfrak p \mid 2$ of $F$ and every $S \in \mathrm{SqCl}(F_{\mathfrak p}^\times, \mathcal O_{\mathfrak p}^\times)$,
the nondegenerate primitive $\mathcal O_{\mathfrak p}$-genera of rank $2$ with $\det_H = S$ are finitely many.  This is
the part of `BinaryLocalGeneraFinite` not proved in the repository for a general number field (the primes
$\mathfrak p \nmid 2$ are `RatND.genera_finite_nd`; over $\mathbb Q$ the dyadic prime is `RatTwo.admGen_finite_two`).  It
is a classical fact (O'Meara 1963, §93: Jordan splittings at dyadic primes have bounded scales and finitely many
classes per component).  It is used only to make the local sums finite and is not equivalent to any mass formula. -/
@[kb "omeara1963" "§93 (finitely many local integral classes of given discriminant, dyadic p)"]
structure BinaryDyadicGeneraFinite (F : Type) [Field F] [NumberField F] : Prop where
  finite : ∀ (v : HeightOneSpectrum (𝓞 F)), (2 : 𝓞 F) ∈ v.asIdeal → ∀ (s : LocalSqCl v),
    {G : LocGenus v 2 | G.Nondeg ∧ G.Prim ∧ G.det = s}.Finite

/-- The dyadic part suffices: `BinaryLocalGeneraFinite` follows from `BinaryDyadicGeneraFinite` and the
nondyadic finiteness `RatND.genera_finite_nd`. -/
theorem binaryLocalGeneraFinite_of_dyadic (H : BinaryDyadicGeneraFinite F) : BinaryLocalGeneraFinite F where
  finite v s := by
    by_cases h2 : (2 : 𝓞 F) ∈ v.asIdeal
    · exact H.finite v h2 s
    · exact (genera_finite_nd h2 2 s).subset fun G hG => ⟨hG.1, hG.2.2⟩

/-- **Over $\mathbb Q$ the binary local genera of given determinant are finitely many at every prime** (unconditional). -/
theorem binaryLocalGeneraFinite_rat : BinaryLocalGeneraFinite ℚ :=
  binaryLocalGeneraFinite_of_dyadic ⟨fun _ h2 s => RatTwo.admGen_finite_two h2 2 s⟩

section Main

open Real

variable [IsTotallyReal F]

/-- **Lemma 7.8 for $n = 2$, conditional only on the dyadic part** of the finiteness input (see `lemma_7_8_two`). -/
@[kb "hanke2011structure" "Lemma 7.8, p. 32 (n = 2)"]
theorem lemma_7_8_two_dyadic (H : BinaryDyadicGeneraFinite F) (S : AdelicSqCl F)
    (hne : (GenStar S (totPosSig F 2) ∅ (fun _ => 1)).Nonempty)
    {βgen χ : HeightOneSpectrum (𝓞 F) → ℝ} (hg : IsGenericFamily S βgen χ) :
    ∑ᶠ t ∈ GenStar S (totPosSig F 2) ∅ (fun _ => 1), massOfTuple S (totPosSig F 2) ∅ (fun _ => 1) t =
      betaInvReg χ βgen * |(discr F : ℝ)| ^ ((1 : ℝ) / 2) * normAssoc S ^ ((3 : ℝ) / 2) *
        (astarTwo S βgen + (epsInf (totPosSig F 2) : ℝ) * bstarTwo S βgen) /
          (2 * (4 * π) ^ Module.finrank ℚ F) :=
  lemma_7_8_two (binaryLocalGeneraFinite_of_dyadic H) S hne hg

/-- **Theorem 7.11 (identity of the total mass, corrected $\kappa$), conditional on the dyadic part** of the finiteness
input and the tables (see `theorem_7_11_two`). -/
@[kb "hanke2011structure" "Thm. 7.11, p. 33 (identity of the total mass; corrected κ)"]
theorem theorem_7_11_two_dyadic (H : BinaryDyadicGeneraFinite F) (hs : TwoSplitsCompletely F) (S : AdelicSqCl F)
    (hne : (GenStar S (totPosSig F 2) ∅ (fun _ => 1)).Nonempty)
    {d : HeightOneSpectrum (𝓞 F) → LocalDatum ℝ} (hd : BinaryTableHolds S d) :
    ∑ᶠ t ∈ GenStar S (totPosSig F 2) ∅ (fun _ => 1), massOfTuple S (totPosSig F 2) ∅ (fun _ => 1) t =
      kappaCorr d * |(discr F : ℝ)| ^ ((1 : ℝ) / 2) * normAssoc S ^ ((1 : ℝ) / 2) /
        (2 * (2 * π) ^ Module.finrank ℚ F) * prodGammaInvNotDvd d :=
  theorem_7_11_two (binaryLocalGeneraFinite_of_dyadic H) hs S hne hd

end Main

/-- **Lemma 7.8 for $n = 2$ over $\mathbb Q$, unconditional**: for the positive definite signature, every $S$ with
$\mathrm{Cls}^*(S,\vec\sigma^+_\infty;2) \ne \emptyset$ and every admissible generic family, the sum over the classes of
$1/|\mathrm{Aut}(L)|$ equals $\beta^{-1}_{2,f}(\widetilde S)N(I(S))^{3/2}[A^*_2(S) + B^*_2(S)]/(2\cdot4\pi)$ (regularized
product, see `lemma_7_8_two`). -/
@[kb "hanke2011structure" "Lemma 7.8, p. 32 (n = 2, F = Q, unconditional)"]
theorem lemma_7_8_two_rat (S : AdelicSqCl ℚ)
    (hne : (GenStar S (totPosSig ℚ 2) ∅ (fun _ => 1)).Nonempty)
    {βgen χ : HeightOneSpectrum (𝓞 ℚ) → ℝ} (hg : IsGenericFamily S βgen χ) :
    ∑ᶠ t ∈ GenStar S (totPosSig ℚ 2) ∅ (fun _ => 1), massOfTuple S (totPosSig ℚ 2) ∅ (fun _ => 1) t =
      betaInvReg χ βgen * |(discr ℚ : ℝ)| ^ ((1 : ℝ) / 2) * normAssoc S ^ ((3 : ℝ) / 2) *
        (astarTwo S βgen + (epsInf (totPosSig ℚ 2) : ℝ) * bstarTwo S βgen) /
          (2 * (4 * Real.pi) ^ Module.finrank ℚ ℚ) :=
  lemma_7_8_two binaryLocalGeneraFinite_rat S hne hg

end QuadFormsKB.Hanke2011Structure

#print axioms QuadFormsKB.Hanke2011Structure.RatND.genera_finite_nd
#print axioms QuadFormsKB.Hanke2011Structure.binaryLocalGeneraFinite_rat
#print axioms QuadFormsKB.Hanke2011Structure.lemma_7_8_two_rat
#print axioms QuadFormsKB.Hanke2011Structure.theorem_7_11_two_dyadic
