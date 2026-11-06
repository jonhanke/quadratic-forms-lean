/-
# Conway–Sloane, LDL IV, §11, Lemma 2 ("if") at $p = 2$: the global part

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §11, Lemma 2, p. 280.

`GenusLemma2Odd.lean` proves the odd primes and the real place and leaves `Lemma2IfDyadicStatement` (equivalence over
$\mathbb Z_2$). This file removes everything global from that statement.

**Proved (unconditional).**
* `qtwo_congrIn_of_discIso`: positive definite $A$, $B$ with an isomorphism of discriminant forms are congruent over
  $\mathbb Q_2$. *Proof:* diagonalize over $\mathbb Q$ with integer entries ($A \sim \langle a_i\rangle$, $B \sim
  \langle b_i\rangle$); the odd-prime part (`Lemma2Odd.zpEquiv_of_discIso`) gives $\langle a\rangle \sim \langle b\rangle$
  over every $\mathbb Q_p$, $p$ odd, hence equal $p$-excesses (`isometric_padic_iff_pExcess`); the real place gives equal
  signatures (Sylvester); the oddity formula (Hilbert reciprocity, `oddity_formula_of_adapted`, summing over the odd
  primes dividing either determinant) then gives equal oddities; with $\det A = \det B$ the classification of
  $\mathbb Q_2$-forms (`isometric_two_adic_iff_oddity`) gives $\langle a\rangle \sim \langle b\rangle$ over $\mathbb Q_2$.
* `lemma2IfDyadic_of_rational`: `Lemma2IfDyadicStatement` follows from the purely 2-adic named statement
  `Lemma2IfDyadicRationalStatement` (below), together with `lemma2If_of_dyadicRational`,
  `lemma2Statement_of_dyadicRational`, `lemma4_of_dyadicRational`.

**Named statement** `Lemma2IfDyadicRationalStatement` (the part of the case $p = 2$ that is *not* global): symmetric
nondegenerate $A$, $B \in M_n(\mathbb Z)$ of the same type with `DiscIso`, which are congruent over $\mathbb Q_2$, are
$\mathrm{GL}_n(\mathbb Z_2)$-equivalent. It uses neither positivity nor the odd primes: only the $2$-primary part of the
discriminant form and the rational class over $\mathbb Q_2$ enter. (It is the local content of Kneser–Puppe: over
$\mathbb Z_2$ the discriminant form together with the $\mathbb Q_2$-class determines the Jordan constituents up to
Conway–Sloane's moves, Thm. 10.) Indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemma2Odd
import QuadFormsKB.Literature.ConwaySloane.GenusSymbolBijectionOddity
import QuadFormsKB.Literature.LocalGlobal.ConwaySloane

set_option linter.unusedSectionVars false

open Matrix QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.LocalDensity QuadFormsKB.Cassels Finset

namespace QuadFormsKB.ConwaySloane.Mass

variable {n : ℕ}

/-- An odd-prime-adapted set may be enlarged by odd primes. -/
theorem adapted_mono {S S' : Finset Nat.Primes} {a : ℤ} (h : Adapted S a) (hS : S ⊆ S')
    (hodd : ∀ p ∈ S', p.1 ≠ 2) : Adapted S' a :=
  ⟨hodd, fun p hp2 hp => hS (h.2 p hp2 hp)⟩

/-- **Equal oddities from the odd primes and the real place.** Integer diagonal forms $\langle a\rangle$, $\langle b\rangle$
with equal signature and equal $p$-excess at every odd prime have equal oddity (the oddity formula, summed over the odd
primes dividing either determinant). -/
theorem oddity_eq_of_excess_eq (a b : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hsig : signature a = signature b)
    (hp : ∀ (p : ℕ), p.Prime → p ≠ 2 → pExcess p a = pExcess p b) : oddity a = oddity b := by
  classical
  set S := oddPrimeSet a ∪ oddPrimeSet b with hS
  have hSodd : ∀ p ∈ S, p.1 ≠ 2 := fun p hp => by
    rcases mem_union.mp hp with h | h
    · exact (adapted_oddPrimeSet a ha).1 p h
    · exact (adapted_oddPrimeSet b hb).1 p h
  have h1 := oddity_formula_of_adapted a ha S
    (adapted_mono (adapted_oddPrimeSet a ha) subset_union_left hSodd)
  have h2 := oddity_formula_of_adapted b hb S
    (adapted_mono (adapted_oddPrimeSet b hb) subset_union_right hSodd)
  rw [← h1, ← h2, hsig]
  congr 1
  exact sum_congr rfl fun p hpS => hp p.1 p.2 (hSodd p hpS)

/-- **Lemma 2 ("if") at $p = 2$ up to the $\mathbb Q_2$-class: the global input is removed.** Positive definite $A$, $B$
with `DiscIso T A B` are congruent over $\mathbb Q_2$: the odd primes and the real place are proved
(`Lemma2Odd.zpEquiv_of_discIso`, `isometricGL_real_of_posDefGram`), and the product formula for the Hasse invariants
(the oddity formula) transfers them to the place $2$. Unconditional. -/
@[kb "conwaysloane1988" "§11, Lemma 2, p. 280 (if; rational equivalence over Q_2, from the oddity formula)"]
theorem qtwo_congrIn_of_discIso {A B : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A) (hB : PosDefGram B)
    {T : ℕ} (h : DiscIso T A B) :
    CongrIn ℚ_[2] (A.map (Int.castRingHom ℚ_[2])) (B.map (Int.castRingHom ℚ_[2])) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdet := det_eq_of_discIso hA hB h
  obtain ⟨a, ha, hAa⟩ := exists_rat_diag A hA.1 hA.det_ne
  obtain ⟨b, hb, hBb⟩ := exists_rat_diag B hB.1 hB.det_ne
  -- odd primes
  have hodd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → (QuadForm.diag fun i => (a i : ℚ)).IsometricIn ℚ_[p]
      (QuadForm.diag fun i => (b i : ℚ)) := by
    intro p _ hp2
    have hZ := Lemma2Odd.zpEquiv_of_discIso hp2 hA.1 hB.1 hA.det_ne hdet h
    exact isometricIn_diag_of_congrIn _ _
      (((congrIn_diag_of_rat (K := ℚ_[p]) hAa).symm.trans (congrIn_of_zpEquiv hZ)).trans
        (congrIn_diag_of_rat (K := ℚ_[p]) hBb))
  -- the real place
  have hCR := (isometricGL_map_iff (K := ℝ) hA.1 hB.1).1 (isometricGL_real_of_posDefGram hA hB)
  have hreal : (QuadForm.diag fun i => (a i : ℚ)).IsometricIn ℝ (QuadForm.diag fun i => (b i : ℚ)) :=
    isometricIn_diag_of_congrIn _ _
      (((congrIn_diag_of_rat (K := ℝ) hAa).symm.trans hCR).trans (congrIn_diag_of_rat (K := ℝ) hBb))
  have hsig : signature a = signature b := by
    rw [signature_eq_negCount a ha, signature_eq_negCount b hb, negCount_eq_of_isometric _ _ hreal]
  have hexc : ∀ (p : ℕ), p.Prime → p ≠ 2 → pExcess p a = pExcess p b := fun p hp hp2 => by
    haveI : Fact p.Prime := ⟨hp⟩
    exact ((isometric_padic_iff_pExcess hp2 a b ha hb).1 (hodd p hp2)).2
  have hod : oddity a = oddity b := oddity_eq_of_excess_eq a b ha hb hsig hexc
  -- the determinants
  have hss : SameSquareClass ℚ_[2] ((∏ i, a i : ℤ) : ℚ) ((∏ i, b i : ℤ) : ℚ) := by
    obtain ⟨c, hc, hca⟩ := det_congrIn hAa
    obtain ⟨d, hd, hdb⟩ := det_congrIn hBb
    rw [det_diagonal, det_map_intCast] at hca hdb
    have hc0 : c ≠ 0 := hc.ne_zero
    have hd0 : d ≠ 0 := hd.ne_zero
    have hdet' : (A.det : ℚ) = (B.det : ℚ) := by rw [hdet]
    have e : ((∏ i, a i : ℤ) : ℚ) = (c / d) ^ 2 * ((∏ i, b i : ℤ) : ℚ) := by
      push_cast
      rw [hca, hdb, hdet', div_pow]
      field_simp
    refine ⟨((c / d : ℚ) : ℚ_[2]), ?_, ?_⟩
    · exact_mod_cast div_ne_zero hc0 hd0
    · have := congrArg (algebraMap ℚ ℚ_[2]) e
      rw [map_mul, map_pow] at this
      exact this
  have h2 := (isometric_two_adic_iff_oddity a b ha hb).2 ⟨hss, hod⟩
  have hD : CongrIn ℚ_[2] (Matrix.diagonal fun i => (((a i : ℤ) : ℚ) : ℚ_[2]))
      (Matrix.diagonal fun i => (((b i : ℤ) : ℚ) : ℚ_[2])) := congrIn_of_isometricIn_diag _ _ h2
  exact (congrIn_diag_of_rat (K := ℚ_[2]) hAa).trans (hD.trans (congrIn_diag_of_rat (K := ℚ_[2]) hBb).symm)

/-- **Lemma 2, "if", at $p = 2$: the purely $2$-adic part**, as a **named statement** (Kneser–Puppe 1953; stated without
proof in LDL IV §11, p. 280). Symmetric nondegenerate $A$, $B \in M_n(\mathbb Z)$ of the same type $T$ (`gramType`) with an
isomorphism $L^*/L \cong M^*/M$ preserving norms mod $T$ (`DiscIso`), which are congruent over $\mathbb Q_2$, are
$\mathrm{GL}_n(\mathbb Z_2)$-equivalent. No positivity and no condition at odd primes: the $\mathbb Q_2$-class is the
only global trace (it is supplied by `qtwo_congrIn_of_discIso`). Not weaker than needed: the oddity example
$\langle 1,1\rangle$, $\langle 3,3\rangle$ (same discriminant form, different $\mathbb Q_2$-class) is excluded by the
hypothesis of congruence over $\mathbb Q_2$. -/
@[kb "conwaysloane1988" "§11, Lemma 2, p. 280 (if, at p = 2, given the Q_2-class; stated)"]
structure Lemma2IfDyadicRationalStatement : Prop where
  imp : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℤ), Aᵀ = A → Bᵀ = B → A.det ≠ 0 → B.det ≠ 0 →
    gramType A = gramType B → DiscIso (gramType A) A B →
    CongrIn ℚ_[2] (A.map (Int.castRingHom ℚ_[2])) (B.map (Int.castRingHom ℚ_[2])) →
      IsometricGL ((ofMatrixZ A).map (Int.castRingHom ℤ_[2])) ((ofMatrixZ B).map (Int.castRingHom ℤ_[2]))

/-- **`Lemma2IfDyadicStatement` from its purely $2$-adic part**: the global content (Hilbert reciprocity) is proved. -/
@[kb "conwaysloane1988" "§11, Lemma 2, p. 280 (if, at p = 2; conditional on the Q_2-local part)"]
theorem lemma2IfDyadic_of_rational (h : Lemma2IfDyadicRationalStatement) : Lemma2IfDyadicStatement where
  imp n A B hA hB ht hi :=
    h.imp n A B hA.1 hB.1 hA.det_ne hB.det_ne ht hi (qtwo_congrIn_of_discIso hA hB hi)

/-- The "if" half of Lemma 2, conditional only on the $2$-adic part. -/
theorem lemma2If_of_dyadicRational (h : Lemma2IfDyadicRationalStatement) : Lemma2IfStatement :=
  lemma2If_of_dyadic (lemma2IfDyadic_of_rational h)

/-- **Lemma 2** conditional only on the $2$-adic part. -/
theorem lemma2Statement_of_dyadicRational (h : Lemma2IfDyadicRationalStatement) : Lemma2Statement :=
  lemma2Statement_of_dyadic (lemma2IfDyadic_of_rational h)

/-- **Lemma 4** conditional only on the $2$-adic part. -/
theorem lemma4_of_dyadicRational (h : Lemma2IfDyadicRationalStatement) : Lemma4Statement :=
  lemma4_of_dyadic (lemma2IfDyadic_of_rational h)

end QuadFormsKB.ConwaySloane.Mass
