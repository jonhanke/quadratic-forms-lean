/-
# Cassels, Appendices A and B: what is proved around the cited class-number statements

Cassels, *Rational Quadratic Forms* (1978), App. A, §3, p. 364 (Watson) and App. B, §3, p. 377 (Magnus), §5, p. 386
(Witt). The three results are quoted without proof and stay named statements (`DefiniteForms.WatsonTwoClasses`,
`Cassels.MagnusOneClassGenera`, `Cassels.WittTwoClassesSixteen`). This file proves what follows without them or
reduces them to their honest core:

* `two_le_encard_genusClasses_twoE8` (unconditional): the genus of $2\Gamma_8$ has **at least** two classes, those of
  $2\Gamma_8$ and $\Gamma_{16}$; so Witt's theorem is exactly the statement that there is no third class
  (`wittTwoClassesSixteen_iff_subset`);
* `WatsonTwoClasses.magnus_two_le`: Watson's $n > 11$ implies the second half of Magnus' statement ($n \ge 35$).

**Layer.** Integer-valued forms `QuadForm ℤ n`, genus `Siegel.SameGenus`, classes `Siegel.genusClasses` (as in
`AppB/Statements.lean`).
-/
import QuadFormsKB.Literature.Cassels.AppB.Statements
import QuadFormsKB.Literature.Cassels.AppA.Statements

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Cassels

open Siegel Lattices DefiniteForms

/-- **The genus of $2\Gamma_8$ has at least two classes** (Cassels, App. A, Example 1, p. 367, and App. B, §5, p. 386;
unconditional): $\Gamma_{16}$ lies in the genus of $2\Gamma_8 = E_8 \perp E_8$ (`gamma16_sameGenus`) and is not
integrally equivalent to it (`gamma16_not_isometric`), so the classes of $2\Gamma_8$ and $\Gamma_{16}$ are two distinct
classes of the genus. -/
@[kb "cassels1978" "App. B, §5, p. 386 (the genus of determinant 1 in 16 variables has at least the two classes 2Γ₈, Γ₁₆)"]
theorem two_le_encard_genusClasses_twoE8 : (2 : ℕ∞) ≤ (genusClasses twoE8).encard := by
  have hsub : ({classOf twoE8, classOf gamma16} : Set (QClass 16)) ⊆ genusClasses twoE8 := by
    rintro c (rfl | rfl)
    · exact classOf_mem_genusClasses_iff.2 (SameGenus.refl _)
    · exact classOf_mem_genusClasses_iff.2 gamma16_sameGenus.symm
  have hne : classOf twoE8 ≠ classOf gamma16 := fun he =>
    gamma16_not_isometric (IsometricGL.symm (Quotient.exact he))
  calc (2 : ℕ∞) = ({classOf twoE8, classOf gamma16} : Set (QClass 16)).encard := by
        rw [Set.encard_pair hne]
    _ ≤ _ := Set.encard_le_encard hsub

/-- **Witt's theorem is "no third class"** (Cassels, App. B, §5, p. 386): the named statement
`WittTwoClassesSixteen` (the classes of the genus of $2\Gamma_8$ are exactly those of $2\Gamma_8$ and $\Gamma_{16}$)
is equivalent to the inclusion of the classes of the genus in $\{[2\Gamma_8], [\Gamma_{16}]\}$; the reverse inclusion is
proved (`two_le_encard_genusClasses_twoE8`). -/
@[kb "cassels1978" "App. B, §5, p. 386 (Witt: the genus of determinant 1 in 16 variables has two classes)"]
theorem wittTwoClassesSixteen_iff_subset :
    WittTwoClassesSixteen ↔ genusClasses twoE8 ⊆ {classOf twoE8, classOf gamma16} := by
  constructor
  · intro h; rw [h.classes]
  · intro h
    refine ⟨Set.Subset.antisymm h ?_⟩
    rintro c (rfl | rfl)
    · exact classOf_mem_genusClasses_iff.2 (SameGenus.refl _)
    · exact classOf_mem_genusClasses_iff.2 gamma16_sameGenus.symm

/-- **Watson implies the second half of Magnus' statement** (Cassels, App. A, §3, p. 364, and App. B, §3, p. 377): if
every genus of positive definite forms in $n > 11$ variables has at least two classes (`WatsonTwoClasses`), then so does
every genus in $n \ge 35$ variables (the field `two_le` of `MagnusOneClassGenera`). Argument: `h` the named statement. -/
@[kb "cassels1978" "App. B, §3, p. 377 (every genus with n ≥ 35 has two classes; from Watson's n > 11, App. A, p. 364)"]
theorem WatsonTwoClasses.magnus_two_le (h : WatsonTwoClasses) :
    ∀ (n : ℕ) (Q : QuadForm ℤ n), 35 ≤ n → IntQF.PosDef Q → (2 : ℕ∞) ≤ (genusClasses Q).encard :=
  fun _ _ hn hQ => h.two_le_encard (by omega) hQ

end QuadFormsKB.Cassels
