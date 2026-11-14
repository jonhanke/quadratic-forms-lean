/-
# Chenevier–Lannes: Mordell's theorem $X_8 = \{E_8\}$ (Corollary 2.3.5)

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §1.1, p. 2, and Corollary 2.3.5, p. 36. Printed page numbers.

**Layer.** Even unimodular lattices as integral forms (`EvenUnimodular.lean`); the statement `MordellRankEight`
($X_8 = \{E_8\}$) is from `Classification.lean`.

**Proves** (all unconditional):
- `card_aut_e8_eq`: $|O(E_8)| = 696729600$ for the form `Siegel.e8` (from O'Meara's `Lattices.card_aut_e8`, which is
  proved from the mass of the genus of $I_9$);
- `mordellRankEight` (**Corollary 2.3.5**): $X_8 = \{E_8\}$;
- `intEquiv_e8_of_isEvenUnimodular`: every even unimodular lattice of dimension $8$ is isomorphic to $E_8$;
- `classSet_eight_ncard`: $|X_8| = 1$.

*Proof differs from the book's.* The book (p. 36) uses that the theta series is $E_4$, so $|R(L)| = 240$ and
$h(L) = 30$, and then the classification of root systems. Here: the mass of the genus of the norm form $2Q$ is
$1/696729600$ (`mass_two_smul_eight`, Conway–Sloane's mass formula), $E_8$ alone already contributes
$1/|O(E_8)| = 1/696729600$, so the genus has no other class (the completeness criterion
`Lattices.exists_intEquiv_of_mass_le`).
-/
import QuadFormsKB.Literature.ChenevierLannes.Wave2.Mass
import QuadFormsKB.Literature.OMeara.Sec106Rank13Aut

open Matrix

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Lattices

/-- The norm form of $E_8$: `ofMatrixZ` of the Cartan matrix is $2 \cdot$ `Siegel.e8`. -/
theorem ofMatrixZ_cartanE8 : LocalDensity.ofMatrixZ (CartanMatrix.E 8) = (2 : ℤ) • e8 := by
  rw [← e8_hessian, ofMatrixZ_hessian]

/-- **$|O(E_8)| = 696729600$** ($= |W(E_8)|$) for the form `Siegel.e8` (Hessian the Cartan matrix of $E_8$).
Unconditional: O'Meara's `Lattices.card_aut_e8` (from the mass of the genus of $I_9$) and $O(2Q) = O(Q)$. -/
theorem card_aut_e8_eq : Nat.card (Aut e8) = 696729600 := by
  have h := card_aut_e8
  have e : LocalDensity.ofMatrixZ e8Data.G = (2 : ℤ) • e8 := ofMatrixZ_cartanE8
  rw [e, Binary.aut_smul (by norm_num)] at h
  exact h

/-- **Every even unimodular lattice of dimension $8$ is isomorphic to $E_8$** (Chenevier–Lannes, Corollary 2.3.5,
p. 36). Unconditional; see the module docstring for the proof (by the mass, not by root systems). -/
@[kb "chenevierlannes2019" "Cor. 2.3.5, p. 36"]
theorem intEquiv_e8_of_isEvenUnimodular {Q : QuadForm ℤ 8} (hQ : IsEvenUnimodular Q) : IntEquiv e8 Q := by
  have hpd : IntQF.PosDef ((2 : ℤ) • e8) := posDef_two_smul e8_posDef
  have hgen : SameGenus ((2 : ℤ) • e8) ((2 : ℤ) • Q) :=
    (Binary.sameGenus_smul_iff (by norm_num) _ _).mpr (sameGenus_of_isEvenUnimodular isEvenUnimodular_e8 hQ)
  obtain ⟨_, hi⟩ := exists_intEquiv_of_mass_le (ι := Unit) hpd (fun _ => (2 : ℤ) • e8)
    (fun _ => SameGenus.refl _) (fun _ _ _ => rfl) (fun _ => 1 / 696729600)
    (fun _ => by rw [Binary.aut_smul (by norm_num), card_aut_e8_eq]; norm_num)
    (by rw [mass_two_smul_eight isEvenUnimodular_e8]; simp) hgen
  exact (Binary.intEquiv_smul_iff (by norm_num) _ _).mp hi

/-- **Corollary 2.3.5 (Mordell)**: $X_8 = \{E_8\}$ (Chenevier–Lannes, p. 36, and §1.1, p. 2). The named statement
`MordellRankEight` is now **proved**, unconditionally. -/
@[kb "chenevierlannes2019" "Cor. 2.3.5, p. 36; §1.1, p. 2"]
theorem mordellRankEight : MordellRankEight := by
  unfold MordellRankEight
  ext c
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact classOf_eq_classOf_iff.mpr (IsometricGL.symm (intEquiv_e8_of_isEvenUnimodular hQ))
  · rintro rfl
    exact ⟨e8, isEvenUnimodular_e8, rfl⟩

/-- **$|X_8| = 1$** (Chenevier–Lannes, §1.1, p. 2). Unconditional. -/
@[kb "chenevierlannes2019" "§1.1, p. 2 (X_8 = {E_8})"]
theorem classSet_eight_ncard : (classSet 8).ncard = 1 := by
  rw [mordellRankEight, Set.ncard_singleton]

end QuadFormsKB.ChenevierLannes
