/-
# Chenevier–Lannes: Witt's theorem $X_{16} = \{E_8 \oplus E_8, E_{16}\}$ (Corollary 2.3.6)

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §1.1, p. 2; Corollary 2.3.6, p. 36; §3.3.1–3.3.2, pp. 57–59.
Printed page numbers.

**Layer.** Even unimodular lattices as integral forms; $E_8 \oplus E_8$ = `Lattices.twoE8`, $E_{16} = D_{16}^+$ =
`Lattices.gamma16` (Cassels' $\Gamma_{16}$); the statement `WittRankSixteen` is from `Classification.lean`.

**Proves** (all unconditional):
- `intEquiv_of_isEvenUnimodular_sixteen`, `wittRankSixteen` (**Corollary 2.3.6**): every even unimodular lattice of
  dimension $16$ is isomorphic to $E_8 \oplus E_8$ or to $E_{16}$;
- `wittTwoClassesSixteen`: Cassels' named input `Cassels.WittTwoClassesSixteen` (the same statement) holds;
- `card_aut_twoE8`, `card_aut_gamma16` (§3.3.1, p. 57, and its Variant, p. 58): $|O(E_8 \oplus E_8)| = 2\,|O(E_8)|^2$ and
  $|O(E_{16})| = 2^{15}\cdot 16!$;
- `card_aut_ratio_sixteen` (§3.3.2, p. 59): $|O(E_8 \oplus E_8)|/|O(E_{16})| = 405/286$.

*Proof differs from the book's.* The book (p. 36) uses $\theta_L = E_8$, so $|R(L)| = 480$ and $h(L) = 30$, and the
classification of root systems. Here: the mass of the genus is $691/277667181515243520000$ (`mass_two_smul_sixteen`,
Conway–Sloane's formula), and the two upper bounds $|O(E_8 \oplus E_8)| \le 2|O(E_8)|^2$ (`card_aut_twoE8_le`, from the
connectedness of the Dynkin diagram of $E_8$) and $|O(E_{16})| \le 2^{15}\cdot 16!$ (`card_aut_gamma16_le`, signed
permutations) show that $E_8 \oplus E_8$ and $E_{16}$ already exhaust the mass:
$$\frac{1}{2 \cdot 696729600^2} + \frac{1}{2^{15}\cdot 16!} = \frac{691}{277667181515243520000}.$$
-/
import QuadFormsKB.Literature.ChenevierLannes.Wave2.Mordell
import QuadFormsKB.Literature.ChenevierLannes.Wave2.AutE16
import QuadFormsKB.Literature.ChenevierLannes.Wave2.AutTwoE8

open Matrix

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Lattices

/-- The two classes of $X_{16}$ as a family indexed by `Fin 2`: the norm forms of $E_8 \oplus E_8$ and $E_{16}$. -/
private def sixteenReps : Fin 2 → QuadForm ℤ 16 := ![(2 : ℤ) • twoE8, (2 : ℤ) • gamma16]

private theorem not_intEquiv_twoE8_gamma16 : ¬ IntEquiv twoE8 gamma16 := fun h =>
  gamma16_not_isometric (IsometricGL.symm h)

private theorem sixteenReps_gen (i : Fin 2) : SameGenus ((2 : ℤ) • twoE8) (sixteenReps i) := by
  fin_cases i
  · exact SameGenus.refl _
  · exact (Binary.sameGenus_smul_iff (by norm_num) _ _).mpr
      (sameGenus_of_isEvenUnimodular isEvenUnimodular_twoE8 isEvenUnimodular_gamma16)

private theorem sixteenReps_dist (i j : Fin 2) (h : IntEquiv (sixteenReps i) (sixteenReps j)) : i = j := by
  have h' : ∀ {a b : QuadForm ℤ 16}, IntEquiv ((2 : ℤ) • a) ((2 : ℤ) • b) → IntEquiv a b :=
    fun hab => (Binary.intEquiv_smul_iff (by norm_num) _ _).mp hab
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd (h' h) not_intEquiv_twoE8_gamma16
  · exact absurd (IsometricGL.symm (h' h)) not_intEquiv_twoE8_gamma16
  · rfl

/-- The two lower bounds $1/(2|O(E_8)|^2)$ and $1/(2^{15}16!)$. -/
private noncomputable def sixteenBounds : Fin 2 → ℝ :=
  ![1 / (2 * 696729600 ^ 2), 1 / (2 ^ 15 * (Nat.factorial 16 : ℝ))]

private theorem inv_le_inv_card {G : Type*} [Group G] [Finite G] {B : ℕ} (hB : Nat.card G ≤ B) :
    (1 : ℝ) / B ≤ ((Nat.card G : ℝ))⁻¹ := by
  have hpos : (0 : ℝ) < Nat.card G := by exact_mod_cast Nat.card_pos
  rw [one_div]
  exact inv_anti₀ hpos (by exact_mod_cast hB)

private theorem finite_aut {Q : QuadForm ℤ 16} (hQ : IntQF.PosDef Q) : Finite (Aut Q) :=
  Nat.finite_of_card_ne_zero hQ.card_aut_pos.ne'

private theorem sixteenBounds_le (i : Fin 2) :
    sixteenBounds i ≤ ((Nat.card (Aut (sixteenReps i)) : ℝ))⁻¹ := by
  fin_cases i
  · show (1 : ℝ) / (2 * 696729600 ^ 2) ≤ ((Nat.card (Aut ((2 : ℤ) • twoE8)) : ℝ))⁻¹
    rw [Binary.aut_smul (by norm_num)]
    have := finite_aut twoE8_posDef
    have h := card_aut_twoE8_le
    rw [card_aut_e8_eq] at h
    refine le_trans (le_of_eq ?_) (inv_le_inv_card h)
    push_cast
    norm_num
  · show (1 : ℝ) / (2 ^ 15 * (Nat.factorial 16 : ℝ)) ≤ ((Nat.card (Aut ((2 : ℤ) • gamma16)) : ℝ))⁻¹
    rw [Binary.aut_smul (by norm_num)]
    have := finite_aut gamma16_posDef
    refine le_trans (le_of_eq ?_) (inv_le_inv_card card_aut_gamma16_le)
    push_cast
    norm_num

private theorem sixteen_mass_eq : Siegel.mass ((2 : ℤ) • twoE8) = ∑ i, sixteenBounds i := by
  rw [mass_two_smul_sixteen isEvenUnimodular_twoE8, Fin.sum_univ_two]
  simp only [sixteenBounds, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  norm_num [Nat.factorial]

/-- **Every even unimodular lattice of dimension $16$ is isomorphic to $E_8 \oplus E_8$ or to $E_{16}$** (Chenevier–Lannes,
Corollary 2.3.6, p. 36). Unconditional; see the module docstring for the proof (by the mass). -/
@[kb "chenevierlannes2019" "Cor. 2.3.6, p. 36"]
theorem intEquiv_of_isEvenUnimodular_sixteen {Q : QuadForm ℤ 16} (hQ : IsEvenUnimodular Q) :
    IntEquiv twoE8 Q ∨ IntEquiv gamma16 Q := by
  have hgen : SameGenus ((2 : ℤ) • twoE8) ((2 : ℤ) • Q) :=
    (Binary.sameGenus_smul_iff (by norm_num) _ _).mpr (sameGenus_of_isEvenUnimodular isEvenUnimodular_twoE8 hQ)
  obtain ⟨i, hi⟩ := exists_intEquiv_of_mass_le (posDef_two_smul twoE8_posDef) sixteenReps sixteenReps_gen
    sixteenReps_dist sixteenBounds sixteenBounds_le sixteen_mass_eq.le hgen
  fin_cases i
  · exact Or.inl ((Binary.intEquiv_smul_iff (by norm_num) _ _).mp hi)
  · exact Or.inr ((Binary.intEquiv_smul_iff (by norm_num) _ _).mp hi)

/-- **Corollary 2.3.6 (Witt)**: $X_{16} = \{E_8 \oplus E_8, E_{16}\}$ (Chenevier–Lannes, p. 36, and §1.1, p. 2). The
named statement `WittRankSixteen` is now **proved**, unconditionally. -/
@[kb "chenevierlannes2019" "Cor. 2.3.6, p. 36; §1.1, p. 2"]
theorem wittRankSixteen : WittRankSixteen := by
  unfold WittRankSixteen
  ext c
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    rcases intEquiv_of_isEvenUnimodular_sixteen hQ with h | h
    · exact Or.inl (classOf_eq_classOf_iff.mpr (IsometricGL.symm h))
    · exact Or.inr (classOf_eq_classOf_iff.mpr (IsometricGL.symm h))
  · rintro (rfl | rfl)
    · exact ⟨twoE8, isEvenUnimodular_twoE8, rfl⟩
    · exact ⟨gamma16, isEvenUnimodular_gamma16, rfl⟩

/-- **Cassels' named input `WittTwoClassesSixteen` holds** (Cassels, App. B, §5, p. 386, quoting Witt): the genus of
$2\Gamma_8 = E_8 \oplus E_8$ consists of the classes of $2\Gamma_8$ and $\Gamma_{16}$. Unconditional
(`wittRankSixteen` and `wittRankSixteen_iff`). -/
theorem wittTwoClassesSixteen : Cassels.WittTwoClassesSixteen := wittRankSixteen_iff.mp wittRankSixteen

/-- **The genus of $2\Gamma_8 = E_8 \oplus E_8$ has exactly two classes** (Cassels, App. B, §5, p. 386, quoting Witt).
Unconditional (Cassels' `WittTwoClassesSixteen.ncard` with `wittTwoClassesSixteen`). -/
theorem genusClasses_twoE8_ncard : (genusClasses twoE8).ncard = 2 := wittTwoClassesSixteen.ncard

/-- **$|X_{16}| = 2$** (Chenevier–Lannes, §1.1, p. 2). Unconditional. -/
@[kb "chenevierlannes2019" "§1.1, p. 2 (X_16 has two elements)"]
theorem classSet_sixteen_ncard_eq : (classSet 16).ncard = 2 := classSet_sixteen_ncard wittRankSixteen

/-! ### The orders of $O(E_8 \oplus E_8)$ and $O(E_{16})$ -/

private theorem card_aut_sixteen_eq :
    Nat.card (Aut twoE8) = 2 * 696729600 ^ 2 ∧ Nat.card (Aut gamma16) = 2 ^ 15 * Nat.factorial 16 := by
  have hle := Kneser.sum_inv_card_aut_le_mass (posDef_two_smul twoE8_posDef) sixteenReps sixteenReps_gen
    sixteenReps_dist
  rw [sixteen_mass_eq, Fin.sum_univ_two, Fin.sum_univ_two] at hle
  have h0 := sixteenBounds_le 0
  have h1 := sixteenBounds_le 1
  simp only [sixteenReps, sixteenBounds, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Binary.aut_smul (show (2 : ℤ) ≠ 0 by norm_num)] at hle h0 h1
  have e0 : ((Nat.card (Aut twoE8) : ℝ))⁻¹ = 1 / (2 * 696729600 ^ 2) := by linarith
  have e1 : ((Nat.card (Aut gamma16) : ℝ))⁻¹ = 1 / (2 ^ 15 * (Nat.factorial 16 : ℝ)) := by linarith
  rw [one_div] at e0 e1
  have f0 := inv_inj.mp e0
  have f1 := inv_inj.mp e1
  constructor
  · exact_mod_cast f0
  · exact_mod_cast f1

/-- **$|O(E_8 \oplus E_8)| = 2\,|O(E_8)|^2$** (Chenevier–Lannes, §3.3.1, p. 57: $O(E_8 \oplus E_8)$ is the wreath product
$S_2 \wr O(E_8)$), with $|O(E_8)| = 696729600$. Unconditional (the upper bound `card_aut_twoE8_le` is an equality by the
mass). -/
@[kb "chenevierlannes2019" "§3.3.1, p. 57 (O(E_8 ⊕ E_8) = S_2 ≀ O(E_8))"]
theorem card_aut_twoE8 : Nat.card (Aut twoE8) = 2 * Nat.card (Aut e8) ^ 2 := by
  rw [card_aut_sixteen_eq.1, card_aut_e8_eq]

/-- **$|O(E_{16})| = 2^{15}\cdot 16!$** (Chenevier–Lannes, §3.3.1, Variant, p. 58: $O(E_{16}) \cong S_{16} \ltimes
(\{\pm1\}^{16})_0$, the signed permutations with an even number of signs $-1$). Unconditional. -/
@[kb "chenevierlannes2019" "§3.3.1, Variant, p. 58 (O(E_16) = S_16 ⋉ ({±1}^16)_0)"]
theorem card_aut_gamma16 : Nat.card (Aut gamma16) = 2 ^ 15 * Nat.factorial 16 := card_aut_sixteen_eq.2

/-- **$|O(E_8 \oplus E_8)|/|O(E_{16})| = 405/286$** (Chenevier–Lannes, §3.3.2, p. 59; also §5.2, p. 126). Unconditional. -/
@[kb "chenevierlannes2019" "§3.3.2, p. 59 (|O(E_8 ⊕ E_8)|/|O(E_16)| = 405/286)"]
theorem card_aut_ratio_sixteen :
    (Nat.card (Aut twoE8) : ℚ) / Nat.card (Aut gamma16) = 405 / 286 := by
  rw [card_aut_sixteen_eq.1, card_aut_sixteen_eq.2]
  norm_num [Nat.factorial]

end QuadFormsKB.ChenevierLannes
