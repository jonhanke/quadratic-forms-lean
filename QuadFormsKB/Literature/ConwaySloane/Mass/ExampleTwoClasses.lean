/-
# Conway–Sloane 1988, §9 (ii): the genus of $a_3 \oplus I_1$ has exactly two classes

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), §9 (ii), p. 273 (bibliography key `conwaysloane1988`): "there are two forms in the genus of $f$, namely
$f = a_3 \oplus I_1$ and $g = c_4$. Their total mass is indeed $\frac1{2^2\cdot2\cdot2\cdot2} + \frac1{2\cdot8\cdot1} = \frac3{32}$."

**Conventions.** Forms are integral Gram matrices with quadratic form `LocalDensity.ofMatrixZ`, variables
$x_0, \ldots, x_3$ (0-based). The two forms are
* $f = a_3 \oplus I_1$, Gram matrix `ex2Gram` $= \begin{pmatrix}7&1&1&0\\1&2&0&0\\1&0&2&0\\0&0&0&1\end{pmatrix}$, where
  $a_3$ = `a3Gram` $= \begin{pmatrix}7&1&1\\1&2&0\\1&0&2\end{pmatrix}$;
* $g = c_4$, represented by the Gram matrix `c4Gram` $= \begin{pmatrix}2&-1&-1&0\\-1&3&0&-1\\-1&0&3&-1\\0&-1&-1&3\end{pmatrix}$
  (determinant $24$, minimum $2$, two vectors of norm $2$; a representative of the paper's
  $c_4 = A_1 6_1 (3^{13})_2[1\,\tfrac12\tfrac12\tfrac12]$, identified here by being the second class of the genus).

Classes are $\mathrm{GL}_4(\mathbb Z)$-classes, $\lvert\mathrm{Aut}\rvert$ counts improper automorphisms (`Siegel.Aut`).

**Proof.**
* $g$ is a $5$-neighbour of $f$ (a Kneser neighbour certificate checked by `decide`, `NbCert.sameGenus`), hence in the
  genus of $f$.
* $\lvert\mathrm{Aut}(a_3)\rvert = 16$ and $\lvert\mathrm{Aut}(g)\rvert = 16$ by certified enumeration (`card_aut_eq_of_cert`), and
  $\lvert\mathrm{Aut}(a_3 \oplus I_1)\rvert = 2\,\lvert\mathrm{Aut}(a_3)\rvert = 32$ since $a_3$ has no vector of norm $1$
  (`card_aut_sumI`, §10). So $f \not\sim g$.
* $m(f) = \frac3{32}$ (`example_ii_mass`) $= \frac1{32} + \frac1{16}$, so there is no third class
  (`Siegel.Kneser.genusClasses_eq_of_sum_eq_mass`).

**Proves** `example_ii_two_classes` (§9 (ii), p. 273). Unconditional.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.ExampleTwo
import QuadFormsKB.Literature.ConwaySloane.Mass.Vines
import QuadFormsKB.Siegel.KneserAut
import QuadFormsKB.Siegel.KneserMass

open Matrix QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.LocalDensity

namespace QuadFormsKB.ConwaySloane.Mass

open QuadFormsKB.Siegel.Kneser

/-- The Gram matrix of $a_3$ (Conway–Sloane 1988, §9 (ii), p. 272). -/
def a3Gram : Matrix (Fin 3) (Fin 3) ℤ := !![7, 1, 1; 1, 2, 0; 1, 0, 2]

/-- A Gram matrix of the second class $c_4$ in the genus of $a_3 \oplus I_1$ (§9 (ii), p. 273). -/
def c4Gram : Matrix (Fin 4) (Fin 4) ℤ := !![2, -1, -1, 0; -1, 3, 0, -1; -1, 0, 3, -1; 0, -1, -1, 3]

theorem eval_a3 (x : Fin 3 → ℤ) : (ofMatrixZ a3Gram).eval x =
    5 * x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + (x 0 + x 1) ^ 2 + (x 0 + x 2) ^ 2 := by
  rw [eval_ofMatrixZ]
  simp [a3Gram, dotProduct, mulVec, Fin.sum_univ_three]
  ring

theorem eval_c4 (x : Fin 4 → ℤ) : (ofMatrixZ c4Gram).eval x =
    (x 0 - x 1) ^ 2 + (x 0 - x 2) ^ 2 + (x 1 - x 3) ^ 2 + (x 2 - x 3) ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 := by
  rw [eval_ofMatrixZ]
  simp [c4Gram, dotProduct, mulVec, Fin.sum_univ_four]
  ring

theorem posDef_a3 : IntQF.PosDef (ofMatrixZ a3Gram) := by
  intro x hx
  rw [eval_a3]
  have : x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext fun i => by fin_cases i <;> simp [h.1, h.2.1, h.2.2])
  rcases this with h | h | h <;> positivity

theorem posDef_c4 : IntQF.PosDef (ofMatrixZ c4Gram) := by
  intro x hx
  rw [eval_c4]
  by_cases h1 : x 1 ≠ 0
  · positivity
  by_cases h2 : x 2 ≠ 0
  · positivity
  by_cases h3 : x 3 ≠ 0
  · positivity
  push Not at h1 h2 h3
  have h0 : x 0 ≠ 0 := fun h0 => hx (funext fun i => by fin_cases i <;> simp [h0, h1, h2, h3])
  rw [h1, h2, h3]
  positivity

/-- $a_3$ is positive definite (rational form). -/
theorem posDefGram_a3 : PosDefGram a3Gram := by
  refine ⟨by decide, fun x hx => ?_⟩
  have e : x ⬝ᵥ (gramQ a3Gram *ᵥ x) =
      5 * x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + (x 0 + x 1) ^ 2 + (x 0 + x 2) ^ 2 := by
    simp [gramQ, a3Gram, dotProduct, mulVec, Fin.sum_univ_three]
    ring
  rw [e]
  have : x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext fun i => by fin_cases i <;> simp [h.1, h.2.1, h.2.2])
  rcases this with h | h | h <;> positivity

/-- $a_3$ has no vector of norm $1$: its norms are $\ge 5$ or even. -/
theorem a3_ne_one (x : Fin 3 → ℤ) : x ⬝ᵥ (a3Gram *ᵥ x) ≠ 1 := by
  have e := eval_a3 x
  rw [eval_ofMatrixZ] at e
  rw [e]
  by_cases h0 : x 0 = 0
  · rw [h0]
    have : (5 : ℤ) * 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + (0 + x 1) ^ 2 + (0 + x 2) ^ 2 = 2 * (x 1 ^ 2 + x 2 ^ 2) := by ring
    rw [this]
    omega
  · have h1 : 0 < x 0 ^ 2 := by positivity
    have h2 : 0 ≤ x 1 ^ 2 + x 2 ^ 2 + (x 0 + x 1) ^ 2 + (x 0 + x 2) ^ 2 := by positivity
    omega

theorem ex2Gram_eq_sumI : ex2Gram = sumI a3Gram 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- **$\lvert\mathrm{Aut}(a_3)\rvert = 16$** (certified enumeration). -/
theorem card_aut_a3 : Nat.card (Aut (ofMatrixZ a3Gram)) = 16 :=
  card_aut_eq_of_cert posDef_a3 (C := !![16, -8, -8; -8, 52, 4; -8, 4, 52]) (D := 192) (B := 1) (by decide +kernel)
    (by norm_num) (by decide +kernel)
    [!![-1, 0, 0; 0, -1, 0; 0, 0, -1], !![-1, 0, 0; 0, 0, -1; 0, -1, 0], !![-1, 0, 0; 0, -1, 0; 1, 0, 1],
      !![-1, 0, 0; 0, 0, -1; 1, 1, 0], !![-1, 0, 0; 1, 0, 1; 0, -1, 0], !![-1, 0, 0; 1, 1, 0; 0, 0, -1],
      !![-1, 0, 0; 1, 0, 1; 1, 1, 0], !![-1, 0, 0; 1, 1, 0; 1, 0, 1], !![1, 0, 0; -1, -1, 0; -1, 0, -1],
      !![1, 0, 0; -1, 0, -1; -1, -1, 0], !![1, 0, 0; -1, -1, 0; 0, 0, 1], !![1, 0, 0; -1, 0, -1; 0, 1, 0],
      !![1, 0, 0; 0, 0, 1; -1, -1, 0], !![1, 0, 0; 0, 1, 0; -1, 0, -1], !![1, 0, 0; 0, 0, 1; 0, 1, 0],
      !![1, 0, 0; 0, 1, 0; 0, 0, 1]] (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **$\lvert\mathrm{Aut}(a_3 \oplus I_1)\rvert = 32 = 2^2\cdot2\cdot2\cdot2$** (§9 (ii), p. 273). -/
@[kb "conwaysloane1988" "§9 (ii), p. 273 (|Aut(a₃ ⊕ I₁)| = 32)"]
theorem card_aut_ex2 : Nat.card (Aut (ofMatrixZ ex2Gram)) = 32 := by
  rw [ex2Gram_eq_sumI, card_aut_sumI posDefGram_a3 a3_ne_one 1, card_aut_a3]
  rfl

/-- **$\lvert\mathrm{Aut}(c_4)\rvert = 16 = 2\cdot8\cdot1$** (§9 (ii), p. 273; certified enumeration). -/
@[kb "conwaysloane1988" "§9 (ii), p. 273 (|Aut(c₄)| = 16)"]
theorem card_aut_c4 : Nat.card (Aut (ofMatrixZ c4Gram)) = 16 :=
  card_aut_eq_of_cert posDef_c4 (C := !![168, 72, 72, 48; 72, 104, 40, 48; 72, 40, 104, 48; 48, 48, 48, 96])
    (D := 384) (B := 1) (by decide +kernel) (by norm_num) (by decide +kernel)
    [!![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1], !![-1, 0, 0, 1; 0, -1, 0, 1; 0, 0, -1, 1; 0, 0, 0, 1],
      !![-1, 0, 0, 0; 0, 0, -1, 0; 0, -1, 0, 0; 0, 0, 0, -1], !![-1, 0, 0, 1; 0, 0, -1, 1; 0, -1, 0, 1; 0, 0, 0, 1],
      !![-1, 1, 1, -1; 0, 0, 1, -1; 0, 1, 0, -1; 0, 0, 0, -1], !![-1, 1, 1, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1],
      !![-1, 1, 1, -1; 0, 1, 0, -1; 0, 0, 1, -1; 0, 0, 0, -1], !![-1, 1, 1, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
      !![1, -1, -1, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1], !![1, -1, -1, 1; 0, -1, 0, 1; 0, 0, -1, 1; 0, 0, 0, 1],
      !![1, -1, -1, 0; 0, 0, -1, 0; 0, -1, 0, 0; 0, 0, 0, -1], !![1, -1, -1, 1; 0, 0, -1, 1; 0, -1, 0, 1; 0, 0, 0, 1],
      !![1, 0, 0, -1; 0, 0, 1, -1; 0, 1, 0, -1; 0, 0, 0, -1], !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1],
      !![1, 0, 0, -1; 0, 1, 0, -1; 0, 0, 1, -1; 0, 0, 0, -1], !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]]
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- $5 \nmid \det H_f = 384$ (certificate $H_f\,\mathrm{adj}(H_f) = 384\cdot1$). -/
theorem five_not_dvd_det_ex2 : ¬ ((5 : ℕ) : ℤ) ∣ (ofMatrixZ ex2Gram).hessian.det :=
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  DetCert.not_dvd_det (c := ⟨!![32, -16, -16, 0; -16, 104, 8, 0; -16, 8, 104, 0; 0, 0, 0, 192], 384⟩)
    (by decide +kernel)

/-- **The $5$-neighbour certificate** of $f = a_3 \oplus I_1$ at the isotropic vector $(11, 2, 0, 1)$, in a basis in which the
neighbour has Gram matrix `c4Gram` (output of the generator `Siegel.Kneser.Gen.nbDataTo`; checked by `decide`). -/
def c4Cert : NbCert 4 :=
  ⟨![11, 2, 0, 1], !![0, -3, 1, 0; -5, 4, 2, 0; 0, 0, -5, 5; 0, 2, -4, -5], ![0, 2, 1, 0], ![2, 0, 0, 0],
    !![504, 95, 70, 6; 567, 108, 79, 7; 126, 24, 17, 1; 126, 24, 18, 1], ![-16, -18, -4, -4], ![-4, -4, -1, -1],
    !![-8, -5, -2, -2; -9, 0, -1, -1; -2, 0, -3, -3; -2, 0, 2, -3]⟩

/-- **$c_4$ is in the genus of $a_3 \oplus I_1$** (§9 (ii), p. 273): it is a $5$-neighbour (certificate). -/
@[kb "conwaysloane1988" "§9 (ii), p. 273 (c₄ in the genus of a₃ ⊕ I₁)"]
theorem sameGenus_ex2_c4 : SameGenus (ofMatrixZ ex2Gram) (ofMatrixZ c4Gram) :=
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  NbCert.sameGenus (c := c4Cert) (by norm_num) five_not_dvd_det_ex2 (by decide +kernel)

theorem not_intEquiv_ex2_c4 : ¬ IntEquiv (ofMatrixZ ex2Gram) (ofMatrixZ c4Gram) := fun h => by
  have := card_aut_eq_of_intEquiv h
  rw [card_aut_ex2, card_aut_c4] at this
  norm_num at this

/-- The two classes as a family indexed by `Fin 2`: $f = a_3 \oplus I_1$, $g = c_4$. -/
def ex2Reps : Fin 2 → QuadForm ℤ 4 := ![ofMatrixZ ex2Gram, ofMatrixZ c4Gram]

theorem ex2Reps_distinct : ∀ i j, IntEquiv (ex2Reps i) (ex2Reps j) → i = j := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd h not_intEquiv_ex2_c4
  · exact absurd (IsometricGL.symm h) not_intEquiv_ex2_c4
  · rfl

/-- **§9 (ii), the two classes** (Conway–Sloane 1988, p. 273): the genus of $f = a_3 \oplus I_1$ consists of exactly two
$\mathrm{GL}_4(\mathbb Z)$-classes, those of $f$ and of $g = c_4$ (Gram matrix `c4Gram`); they are distinct,
$\lvert\mathrm{Aut}(f)\rvert = 32 = 2^2\cdot2\cdot2\cdot2$, $\lvert\mathrm{Aut}(g)\rvert = 16 = 2\cdot8\cdot1$, and
$\frac1{32} + \frac1{16} = \frac3{32} = m(f)$. Unconditional. -/
@[kb "conwaysloane1988" "§9 (ii), p. 273 (two classes a₃ ⊕ I₁ and c₄; 1/32 + 1/16 = 3/32)"]
theorem example_ii_two_classes :
    genusClasses (ofMatrixZ ex2Gram) = {classOf (ofMatrixZ ex2Gram), classOf (ofMatrixZ c4Gram)} ∧
      classOf (ofMatrixZ ex2Gram) ≠ classOf (ofMatrixZ c4Gram) ∧
      Nat.card (Aut (ofMatrixZ ex2Gram)) = 32 ∧ Nat.card (Aut (ofMatrixZ c4Gram)) = 16 ∧
      (1 / (2 ^ 2 * 2 * 2 * 2) + 1 / (2 * 8 * 1) : ℝ) = 3 / 32 ∧ Siegel.mass (ofMatrixZ ex2Gram) = 3 / 32 := by
  refine ⟨?_, fun h => not_intEquiv_ex2_c4 (classOf_eq_classOf_iff.mp h), card_aut_ex2, card_aut_c4,
    by norm_num, example_ii_mass⟩
  have h := genusClasses_eq_of_sum_eq_mass ex2Gram_posDef ex2Reps (fun i => by
      fin_cases i
      · exact SameGenus.refl _
      · exact sameGenus_ex2_c4) ex2Reps_distinct
    (by
      rw [example_ii_mass, Fin.sum_univ_two]
      simp only [ex2Reps, Matrix.cons_val_zero, Matrix.cons_val_one, card_aut_ex2, card_aut_c4]
      norm_num)
  rw [h]
  ext c
  simp [ex2Reps, Fin.exists_fin_two, eq_comm]

end QuadFormsKB.ConwaySloane.Mass
