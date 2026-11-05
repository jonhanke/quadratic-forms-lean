/-
# Conway–Sloane 1988, §9 (i): the genus of $\mathrm{diag}(7,1,1)$ has exactly two classes

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), §9 (i), p. 272 (bibliography key `conwaysloane1988`): "there are two forms in the genus of $f$, namely
$7_1 \oplus I_2 = f$ itself and $7_2 \oplus I_1 = g$. These forms have automorphism groups of orders 16 and 8
respectively, and indeed $\frac1{16} + \frac18 = \frac3{16}$."

**Conventions.** A form is its integral Gram matrix $A$, with quadratic form `LocalDensity.ofMatrixZ A`,
$\vec x \mapsto \vec x^{\mathsf T}A\vec x$ (variables $x_0, x_1, x_2$, 0-based). The two forms are
* $f = 7 \oplus I_2$, Gram matrix `ex1Gram` $= \mathrm{diag}(7, 1, 1)$, i.e. $f(\vec x) = 7x_0^2 + x_1^2 + x_2^2$;
* $g = 7_2 \oplus I_1$, Gram matrix `ex1gGram` $= \begin{pmatrix}2&1&0\\1&4&0\\0&0&1\end{pmatrix}$, i.e.
  $g(\vec x) = 2x_0^2 + 2x_0x_1 + 4x_1^2 + x_2^2$; here $7_2$ is the binary form of determinant $7$ with Gram
  matrix $\begin{pmatrix}2&1\\1&4\end{pmatrix}$.

Classes are $\mathrm{GL}_3(\mathbb Z)$-classes (`Siegel.classOf`), the genus is `Siegel.SameGenus` (equivalence over
every $\mathbb Z_p$ and over $\mathbb R$), $\lvert\mathrm{Aut}\rvert$ counts improper automorphisms too
(`Siegel.Aut`), and the mass is `Siegel.mass` $= \sum_{[f'] \in \mathrm{Gen}(f)} 1/\lvert\mathrm{Aut}(f')\rvert$.

**Proof (the paper's mass check, made rigorous).** The mass $m(f) = \frac3{16}$ is proved from the mass formula
(`example_i_mass_unconditional`). $g$ is in the genus of $f$, and $\lvert\mathrm{Aut}(f)\rvert = 16$,
$\lvert\mathrm{Aut}(g)\rvert = 8$: these are transported along explicit integral equivalences from the worked
example of the Kneser neighbour files (`Siegel.Kneser.Examples`: $x_0^2 + x_1^2 + 7x_2^2$ and
$x_0^2 + 2x_1^2 - 2x_1x_2 + 4x_2^2$, a $3$-neighbour pair with certified automorphism counts). So $f \not\sim g$, and
since $\frac1{16} + \frac18 = \frac3{16}$ equals the mass, a third class would add a positive term: the genus is
exactly $\{[f], [g]\}$ (`Siegel.Kneser.genusClasses_eq_of_sum_eq_mass`).

**Proves**
* `sameGenus_ex1_ex1g`: $g$ is in the genus of $f$;
* `card_aut_ex1`, `card_aut_ex1g`: $\lvert\mathrm{Aut}(f)\rvert = 16$, $\lvert\mathrm{Aut}(g)\rvert = 8$;
* `example_i_two_classes` (§9 (i), p. 272): the genus of $f$ is $\{[f], [g]\}$, $[f] \ne [g]$, and
  $\frac1{16} + \frac18 = \frac3{16} = m(f)$. Unconditional.
-/
import QuadFormsKB.Siegel.KneserExample
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicFinal

open Matrix QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.LocalDensity

namespace QuadFormsKB.ConwaySloane.Mass

open QuadFormsKB.Siegel.Kneser QuadFormsKB.Siegel.Kneser.Examples

/-- The Gram matrix $\begin{pmatrix}2&1&0\\1&4&0\\0&0&1\end{pmatrix}$ of $g = 7_2 \oplus I_1$ (§9 (i), p. 272), the second
class in the genus of $\mathrm{diag}(7,1,1)$. -/
def ex1gGram : Matrix (Fin 3) (Fin 3) ℤ := !![2, 1, 0; 1, 4, 0; 0, 0, 1]

/-- An element of $\mathrm{GL}_3(\mathbb Z)$ from a matrix and an explicit inverse. -/
def glOf (M N : Matrix (Fin 3) (Fin 3) ℤ) (h1 : M * N = 1) (h2 : N * M = 1) : GL (Fin 3) ℤ := ⟨M, N, h1, h2⟩

theorem eval_ex1 (x : Fin 3 → ℤ) : (ofMatrixZ ex1Gram).eval x = 7 * x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [eval_ofMatrixZ]
  simp [ex1Gram, dotProduct, mulVec, Fin.sum_univ_three, Matrix.diagonal]
  ring

theorem eval_ex1g (x : Fin 3 → ℤ) :
    (ofMatrixZ ex1gGram).eval x = 2 * x 0 ^ 2 + 2 * x 0 * x 1 + 4 * x 1 ^ 2 + x 2 ^ 2 := by
  rw [eval_ofMatrixZ]
  simp [ex1gGram, dotProduct, mulVec, Fin.sum_univ_three]
  ring

/-- $f = \mathrm{diag}(7,1,1)$ is equivalent to $x_0^2 + x_1^2 + 7x_2^2$ (cyclic permutation of the variables). -/
theorem intEquiv_ex1_Q₁ : IntEquiv (ofMatrixZ ex1Gram) Q₁ := by
  refine ⟨glOf !![0, 0, 1; 1, 0, 0; 0, 1, 0] !![0, 1, 0; 0, 0, 1; 1, 0, 0] (by decide) (by decide), fun x => ?_⟩
  rw [eval_ex1, eval_Q₁]
  simp [glOf, mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- $x_0^2 + 2x_1^2 - 2x_1x_2 + 4x_2^2$ is equivalent to $g = 7_2 \oplus I_1$. -/
theorem intEquiv_Q₂_ex1g : IntEquiv Q₂ (ofMatrixZ ex1gGram) := by
  refine ⟨glOf !![0, 0, 1; 1, 0, 0; 0, -1, 0] !![0, 1, 0; 0, 0, -1; 1, 0, 0] (by decide) (by decide), fun x => ?_⟩
  rw [eval_ex1g, eval_Q₂]
  simp [glOf, mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- $f = \mathrm{diag}(7,1,1)$ is positive definite. -/
theorem posDef_ex1 : IntQF.PosDef (ofMatrixZ ex1Gram) := by
  intro x hx
  rw [eval_ex1]
  rcases ne_zero_cases hx with h | h | h <;> positivity

/-- **$g = 7_2 \oplus I_1$ is in the genus of $f = \mathrm{diag}(7,1,1)$** (§9 (i), p. 272). -/
@[kb "conwaysloane1988" "§9 (i), p. 272 (7₂ ⊕ I₁ in the genus of diag(7,1,1))"]
theorem sameGenus_ex1_ex1g : SameGenus (ofMatrixZ ex1Gram) (ofMatrixZ ex1gGram) :=
  (intEquiv_ex1_Q₁.sameGenus.trans sameGenus_Q₁_Q₂).trans intEquiv_Q₂_ex1g.sameGenus

/-- **$\lvert\mathrm{Aut}(7 \oplus I_2)\rvert = 16$** (§9 (i), p. 272). -/
@[kb "conwaysloane1988" "§9 (i), p. 272 (|Aut(7 ⊕ I₂)| = 16)"]
theorem card_aut_ex1 : Nat.card (Aut (ofMatrixZ ex1Gram)) = 16 := by
  rw [card_aut_eq_of_intEquiv intEquiv_ex1_Q₁, card_aut_Q₁]

/-- **$\lvert\mathrm{Aut}(7_2 \oplus I_1)\rvert = 8$** (§9 (i), p. 272). -/
@[kb "conwaysloane1988" "§9 (i), p. 272 (|Aut(7₂ ⊕ I₁)| = 8)"]
theorem card_aut_ex1g : Nat.card (Aut (ofMatrixZ ex1gGram)) = 8 := by
  rw [← card_aut_eq_of_intEquiv intEquiv_Q₂_ex1g, card_aut_Q₂]

/-- $7 \oplus I_2 \not\sim 7_2 \oplus I_1$ (different automorphism counts). -/
theorem not_intEquiv_ex1_ex1g : ¬ IntEquiv (ofMatrixZ ex1Gram) (ofMatrixZ ex1gGram) := fun h => by
  have := card_aut_eq_of_intEquiv h
  rw [card_aut_ex1, card_aut_ex1g] at this
  norm_num at this

/-- The two classes, as a family indexed by `Fin 2`: $f = 7 \oplus I_2$, $g = 7_2 \oplus I_1$. -/
def ex1Reps : Fin 2 → QuadForm ℤ 3 := ![ofMatrixZ ex1Gram, ofMatrixZ ex1gGram]

theorem ex1Reps_distinct : ∀ i j, IntEquiv (ex1Reps i) (ex1Reps j) → i = j := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd h not_intEquiv_ex1_ex1g
  · exact absurd (IsometricGL.symm h) not_intEquiv_ex1_ex1g
  · rfl

theorem sum_ex1Reps : ∑ i, ((Nat.card (Aut (ex1Reps i)) : ℝ))⁻¹ = 3 / 16 := by
  rw [Fin.sum_univ_two]
  simp only [ex1Reps, Matrix.cons_val_zero, Matrix.cons_val_one, card_aut_ex1, card_aut_ex1g]
  norm_num

/-- **§9 (i), the two classes** (Conway–Sloane 1988, p. 272): the genus of $f = \mathrm{diag}(7,1,1)$ consists of exactly
two $\mathrm{GL}_3(\mathbb Z)$-classes, those of $f = 7 \oplus I_2$ and of $g = 7_2 \oplus I_1$ (Gram matrix
$\begin{pmatrix}2&1&0\\1&4&0\\0&0&1\end{pmatrix}$); they are distinct, $\lvert\mathrm{Aut}(f)\rvert = 16$,
$\lvert\mathrm{Aut}(g)\rvert = 8$, and $\frac1{16} + \frac18 = \frac3{16} = m(f)$. Unconditional: the mass $\frac3{16}$
comes from the proved mass formula (`example_i_mass_unconditional`), and a third class would make the mass larger. -/
@[kb "conwaysloane1988" "§9 (i), p. 272 (two classes 7 ⊕ I₂, 7₂ ⊕ I₁; 1/16 + 1/8 = 3/16)"]
theorem example_i_two_classes :
    genusClasses (ofMatrixZ ex1Gram) = {classOf (ofMatrixZ ex1Gram), classOf (ofMatrixZ ex1gGram)} ∧
      classOf (ofMatrixZ ex1Gram) ≠ classOf (ofMatrixZ ex1gGram) ∧
      Nat.card (Aut (ofMatrixZ ex1Gram)) = 16 ∧ Nat.card (Aut (ofMatrixZ ex1gGram)) = 8 ∧
      (1 / 16 + 1 / 8 : ℝ) = 3 / 16 ∧ Siegel.mass (ofMatrixZ ex1Gram) = 3 / 16 := by
  refine ⟨?_, fun h => not_intEquiv_ex1_ex1g (classOf_eq_classOf_iff.mp h), card_aut_ex1, card_aut_ex1g,
    by norm_num, example_i_mass_unconditional⟩
  have h := genusClasses_eq_of_sum_eq_mass posDef_ex1 ex1Reps (fun i => by
      fin_cases i
      · exact SameGenus.refl _
      · exact sameGenus_ex1_ex1g) ex1Reps_distinct
    (by rw [sum_ex1Reps, example_i_mass_unconditional])
  rw [h]
  ext c
  simp [ex1Reps, Fin.exists_fin_two, eq_comm]

end QuadFormsKB.ConwaySloane.Mass
