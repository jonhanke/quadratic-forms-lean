/-
# Conway–Sloane 1988, §13: the forms $f$, $g$, $h$ and the transformation (20)

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), §13, p. 283 (bibliography key `conwaysloane1988`).

§13 explains the free/bound distinction of Table 1 with $f = \begin{pmatrix}2&1\\1&2\end{pmatrix}$ and
$g = f \oplus \langle 2\rangle$: both have the constituent $f_1 = g_1 = 2(x^2+xy+y^2)$ of type II, dimension 2 and
octane value 4 ($\mathrm{II}_2{:}4$), free for $f$ (species $2-$) and bound for $g$ (species 3) (`species_f_g`).
$g$ is 2-adically equivalent to $h = \begin{pmatrix}2&1&0\\1&4&0\\0&0&6/7\end{pmatrix}$ with $h_1 = 2(x^2+xy+2y^2)$ of
octane value 0 ($\mathrm{II}_2{:}0$); the basis is $e'_1 = e_1$, $e'_2 = e_2 + e_3$, $e'_3 = \ldots$.

*Erratum (candidate):* the transformation (20) is printed with third row $(\frac47, -\frac27, \frac37)$. With it the
new Gram matrix is not $h$ (in either reading of the matrix, `printed20_not_rows`, `printed20_not_cols`), and its
determinant is $\frac57$, so it is not invertible over $\mathbb Z_2$ with the right determinant. The row
$(\frac27, -\frac47, \frac37)$, i.e. $e'_3 = \frac17(2e_1 - 4e_2 + 3e_3)$, gives exactly $h$ (`corrected20`), has
determinant 1 and entries in $\mathbb Z_{(2)}$, and keeps the identity block $X_1$ that the paper's argument uses.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.PMass

namespace QuadFormsKB.ConwaySloane.Mass

open Matrix

/-- **§13, p. 283: $\mathrm{II}_2{:}4$ free has species $2-$, bound species 3; $\mathrm{II}_2{:}0$ free has species
$2+$** (Conway–Sloane 1988: "This explains the entry $2-$ for free forms $\mathrm{II}_2{:}4$ in table 1", "This
explains the entry 3 for bound forms $\mathrm{II}_2$"). The constituent $2(x^2+xy+y^2)$ has determinant $3$, sign $-$,
so its octane value is $4$; $2(x^2+xy+2y^2)$ has determinant $7$, sign $+$, octane value $0$. -/
@[kb "conwaysloane1988" "§13, p. 283 (f, g, h; Table 1 entries 2- and 3)"]
theorem species_f_g :
    twoSpecies ⟨2, .minus, .II, 0⟩ False = Species.minus 2 ∧
    twoSpecies ⟨2, .minus, .II, 0⟩ True = Species.odd 3 ∧
    twoSpecies ⟨2, .plus, .II, 0⟩ False = Species.plus 2 ∧
    octane ⟨2, .minus, .II, 0⟩ = 4 ∧ octane ⟨2, .plus, .II, 0⟩ = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The Gram matrix of $g = \begin{pmatrix}2&1\\1&2\end{pmatrix} \oplus \langle2\rangle$. -/
def gram13g : Matrix (Fin 3) (Fin 3) ℚ := !![2, 1, 0; 1, 2, 0; 0, 0, 2]

/-- The Gram matrix of $h$ (§13, p. 283). -/
def gram13h : Matrix (Fin 3) (Fin 3) ℚ := !![2, 1, 0; 1, 4, 0; 0, 0, 6 / 7]

/-- The transformation (20) as printed (rows: $e'_1, e'_2, e'_3$ in terms of $e_1, e_2, e_3$). -/
def printed20 : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 0; 0, 1, 1; 4 / 7, -2 / 7, 3 / 7]

/-- The corrected transformation: $e'_3 = \frac17(2e_1 - 4e_2 + 3e_3)$. -/
def corrected20 : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 0; 0, 1, 1; 2 / 7, -4 / 7, 3 / 7]

/-- **(20) corrected** (Conway–Sloane 1988, §13, p. 283): with $e'_1 = e_1$, $e'_2 = e_2 + e_3$,
$e'_3 = \frac17(2e_1 - 4e_2 + 3e_3)$ the Gram matrix of $g$ becomes $h$; the matrix has determinant 1 and its entries
have odd denominators, so $g$ and $h$ are 2-adically equivalent, and its $2\times2$ block $X_1$ is the identity. -/
@[kb "conwaysloane1988" "§13, (20), p. 283 (corrected)"]
theorem corrected20_spec : corrected20 * gram13g * corrected20ᵀ = gram13h ∧ corrected20.det = 1 := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [corrected20, gram13g, gram13h, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
  · simp [corrected20, Matrix.det_fin_three]; norm_num

/-- **(20) as printed does not transform $g$ into $h$** (rows read as the new basis vectors). -/
@[kb "conwaysloane1988" "§13, (20), p. 283 (erratum)"]
theorem printed20_not_rows : printed20 * gram13g * printed20ᵀ ≠ gram13h := by
  intro h
  have := congrFun (congrFun h 0) 2
  simp [printed20, gram13g, gram13h, Matrix.mul_apply, Fin.sum_univ_succ] at this
  norm_num at this

/-- **(20) as printed does not transform $g$ into $h$** (columns read as the new basis vectors), and its determinant is
$\frac57 \ne \pm1$. -/
@[kb "conwaysloane1988" "§13, (20), p. 283 (erratum)"]
theorem printed20_not_cols : printed20ᵀ * gram13g * printed20 ≠ gram13h ∧ printed20.det = 5 / 7 := by
  refine ⟨fun h => ?_, ?_⟩
  · have := congrFun (congrFun h 0) 0
    simp [printed20, gram13g, gram13h, Matrix.mul_apply, Fin.sum_univ_succ] at this
    try norm_num at this
  · simp [printed20, Matrix.det_fin_three]; norm_num

end QuadFormsKB.ConwaySloane.Mass
