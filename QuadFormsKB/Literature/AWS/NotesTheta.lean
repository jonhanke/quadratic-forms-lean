/-
# Hanke, Arizona Winter School 2009 notes, Thm 2.2.2: the transformation law of $\Theta_{x^2}$ under $\Gamma_0(4)$

J. Hanke, *Quadratic Forms and Automorphic Forms*, notes from the 2009 Arizona Winter School,
arXiv:1105.5759 v3 (bibkey `hanke2011aws`; PDF page = printed page), §2.2, p. 27.

The theorem is cited by the notes (Shimura 1973, Prop. 2) and is a statement about modular forms of
half-integral weight, which the library does not cover; it is stated here as the named statement
`ThetaMultiplier` (not proved, not used as a hypothesis). The two symbols of the statement, $\varepsilon_d$ and the
extended quadratic symbol $\left(\frac{c}{d}\right)$, are defined and their basic values checked.
-/
import QuadFormsKB.Siegel.Theta

open Complex

namespace QuadFormsKB.AWS.Notes

/-- **Notes, Thm 2.2.2, p. 27:** $\varepsilon_d = 1$ if $d \equiv 1 \pmod 4$ and $\varepsilon_d = i$ if
$d \equiv 3 \pmod 4$ (for odd $d \in \mathbb Z$; the value $i$ is used for every $d \not\equiv 1$). -/
@[kb "hanke2011aws" "§2.2, Thm. 2.2.2, p. 27 (ε_d)"]
noncomputable def epsD (d : ℤ) : ℂ := if d % 4 = 1 then 1 else I

/-- **Notes, Thm 2.2.2, p. 27:** the extended quadratic symbol $\left(\frac{c}{d}\right)$ for odd $d$:
$\left(\frac{c}{|d|}\right)$ (Jacobi symbol), negated when both $c < 0$ and $d < 0$.

*Erratum:* the notes define it as $\left(\frac{c}{|d|}\right)$ "if $c > 0$
or $d > 0$" and $-\left(\frac{c}{|d|}\right)$ "if both $c, d < 0$", which leaves out $c = 0$, $d < 0$ (that is,
$\gamma = -I$, $d = -1$). Shimura's convention gives $\left(\frac{0}{-1}\right) = 1$, which this definition
follows; it is the value for which the transformation law holds at $\gamma = -I$. -/
@[kb "hanke2011aws" "§2.2, Thm. 2.2.2, p. 27 ((c/d))"]
def quadSym (c d : ℤ) : ℤ := if c < 0 ∧ d < 0 then -jacobiSym c d.natAbs else jacobiSym c d.natAbs

/-- **Named statement: Notes, Thm 2.2.2, p. 27** (Shimura 1973, (1.10) and Prop. 2). For every
$\gamma = \begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \mathrm{SL}_2(\mathbb Z)$ with $4 \mid c$ and every $z$ in
the upper half-plane,
$$\Theta_{x^2}\!\left(\frac{az+b}{cz+d}\right)
  = \varepsilon_d^{-1}\left(\frac{c}{d}\right)\sqrt{cz+d}\;\Theta_{x^2}(z),$$
with the principal square root, $-\pi/2 < \arg\sqrt{w} \le \pi/2$ (Mathlib's `w ^ (1/2 : ℂ)`), and
$\Theta_{x^2}(z) = \sum_{m \in \mathbb Z} e^{2\pi i m^2 z}$ = `Siegel.theta (Siegel.sumSq 1)`. Not proved here
(half-integral weight); not used as a hypothesis. -/
@[kb "hanke2011aws" "§2.2, Thm. 2.2.2, p. 27 (named statement)"]
structure ThetaMultiplier : Prop where
  transform : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : ℂ), 0 < z.im → (4 : ℤ) ∣ γ 1 0 →
    Siegel.theta (Siegel.sumSq 1) ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) =
      (epsD (γ 1 1))⁻¹ * (quadSym (γ 1 0) (γ 1 1) : ℂ) * (γ 1 0 * z + γ 1 1) ^ (1 / 2 : ℂ) *
        Siegel.theta (Siegel.sumSq 1) z

/-- Sanity check of the symbols at $\gamma = -I$: $\varepsilon_{-1}^{-1}\left(\frac{0}{-1}\right)\sqrt{-1} = 1$, so
the law of Thm 2.2.2 reads $\Theta_{x^2}(z) = \Theta_{x^2}(z)$ there. -/
theorem multiplier_neg_one : (epsD (-1))⁻¹ * (quadSym 0 (-1) : ℂ) * (-1 : ℂ) ^ (1 / 2 : ℂ) = 1 := by
  have h1 : epsD (-1) = I := by simp [epsD]
  have h2 : quadSym 0 (-1) = 1 := by simp [quadSym]
  have h3 : (-1 : ℂ) ^ (1 / 2 : ℂ) = I := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num), Complex.log_neg_one]
    have : ↑Real.pi * I * (1 / 2) = ↑(Real.pi / 2) * I := by push_cast; ring
    rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    simp
  rw [h1, h2, h3]
  simp

/-- Sanity check at $\gamma = T = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$: the multiplier is $1$, matching
$\Theta_{x^2}(z+1) = \Theta_{x^2}(z)$ of (2.1). -/
theorem multiplier_T : (epsD 1)⁻¹ * (quadSym 0 1 : ℂ) * (1 : ℂ) ^ (1 / 2 : ℂ) = 1 := by
  simp [epsD, quadSym]

end QuadFormsKB.AWS.Notes
