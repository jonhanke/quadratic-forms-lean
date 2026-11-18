import QuadFormsKB.Historical.Gauss.Opposite

/-!
# Transformations along chains of neighbours; transformations between forms of square determinant (*Disquisitiones Arithmeticae*, Arts. 177 and 208)

Two statements from the historical sources.

* (Art. 177), proved: if $F^{(k)} = (a^{(k)}, b^{(k)}, a^{(k+1)})$ is a chain of right neighbours
  (Art. 160: $b^{(k)} + b^{(k+1)} = h^{(k+1)} a^{(k+1)}$, all of one determinant), then the explicit recursion
  `chainMatrix` gives proper transformations of $F^{(0)}$ into $F^{(k)}$ (`subst_chainMatrix`,
  `chainMatrix_det`). Gauss's recursion starts at $k = 1$ with $(0, -1, 1, h')$; here the sequences are 0-based and
  start at the identity $(1, 0, 0, 1)$ for $k = 0$, from which the same recursion gives $(0, -1, 1, h^{(1)})$ at
  $k = 1$, so the formulas coincide with Gauss's for $k \ge 1$. About "provided no $a^{(k)}$ vanishes": see
  `chain_third_coefficient`; the exact hypothesis needed is the third-coefficient relation
  $a^{(k+2)} = a^{(k)} - 2 b^{(k)} h^{(k+1)} + a^{(k+1)} (h^{(k+1)})^2$, which follows from equal determinants
  exactly when $a^{(k+1)} \neq 0$.
* (Art. 208), proved except as noted: `transform_between_of_common_target` (the composition formula,
  any determinant), `closed_formula_of_common_target` (a closed formula of the type in the historical sources, **reconstructed**,
  see its docstring: it is not verified against Gauss's text, in particular the symbols $f, g, f', g'$ there
  are not defined in the historical sources), and `improper_between_of_common_target` (improper transformations from a
  proper one for the opposite form).
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary

/-! ### Art. 177: the transformation along a chain of right neighbours -/

/-- **The transformation matrices along a chain of right neighbours** (*Disq. Arith.*
Art. 177): given the integers $h^{(1)}, h^{(2)}, \dots$ (`h 1`, `h 2`, ... ; `h 0` is unused), the quadruple
$(\alpha^{(k)}, \beta^{(k)}, \gamma^{(k)}, \delta^{(k)})$ with $(\alpha^{(0)}, \beta^{(0)}, \gamma^{(0)},
\delta^{(0)}) = (1, 0, 0, 1)$ and
$$\alpha^{(k+1)} = \beta^{(k)},\quad \beta^{(k+1)} = h^{(k+1)}\beta^{(k)} - \alpha^{(k)},\quad
\gamma^{(k+1)} = \delta^{(k)},\quad \delta^{(k+1)} = h^{(k+1)}\delta^{(k)} - \gamma^{(k)}.$$
Gauss starts at $k = 1$ with $(0, -1, 1, h')$; this is what the recursion gives at $k = 1$ from the identity at
$k = 0$. -/
@[kb "gauss1801" "Art. 177"]
def chainMatrix (h : ℕ → ℤ) : ℕ → ℤ × ℤ × ℤ × ℤ
  | 0 => (1, 0, 0, 1)
  | k + 1 =>
    ((chainMatrix h k).2.1, h (k + 1) * (chainMatrix h k).2.1 - (chainMatrix h k).1,
      (chainMatrix h k).2.2.2, h (k + 1) * (chainMatrix h k).2.2.2 - (chainMatrix h k).2.2.1)

/-- The entry $\alpha^{(k)}$ of `chainMatrix`. -/
def chainAlpha (h : ℕ → ℤ) (k : ℕ) : ℤ := (chainMatrix h k).1
/-- The entry $\beta^{(k)}$ of `chainMatrix`. -/
def chainBeta (h : ℕ → ℤ) (k : ℕ) : ℤ := (chainMatrix h k).2.1
/-- The entry $\gamma^{(k)}$ of `chainMatrix`. -/
def chainGamma (h : ℕ → ℤ) (k : ℕ) : ℤ := (chainMatrix h k).2.2.1
/-- The entry $\delta^{(k)}$ of `chainMatrix`. -/
def chainDelta (h : ℕ → ℤ) (k : ℕ) : ℤ := (chainMatrix h k).2.2.2

/-- **The recursion of Art. 177, entrywise:** $\alpha^{(k+1)} = \beta^{(k)}$,
$\beta^{(k+1)} = h^{(k+1)}\beta^{(k)} - \alpha^{(k)}$, $\gamma^{(k+1)} = \delta^{(k)}$,
$\delta^{(k+1)} = h^{(k+1)}\delta^{(k)} - \gamma^{(k)}$, and the initial values
$(\alpha^{(1)}, \beta^{(1)}, \gamma^{(1)}, \delta^{(1)}) = (0, -1, 1, h^{(1)})$ of Gauss. -/
theorem chainMatrix_succ (h : ℕ → ℤ) (k : ℕ) :
    chainAlpha h (k + 1) = chainBeta h k ∧
    chainBeta h (k + 1) = h (k + 1) * chainBeta h k - chainAlpha h k ∧
    chainGamma h (k + 1) = chainDelta h k ∧
    chainDelta h (k + 1) = h (k + 1) * chainDelta h k - chainGamma h k :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Gauss's initial values $(0, -1, 1, h')$ at $k = 1$. -/
theorem chainMatrix_one (h : ℕ → ℤ) :
    chainMatrix h 1 = (0, -1, 1, h 1) := by
  simp [chainMatrix]

/-- **Every matrix of the chain has determinant $1$** (*Disq. Arith.* Art. 177): the
transformations are proper. No hypothesis on the forms is needed. -/
@[kb "gauss1801" "Art. 177"]
theorem chainMatrix_det (h : ℕ → ℤ) (k : ℕ) :
    chainAlpha h k * chainDelta h k - chainBeta h k * chainGamma h k = 1 := by
  induction k with
  | zero => simp [chainAlpha, chainBeta, chainGamma, chainDelta, chainMatrix]
  | succ k ih =>
    obtain ⟨h1, h2, h3, h4⟩ := chainMatrix_succ h k
    rw [h1, h2, h3, h4]
    linear_combination ih

/-- One step: the proper substitution $(0, -1, 1, h)$ takes $(a, b, c)$ to
$(c,\; h c - b,\; a - 2 b h + c h^2)$. -/
theorem subst_neighbour_step (a b c h : ℤ) :
    subst 0 (-1) 1 h (gaussForm a b c) = gaussForm c (h * c - b) (a - 2 * b * h + c * h ^ 2) := by
  rw [subst_gaussForm]
  congr 1 <;> ring

/-- **The transformation along a chain of right neighbours** (*Disq. Arith.* Art. 177):
let $F^{(k)} = (a^{(k)}, b^{(k)}, a^{(k+1)})$, with $a^{(k+1)} h^{(k+1)} = b^{(k)} + b^{(k+1)}$ (so that
$F^{(k+1)}$ is a right neighbour of $F^{(k)}$, Art. 160) and with third coefficients satisfying
$a^{(k+2)} = a^{(k)} - 2 b^{(k)} h^{(k+1)} + a^{(k+1)} (h^{(k+1)})^2$ (the value forced by the determinant when
$a^{(k+1)} \ne 0$, see `chain_third_coefficient`). Then the substitution `chainMatrix h k` takes $F^{(0)}$ to
$F^{(k)}$ for every $k$ (and it is proper by `chainMatrix_det`). Proved for any determinant, with no condition that
the $a^{(k)}$ be non-zero beyond what is built into the third-coefficient relation `ha`. Indices are 0-based:
Gauss's $F, F', F'', \dots$ are $F^{(0)}, F^{(1)}, F^{(2)}, \dots$. -/
@[kb "gauss1801" "Art. 177"]
theorem subst_chainMatrix (a b h : ℕ → ℤ)
    (hb : ∀ k, a (k + 1) * h (k + 1) = b k + b (k + 1))
    (ha : ∀ k, a (k + 2) = a k - 2 * b k * h (k + 1) + a (k + 1) * h (k + 1) ^ 2) (k : ℕ) :
    subst (chainAlpha h k) (chainBeta h k) (chainGamma h k) (chainDelta h k) (gaussForm (a 0) (b 0) (a 1)) =
      gaussForm (a k) (b k) (a (k + 1)) := by
  induction k with
  | zero => simpa [chainAlpha, chainBeta, chainGamma, chainDelta, chainMatrix] using subst_one _
  | succ k ih =>
    obtain ⟨h1, h2, h3, h4⟩ := chainMatrix_succ h k
    have hstep : subst 0 (-1) 1 (h (k + 1)) (gaussForm (a k) (b k) (a (k + 1))) =
        gaussForm (a (k + 1)) (b (k + 1)) (a (k + 2)) := by
      rw [subst_neighbour_step]
      have e1 : h (k + 1) * a (k + 1) - b k = b (k + 1) := by linarith [hb k]
      rw [e1, ← ha k]
    rw [h1, h2, h3, h4, ← hstep, ← ih, subst_subst]
    congr 1 <;> ring

/-- **The third coefficient is forced by the determinant exactly when the middle neighbour coefficient is
non-zero** (*Disq. Arith.* Art. 177, "provided no $a^{(k)}$ vanishes"): if
$a^{(k+1)} h^{(k+1)} = b^{(k)} + b^{(k+1)}$, $a^{(k+1)} \ne 0$, and $(a^{(k)}, b^{(k)}, a^{(k+1)})$ and
$(a^{(k+1)}, b^{(k+1)}, a^{(k+2)})$ have the same determinant, then
$a^{(k+2)} = a^{(k)} - 2 b^{(k)} h^{(k+1)} + a^{(k+1)} (h^{(k+1)})^2$. If $a^{(k+1)} = 0$ this fails (take
$a^{(k+1)} = 0$, $b^{(k+1)} = -b^{(k)}$, any $h^{(k+1)}$: the determinants agree for every $a^{(k+2)}$), so for
chains through a vanishing $a^{(k+1)}$ the relation `ha` of `subst_chainMatrix` must be assumed rather than derived.
Hence Gauss's proviso is needed only to know that $F^{(k+1)}$ is a form of the same determinant *with the third
coefficient given by the neighbour step*; the transformation formulas themselves need only `ha`. -/
@[kb "gauss1801" "Art. 177"]
theorem chain_third_coefficient {a₀ a₁ a₂ b₀ b₁ h : ℤ} (hb : a₁ * h = b₀ + b₁) (hne : a₁ ≠ 0)
    (hdet : gaussDet a₀ b₀ a₁ = gaussDet a₁ b₁ a₂) :
    a₂ = a₀ - 2 * b₀ * h + a₁ * h ^ 2 := by
  unfold gaussDet at hdet
  have hb' : b₁ = a₁ * h - b₀ := by linarith
  apply mul_left_cancel₀ hne
  linear_combination hdet + (b₁ + a₁ * h - b₀) * hb'

/-- **The chain theorem for forms of a common determinant** (*Disq. Arith.* Art. 177):
the same as `subst_chainMatrix`, with the third-coefficient relation replaced by the hypotheses of Gauss: all
$a^{(k)} \ne 0$ for $k \ge 1$ and all forms $F^{(k)}$ of the same determinant as $F^{(0)}$. -/
@[kb "gauss1801" "Art. 177"]
theorem subst_chainMatrix_of_det (a b h : ℕ → ℤ)
    (hb : ∀ k, a (k + 1) * h (k + 1) = b k + b (k + 1))
    (hne : ∀ k, a (k + 1) ≠ 0)
    (hdet : ∀ k, gaussDet (a k) (b k) (a (k + 1)) = gaussDet (a 0) (b 0) (a 1)) (k : ℕ) :
    subst (chainAlpha h k) (chainBeta h k) (chainGamma h k) (chainDelta h k) (gaussForm (a 0) (b 0) (a 1)) =
      gaussForm (a k) (b k) (a (k + 1)) :=
  subst_chainMatrix a b h hb
    (fun k => chain_third_coefficient (hb k) (hne k) (by rw [hdet k, hdet (k + 1)])) k

/-! ### Art. 208: transformations between forms of square determinant -/

/-- **Transformation between two forms with a common target** (first part; *Disq. Arith.*
Art. 208): if $F$ and $F'$ are carried to the same form $\Phi$ by the proper substitutions $(\alpha, \beta, \gamma,
\delta)$ and $(\alpha', \beta', \gamma', \delta')$, then $F$ is carried to $F'$ by the proper substitution
$$(\alpha\delta' - \beta\gamma',\; \beta\alpha' - \alpha\beta',\; \gamma\delta' - \delta\gamma',\;
\delta\alpha' - \gamma\beta')$$
(the first substitution followed by the inverse of the second). This is pure algebra: it holds for arbitrary
binary forms of any determinant (Gauss applies it to square determinants, with $\Phi$ the reduced form of
Arts. 206-207). -/
@[kb "gauss1801" "Art. 208"]
theorem transform_between_of_common_target {F F' Φ : BinQF} {α β γ δ α' β' γ' δ' : ℤ}
    (hd : α * δ - β * γ = 1) (hd' : α' * δ' - β' * γ' = 1)
    (h : subst α β γ δ F = Φ) (h' : subst α' β' γ' δ' F' = Φ) :
    (α * δ' - β * γ') * (δ * α' - γ * β') - (β * α' - α * β') * (γ * δ' - δ * γ') = 1 ∧
    subst (α * δ' - β * γ') (β * α' - α * β') (γ * δ' - δ * γ') (δ * α' - γ * β') F = F' := by
  refine ⟨?_, ?_⟩
  · have e : (α * δ' - β * γ') * (δ * α' - γ * β') - (β * α' - α * β') * (γ * δ' - δ * γ') =
        (α * δ - β * γ) * (α' * δ' - β' * γ') := by ring
    rw [e, hd, hd', one_mul]
  have e : subst δ' (-β') (-γ') α' Φ = F' := by
    rw [← h', subst_subst]
    have e1 : α' * δ' + β' * -γ' = 1 := by linear_combination hd'
    have e4 : γ' * -β' + δ' * α' = 1 := by linear_combination hd'
    have e2 : α' * -β' + β' * α' = 0 := by ring
    have e3 : γ' * δ' + δ' * -γ' = 0 := by ring
    rw [e1, e2, e3, e4, subst_one]
  rw [← e, ← h, subst_subst]
  congr 1 <;> ring

/-- **A closed formula for the transformation between forms of square determinant** (the historical sources,
second part; *Disq. Arith.* Art. 208). **Reconstructed**, not verified against Gauss's text: the historical sources
give the formula in terms of unexplained symbols $f, g, f', g'$ with denominator $2h$. Here $F = (a, b, c)$,
$F' = (a', b', c')$ are carried by proper substitutions $(\alpha, \beta, \gamma, \delta)$,
$(\alpha', \beta', \gamma', \delta')$ to the same form $(A, h, 0)$ (of square determinant $h^2$, the reduced form
of Arts. 206-207). Put $f = a\alpha + b\gamma$, $g = b\alpha + c\gamma$, $f' = a'\alpha' + b'\gamma'$,
$g' = b'\alpha' + c'\gamma'$ (half the partial derivatives of $F$, $F'$ at the first columns). Then the four entries
$N_{11}, N_{12}, N_{21}, N_{22}$ of `transform_between_of_common_target` satisfy
$$h N_{11} = \beta f' + \delta' g,\quad h N_{12} = \beta g' - \beta' g,\quad
h N_{21} = \delta f' - \delta' f,\quad h N_{22} = \beta' f + \delta g'.$$
With Gauss's $2h$ these are the formulas of the historical sources if his $f, g, f', g'$ are $2(a\alpha + b\gamma)$,
$-2(b\alpha + c\gamma)$ and the primed analogues (their signs of $g, g'$ then agree with ours); we could not
confirm this. The right-hand sides still involve the first columns $(\alpha, \gamma)$, $(\alpha', \gamma')$ of the
substitutions, though not the reduced form itself; the third coefficient of the reduced form is not used. -/
@[kb "gauss1801" "Art. 208"]
theorem closed_formula_of_common_target {a b c a' b' c' A h α β γ δ α' β' γ' δ' : ℤ}
    (hd : α * δ - β * γ = 1) (hd' : α' * δ' - β' * γ' = 1)
    (hF : subst α β γ δ (gaussForm a b c) = gaussForm A h 0)
    (hF' : subst α' β' γ' δ' (gaussForm a' b' c') = gaussForm A h 0) :
    h * (α * δ' - β * γ') = β * (a' * α' + b' * γ') + δ' * (b * α + c * γ) ∧
    h * (β * α' - α * β') = β * (b' * α' + c' * γ') - β' * (b * α + c * γ) ∧
    h * (γ * δ' - δ * γ') = δ * (a' * α' + b' * γ') - δ' * (a * α + b * γ) ∧
    h * (δ * α' - γ * β') = β' * (a * α + b * γ) + δ * (b' * α' + c' * γ') := by
  rw [subst_gaussForm] at hF hF'
  obtain ⟨hA, hH, -⟩ := gaussForm_inj hF
  obtain ⟨hA', hH', -⟩ := gaussForm_inj hF'
  -- `A δ - h γ = (aα + bγ)·det` and `h α - A β = (bα + cγ)·det`, and the primed analogues.
  have f1 : a * α + b * γ = A * δ - h * γ := by
    rw [← hA, ← hH]; linear_combination (-(a * α + b * γ)) * hd
  have g1 : b * α + c * γ = h * α - A * β := by
    rw [← hA, ← hH]; linear_combination (-(b * α + c * γ)) * hd
  have f2 : a' * α' + b' * γ' = A * δ' - h * γ' := by
    rw [← hA', ← hH']; linear_combination (-(a' * α' + b' * γ')) * hd'
  have g2 : b' * α' + c' * γ' = h * α' - A * β' := by
    rw [← hA', ← hH']; linear_combination (-(b' * α' + c' * γ')) * hd'
  rw [f1, g1, f2, g2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- **Improper transformations between forms of square determinant** (third part;
*Disq. Arith.* Art. 208, end): if $F$ is carried to the common form $\Phi$ by a proper substitution and the
opposite form of $F'$ is carried to $\Phi$ by a proper substitution, then there is an improper substitution
(determinant $-1$), namely $(N_{11}, -N_{12}, N_{21}, -N_{22})$ with $N$ as in `transform_between_of_common_target`
(for $F$ and the opposite of $F'$), carrying $F$ to $F'$. Proved for arbitrary binary forms. -/
@[kb "gauss1801" "Art. 208"]
theorem improper_between_of_common_target {F F' Φ : BinQF} {α β γ δ α' β' γ' δ' : ℤ}
    (hd : α * δ - β * γ = 1) (hd' : α' * δ' - β' * γ' = 1)
    (h : subst α β γ δ F = Φ) (h' : subst α' β' γ' δ' (conjForm F') = Φ) :
    (α * δ' - β * γ') * (-(δ * α' - γ * β')) - (-(β * α' - α * β')) * (γ * δ' - δ * γ') = -1 ∧
    subst (α * δ' - β * γ') (-(β * α' - α * β')) (γ * δ' - δ * γ') (-(δ * α' - γ * β')) F = F' := by
  obtain ⟨hdet, hsub⟩ := transform_between_of_common_target hd hd' h h'
  have := improper_of_proper_opposite (f := F') hdet hsub
  exact this

end QuadFormsKB.Historical.Gauss
