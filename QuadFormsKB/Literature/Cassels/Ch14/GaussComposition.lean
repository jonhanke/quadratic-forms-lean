/-
# Cassels, Chapter 14: Gauss' definition of composition; Example 7 (i), (ii)

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, Notes, p. 354, and Examples, Ex. 7, pp. 360–361.

* (Notes, p. 354) Gauss' definition: the class of $f$ is the composition of the classes of $f_1, f_2$ if there are
  integral bilinear forms $X, Y$ in $(x_1, x_2)$, $(y_1, y_2)$ with $f_1(x_1, x_2)f_2(y_1, y_2) = f(X, Y)$
  identically (`IsGaussComposite`). Cassels says this is equivalent to Dirichlet's definition used in §2. Here the
  direction "Dirichlet's composition is a Gauss composition" is proved (`isGaussComposite_comp`, with
  $X = x_1y_1 - cx_2y_2$, $Y = a_1x_1y_2 + a_2x_2y_1 + bx_2y_2$). *Deviation:* Gauss' definition also imposes
  orientation conditions on $X, Y$ (so that the composition is the class, not its inverse); Cassels' paraphrase
  omits them, and so does `IsGaussComposite`. The converse direction is not formalized.
* (Ex. 7) With $g(x, y, z) = y^2 - xz$ and $f(x, y) = g(x\mathbf r + y\mathbf s)$ for a basis $\mathbf r, \mathbf s,
  \mathbf t$ of $\mathbb Z^3$ (Ex. 6), put $\mathbf e = \mathbf r \times \mathbf s$, i.e.
  $e_1 = r_2s_3 - r_3s_2$, $e_2 = r_3s_1 - r_1s_3$, $e_3 = r_1s_2 - r_2s_1$, and $h(x, y) = e_1x^2 - e_2xy + e_3y^2$.
  (i) $h$ is a primitive integral form of discriminant $D = \operatorname{disc} f$ (`ex7_h_isPrimitive`,
  `ex7_disc_h`). (ii) For an integral automorph $T$ of $g$ of the shape (5.6) of Chapter 13 with
  $\alpha\delta - \beta\gamma = 1$, the vectors $\mathbf r^* = T\mathbf r$, $\mathbf s^* = T\mathbf s$ again give $f$,
  and the form $h^*$ built from them is properly equivalent to $h$ (`ex7_h_star`), and every form properly equivalent to $h$ arises in this way (`ex7_ii_surj`). The formulas of Ex. 7 are lost
  in the machine-read text and were read from the page image (p. 360).
-/
import QuadFormsKB.Literature.Cassels.Ch14.Group
import QuadFormsKB.Literature.Cassels.Ch13.Sec5Matrix

namespace QuadFormsKB.Composition

open BinQF Binary Matrix

/-! ### Gauss' definition of composition (Notes, p. 354) -/

/-- **Gauss' definition of composition** (Cassels, Ch. 14, Notes, p. 354): there are integral bilinear forms
$X = \sum_{i,j} X_{ij}x_iy_j$, $Y = \sum_{i,j} Y_{ij}x_iy_j$ in $\vec x = (x_0, x_1)$, $\vec y = (y_0, y_1)$ with
$f_1(\vec x)f_2(\vec y) = f(X, Y)$ for all integral $\vec x, \vec y$. (Indices are $0$-based.) -/
@[kb "cassels1978" "Ch. 14, Notes, p. 354 (Gauss' definition of composition)"]
def IsGaussComposite (f₁ f₂ f : BinQF) : Prop :=
  ∃ X Y : Fin 2 → Fin 2 → ℤ, ∀ x y : Fin 2 → ℤ,
    f₁.eval (x 0) (x 1) * f₂.eval (y 0) (y 1) =
      f.eval (∑ i, ∑ j, X i j * x i * y j) (∑ i, ∑ j, Y i j * x i * y j)

/-- **Dirichlet's composition is a composition in Gauss' sense** (Cassels, Ch. 14, Notes, p. 354): for concordant
$f_1 = [a_1, b, a_2c]$, $f_2 = [a_2, b, a_1c]$ the composition $f_3 = [a_1a_2, b, c]$ (2.9) satisfies
$f_1(\vec x)f_2(\vec y) = f_3(x_0y_0 - cx_1y_1,\ a_1x_0y_1 + a_2x_1y_0 + bx_1y_1)$. -/
@[kb "cassels1978" "Ch. 14, Notes, p. 354 (Dirichlet's composition satisfies Gauss' definition)"]
theorem isGaussComposite_comp {f₁ f₂ : BinQF} (h : Concordant f₁ f₂) :
    IsGaussComposite f₁ f₂ (comp f₁ f₂) := by
  obtain ⟨h0, hb, hD, k, hk⟩ := h
  have ha₁ : f₁.a ≠ 0 := left_ne_zero_of_mul h0
  have ha₂ : f₂.a ≠ 0 := right_ne_zero_of_mul h0
  have h4 : 4 * f₁.a * f₂.a ≠ 0 := by
    intro h'; apply h0; linarith
  have hq : (f₁.b ^ 2 - f₁.disc) / (4 * f₁.a * f₂.a) = k := by
    rw [hk]; exact Int.mul_ediv_cancel_left _ h4
  have d1 : f₁.disc = f₁.b ^ 2 - 4 * f₁.a * f₁.c := rfl
  have d2 : f₂.disc = f₂.b ^ 2 - 4 * f₂.a * f₂.c := rfl
  have e1 : f₁.c = f₂.a * k := by
    apply mul_left_cancel₀ (show (4 * f₁.a : ℤ) ≠ 0 by intro h'; apply ha₁; linarith)
    linear_combination d1 + hk
  have e2 : f₂.c = f₁.a * k := by
    apply mul_left_cancel₀ (show (4 * f₂.a : ℤ) ≠ 0 by intro h'; apply ha₂; linarith)
    linear_combination d2 + hk - (f₁.b + f₂.b) * hb + hD
  refine ⟨![![1, 0], ![0, -k]], ![![0, f₁.a], ![f₂.a, f₁.b]], fun x y => ?_⟩
  simp only [BinQF.eval_eq, comp, a_mk, b_mk, c_mk]
  rw [hq]
  simp only [Fin.sum_univ_two, e1, e2, hb]
  simp
  ring

/-! ### Example 7 -/

/-- The form $g(x, y, z) = y^2 - xz$ of Ex. 6–7 (indices $0, 1, 2$ for $x, y, z$). -/
def gEx6 (v : Fin 3 → ℤ) : ℤ := v 1 ^ 2 - v 0 * v 2

/-- The binary form $f(x, y) = g(x\mathbf r + y\mathbf s)$ of Ex. 6–7:
$[r_1^2 - r_0r_2,\ 2r_1s_1 - r_0s_2 - r_2s_0,\ s_1^2 - s_0s_2]$ ($0$-based indices). -/
def fOfRS (r s : Fin 3 → ℤ) : BinQF :=
  BinQF.mk (r 1 ^ 2 - r 0 * r 2) (2 * r 1 * s 1 - r 0 * s 2 - r 2 * s 0) (s 1 ^ 2 - s 0 * s 2)

theorem fOfRS_eval (r s : Fin 3 → ℤ) (x y : ℤ) : (fOfRS r s).eval x y = gEx6 (x • r + y • s) := by
  simp only [BinQF.eval_eq, fOfRS, gEx6, a_mk, b_mk, c_mk, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Cassels' form $h$ of Ex. 7** (p. 360): $h(x, y) = e_1x^2 - e_2xy + e_3y^2$ with $\mathbf e = \mathbf r \times
\mathbf s$; in $0$-based indices $e_1 = r_1s_2 - r_2s_1$, $e_2 = r_2s_0 - r_0s_2$, $e_3 = r_0s_1 - r_1s_0$. -/
@[kb "cassels1978" "Ch. 14, Ex. 7, p. 360 (the form h = e₁x² − e₂xy + e₃y²)"]
def hOfRS (r s : Fin 3 → ℤ) : BinQF :=
  BinQF.mk (r 1 * s 2 - r 2 * s 1) (-(r 2 * s 0 - r 0 * s 2)) (r 0 * s 1 - r 1 * s 0)

/-- **Cassels, Ch. 14, Ex. 7 (i)** (p. 360), discriminant: *$h$ has the discriminant $D$ of $f$.* (An identity in
$\mathbf r, \mathbf s$.) -/
@[kb "cassels1978" "Ch. 14, Ex. 7 (i), p. 360 (h has discriminant D)"]
theorem ex7_disc_h (r s : Fin 3 → ℤ) : (hOfRS r s).disc = (fOfRS r s).disc := by
  simp only [hOfRS, fOfRS, BinQF.disc, BinQF.a_mk, BinQF.b_mk, BinQF.c_mk]
  ring

/-- **Cassels, Ch. 14, Ex. 7 (i)** (p. 360), primitivity: *if $\mathbf r, \mathbf s, \mathbf t$ is a basis of
$\mathbb Z^3$, then $h$ is primitive.* The basis condition is $\det(\mathbf r, \mathbf s, \mathbf t) = \pm 1$. -/
@[kb "cassels1978" "Ch. 14, Ex. 7 (i), p. 360 (h is primitive)"]
theorem ex7_h_isPrimitive (r s t : Fin 3 → ℤ) (hb : IsUnit (Matrix.of ![r, s, t]).det) :
    (hOfRS r s).IsPrimitive := by
  have h : (Matrix.of ![r, s, t]).det = t 0 * (r 1 * s 2 - r 2 * s 1) + t 1 * (r 2 * s 0 - r 0 * s 2)
      + t 2 * (r 0 * s 1 - r 1 * s 0) := by
    rw [Matrix.det_fin_three]; simp; ring
  intro d h1 h2 h3
  simp only [hOfRS, BinQF.a_mk, BinQF.b_mk, BinQF.c_mk] at h1 h2 h3
  have h2' : d ∣ r 2 * s 0 - r 0 * s 2 := (dvd_neg).mp h2
  have : d ∣ (Matrix.of ![r, s, t]).det := by
    rw [h]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h2' _))
      (dvd_mul_of_dvd_right h3 _)
  exact isUnit_of_dvd_unit this hb

/-- **The automorph (5.6) of Chapter 13 of $g = y^2 - xz$** attached to $\begin{pmatrix}\alpha&\beta\\
\gamma&\delta\end{pmatrix}$ with $\alpha\delta - \beta\gamma = 1$: the matrix of the action on binary quadratic
forms $(x, y, z) \leftrightarrow$ the symmetric square, $T = \begin{pmatrix} \alpha^2 & 2\alpha\gamma & \gamma^2 \\
\alpha\beta & \alpha\delta + \beta\gamma & \gamma\delta \\ \beta^2 & 2\beta\delta & \delta^2 \end{pmatrix}$, so
that $g(T\vec v) = (\alpha\delta - \beta\gamma)^2 g(\vec v)$ (Cassels' (5.6) divides by $\lambda = \alpha\delta -
\beta\gamma = 1$). This is Chapter 13's `Cassels.Ch13.symSq` of $\begin{pmatrix}\alpha&\gamma\\\beta&\delta
\end{pmatrix}$; no new matrix is defined. -/
abbrev autG (α β γ δ : ℤ) : Matrix (Fin 3) (Fin 3) ℤ := Cassels.Ch13.symSq !![α, γ; β, δ]

/-- **The substitution behind Ex. 7 (ii)**: $h^* = h \circ \begin{pmatrix}\delta&\gamma\\\beta&\alpha\end{pmatrix}$
for $\mathbf r^* = T\mathbf r$, $\mathbf s^* = T\mathbf s$, $T$ = (5.6) with $\alpha\delta - \beta\gamma = 1$. -/
theorem subst_hOfRS_autG (r s : Fin 3 → ℤ) {α β γ δ : ℤ} (hdet : α * δ - β * γ = 1) :
    BinQF.subst δ γ β α (hOfRS r s) = hOfRS (autG α β γ δ *ᵥ r) (autG α β γ δ *ᵥ s) := by
  apply BinQF.ext_abc
  · simp only [a_subst, hOfRS, a_mk, b_mk, c_mk]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Cassels.Ch13.symSq]
    linear_combination (-((r 1 * s 2 - r 2 * s 1) * δ ^ 2 - (r 2 * s 0 - r 0 * s 2) * δ * β
      + (r 0 * s 1 - r 1 * s 0) * β ^ 2)) * hdet
  · simp only [b_subst, hOfRS, a_mk, b_mk, c_mk]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Cassels.Ch13.symSq]
    linear_combination (-(2 * (r 1 * s 2 - r 2 * s 1) * δ * γ
      - (r 2 * s 0 - r 0 * s 2) * (δ * α + γ * β) + 2 * (r 0 * s 1 - r 1 * s 0) * β * α)) * hdet
  · simp only [c_subst, hOfRS, a_mk, b_mk, c_mk]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Cassels.Ch13.symSq]
    linear_combination (-((r 1 * s 2 - r 2 * s 1) * γ ^ 2 - (r 2 * s 0 - r 0 * s 2) * γ * α
      + (r 0 * s 1 - r 1 * s 0) * α ^ 2)) * hdet

/-- **Cassels, Ch. 14, Ex. 7 (ii)** (pp. 360–361): *for an integral automorph $T$ of $g$ given by (5.6) of Chapter 13
with $\alpha\delta - \beta\gamma = 1$, put $\mathbf r^* = T\mathbf r$, $\mathbf s^* = T\mathbf s$. Then
$g(x\mathbf r^* + y\mathbf s^*) = f(x, y)$, and the form $h^*$ built from $\mathbf r^*, \mathbf s^*$ is properly
equivalent to $h$.* (The converse part of (ii), that every form properly equivalent to $h$ arises in this way, is
`ex7_ii_surj`.) -/
@[kb "cassels1978" "Ch. 14, Ex. 7 (ii), pp. 360–361 (r* = Tr, s* = Ts give f again and h* ∼ h)"]
theorem ex7_h_star (r s : Fin 3 → ℤ) {α β γ δ : ℤ} (hdet : α * δ - β * γ = 1) :
    fOfRS (autG α β γ δ *ᵥ r) (autG α β γ δ *ᵥ s) = fOfRS r s ∧
      SLEquiv (hOfRS r s) (hOfRS (autG α β γ δ *ᵥ r) (autG α β γ δ *ᵥ s)) := by
  constructor
  · apply BinQF.ext_abc
    · simp only [fOfRS, a_mk]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Cassels.Ch13.symSq]
      linear_combination (r 1 ^ 2 - r 0 * r 2) * (α * δ - β * γ + 1) * hdet
    · simp only [fOfRS, b_mk]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Cassels.Ch13.symSq]
      linear_combination (2 * r 1 * s 1 - r 0 * s 2 - r 2 * s 0) * (α * δ - β * γ + 1) * hdet
    · simp only [fOfRS, c_mk]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Cassels.Ch13.symSq]
      linear_combination (s 1 ^ 2 - s 0 * s 2) * (α * δ - β * γ + 1) * hdet
  · exact (sLEquiv_iff _ _).mpr ⟨δ, γ, β, α, by linear_combination hdet, subst_hOfRS_autG r s hdet⟩

/-- **Cassels, Ch. 14, Ex. 7 (ii)** (p. 361), second part: *every form properly equivalent to $h$ occurs as $h^*$ for an
appropriate automorph $T$* (5.6) with $\alpha\delta - \beta\gamma = 1$. -/
@[kb "cassels1978" "Ch. 14, Ex. 7 (ii), p. 361 (every form properly equivalent to h is some h*)"]
theorem ex7_ii_surj (r s : Fin 3 → ℤ) {h' : BinQF} (h : SLEquiv (hOfRS r s) h') :
    ∃ α β γ δ : ℤ, α * δ - β * γ = 1 ∧ hOfRS (autG α β γ δ *ᵥ r) (autG α β γ δ *ᵥ s) = h' := by
  obtain ⟨p, q, r', s', hd, rfl⟩ := (sLEquiv_iff _ _).mp h
  exact ⟨s', r', q, p, by linear_combination hd, (subst_hOfRS_autG r s (by linear_combination hd)).symm⟩

end QuadFormsKB.Composition
