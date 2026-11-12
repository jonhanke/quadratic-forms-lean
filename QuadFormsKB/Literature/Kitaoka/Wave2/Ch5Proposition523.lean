/-
# Kitaoka 1993, Proposition 5.2.3: ternary diagonal lattices over $\mathbb Z_2$

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §5.2, Proposition 5.2.3, pp. 78–79, with
Lemma 5.2.6, p. 77 (printed pages).

**Proves** `Padic.proposition523 : Padic.Proposition523`: for units $\epsilon_0, \epsilon_1, \epsilon_2$ of
$\mathbb Z_2$,
$$\langle\epsilon_0\rangle \perp \langle\epsilon_1\rangle \perp \langle\epsilon_2\rangle \cong
\begin{pmatrix} 2a & 1 \\ 1 & 2a\end{pmatrix} \perp \langle\epsilon\rangle,\qquad a \in \{0, 1\},\ \epsilon \in
\mathbb Z_2^\times,$$
and $2x^2 + 2xy + 2y^2$ is anisotropic over $\mathbb Q_2$ (Kitaoka's indices $1, 2, 3$ are $0, 1, 2$ here).

*Proof.* As in the book, $M = \mathbb Z_2[v_0 + v_1, v_1 + v_2]$ has Gram matrix
$G = \begin{pmatrix} 2c & b \\ b & 2d\end{pmatrix}$ with $2c = \epsilon_0 + \epsilon_1$, $b = \epsilon_1$,
$2d = \epsilon_1 + \epsilon_2$ (units of $\mathbb Z_2$ are odd), and $L = M \perp M^\perp$ with
$M^\perp = \mathbb Z_2 e$, $e = (-\epsilon_1\epsilon_2, \epsilon_0\epsilon_2, -\epsilon_0\epsilon_1)$,
$Q(e) = \epsilon_0\epsilon_1\epsilon_2(\epsilon_1\epsilon_2 + \epsilon_0\epsilon_2 + \epsilon_0\epsilon_1)$, a unit.
Kitaoka identifies $M$ through Lemma 5.2.6 (maximal lattices); here the basis is found directly with Hensel's lemma
(Mathlib `hensels_lemma`):
* if $c$ or $d$ is even, $cx^2 + bx + d = 0$ (or $dy^2 + by + c = 0$) has a root, giving an isotropic primitive
  $z$; with $w' = \beta^{-1}(1, 0)$, $\beta = B(z, (1, 0))$, the vector $w = w' - c\beta^{-2}z$ gives
  $\begin{pmatrix} 0 & 1 \\ 1 & 0\end{pmatrix}$ ($a = 0$);
* if $c$ and $d$ are odd, $cx^2 + bx + d - 1 = 0$ gives $z$ with $Q(z) = 2$; with $w_0 = \beta^{-1}(1, 0)$,
  $Q(w_0) = 2c'$ ($c'$ odd), a root $y$ of $3y^2 + 3y + 1 - c' = 0$ gives $w = (1 + 2y)^{-1}(w_0 + yz)$ with
  $Q(w) = 2$, $B(z, w) = 1$ ($a = 1$).
The change of basis has unit determinant because $\det(P)^2\det\operatorname{diag}(\epsilon) = (4a^2 - 1)\epsilon$.
Anisotropy: $t^2 + t + 1 = 0$ has no root in $\mathbb Q_2$ (for $\|t\| > 1$ the term $t^2$ dominates; for
$t \in \mathbb Z_2$ reduce modulo $2$).
-/
import QuadFormsKB.Literature.Kitaoka.Ch5Dyadic
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms

open Matrix Polynomial

noncomputable section

namespace QuadFormsKB.Kitaoka.Padic

/-- Every element of $\mathbb Z_2$ is even or odd. -/
theorem even_or_odd₂ (x : ℤ_[2]) : (∃ k, x = 2 * k) ∨ ∃ k, x = 2 * k + 1 := by
  have hmem : ∀ y : ℤ_[2], PadicInt.toZMod y = 0 → ∃ k, y = 2 * k := by
    intro y hy
    have : y ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
      rw [← PadicInt.ker_toZMod, RingHom.mem_ker]; exact hy
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at this
    obtain ⟨k, hk⟩ := this
    exact ⟨k, by rw [← hk]; push_cast; ring⟩
  have : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases this (PadicInt.toZMod x) with h | h
  · exact Or.inl (hmem x h)
  · right
    obtain ⟨k, hk⟩ := hmem (x - 1) (by rw [map_sub, h, map_one, sub_self])
    exact ⟨k, by linear_combination hk⟩

theorem not_isUnit_two_mul (k : ℤ_[2]) : ¬ IsUnit (2 * k) := by
  rw [PadicInt.isUnit_iff, norm_mul]
  have h2 : ‖(2 : ℤ_[2])‖ = 1 / 2 := by
    have := PadicInt.norm_p (p := 2); push_cast at this; rw [this]; norm_num
  rw [h2]
  have := PadicInt.norm_le_one k
  intro h; linarith

theorem isUnit_odd (k : ℤ_[2]) : IsUnit (2 * k + 1) := by
  rw [← IsLocalRing.notMem_maximalIdeal, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton']
  rintro ⟨a, ha⟩
  have : IsUnit (1 : ℤ_[2]) := isUnit_one
  rw [show (1 : ℤ_[2]) = 2 * (a - k) by push_cast at ha; linear_combination (-1 : ℤ_[2]) * ha] at this
  exact not_isUnit_two_mul _ this

theorem odd_of_isUnit {u : ℤ_[2]} (hu : IsUnit u) : ∃ k, u = 2 * k + 1 := by
  rcases even_or_odd₂ u with ⟨k, rfl⟩ | h
  · exact absurd hu (not_isUnit_two_mul k)
  · exact h

/-- **Hensel's lemma for $cx^2 + bx + e$** with $b$ a unit and $e$ even: there is a root in $\mathbb Z_2$. -/
theorem exists_root_quad (c b e : ℤ_[2]) (hb : IsUnit b) (he : ∃ k, e = 2 * k) :
    ∃ x : ℤ_[2], c * x ^ 2 + b * x + e = 0 := by
  obtain ⟨k, rfl⟩ := he
  let F : Polynomial ℤ_[2] := C c * X ^ 2 + C b * X + C (2 * k)
  have hF0 : F.aeval (0 : ℤ_[2]) = 2 * k := by simp [F]
  have hF'0 : F.derivative.aeval (0 : ℤ_[2]) = b := by simp [F]
  have hnorm : ‖F.aeval (0 : ℤ_[2])‖ < ‖F.derivative.aeval (0 : ℤ_[2])‖ ^ 2 := by
    rw [hF0, hF'0, (PadicInt.isUnit_iff.mp hb), one_pow]
    by_contra h
    exact not_isUnit_two_mul k (PadicInt.isUnit_iff.mpr (le_antisymm (PadicInt.norm_le_one _) (not_lt.mp h)))
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  exact ⟨z, by simpa [F] using hz⟩

/-- The binary core: vectors $z, w$ (coordinates in the basis $v_0 + v_1, v_1 + v_2$) with $Q(z) = Q(w) = 2a$ and
$B(z, w) = 1$, $a \in \{0, 1\}$. -/
theorem exists_binary_core (c b d : ℤ_[2]) (hb : IsUnit b) :
    ∃ z₁ z₂ w₁ w₂ a : ℤ_[2], (a = 0 ∨ a = 1) ∧
      2 * c * z₁ ^ 2 + 2 * b * z₁ * z₂ + 2 * d * z₂ ^ 2 = 2 * a ∧
      2 * c * w₁ ^ 2 + 2 * b * w₁ * w₂ + 2 * d * w₂ ^ 2 = 2 * a ∧
      2 * c * z₁ * w₁ + b * (z₁ * w₂ + z₂ * w₁) + 2 * d * z₂ * w₂ = 1 := by
  obtain ⟨kb, hkb⟩ := odd_of_isUnit hb
  rcases even_or_odd₂ d with hde | hdo
  · -- isotropic: c x² + b x + d = 0, z = (x, 1)
    obtain ⟨x, hx⟩ := exists_root_quad c b d hb hde
    obtain ⟨βu, hβ⟩ := isUnit_odd (c * x + kb)
    set βi : ℤ_[2] := ↑βu⁻¹
    have hβi : βi * (2 * c * x + b) = 1 := by
      rw [hkb, show 2 * c * x + (2 * kb + 1) = 2 * (c * x + kb) + 1 by ring, ← hβ]; exact βu.inv_mul
    refine ⟨x, 1, βi - c * βi ^ 2 * x, -(c * βi ^ 2), 0, Or.inl rfl, ?_, ?_, ?_⟩
    · linear_combination 2 * hx
    · linear_combination (2 * c ^ 2 * βi ^ 4) * hx + (-(2 * c * βi ^ 2)) * hβi
    · linear_combination (-(c * βi ^ 2) * 2) * hx + hβi
  · rcases even_or_odd₂ c with hce | hco
    · -- isotropic: d y² + b y + c = 0, z = (1, y)
      obtain ⟨y, hy⟩ := exists_root_quad d b c hb hce
      obtain ⟨βu, hβ⟩ := isUnit_odd (d * y + kb)
      set βi : ℤ_[2] := ↑βu⁻¹
      have hβi : βi * (2 * d * y + b) = 1 := by
        rw [hkb, show 2 * d * y + (2 * kb + 1) = 2 * (d * y + kb) + 1 by ring, ← hβ]; exact βu.inv_mul
      refine ⟨1, y, -(d * βi ^ 2), βi - d * βi ^ 2 * y, 0, Or.inl rfl, ?_, ?_, ?_⟩
      · linear_combination 2 * hy
      · linear_combination (2 * d ^ 2 * βi ^ 4) * hy + (-(2 * d * βi ^ 2)) * hβi
      · linear_combination (-(d * βi ^ 2) * 2) * hy + hβi
    · -- anisotropic: c x² + b x + (d - 1) = 0, z = (x, 1), Q(z) = 2
      obtain ⟨kd, hkd⟩ := hdo
      obtain ⟨kc, hkc⟩ := hco
      obtain ⟨x, hx⟩ := exists_root_quad c b (d - 1) hb ⟨kd, by rw [hkd]; ring⟩
      obtain ⟨βu, hβ⟩ := isUnit_odd (c * x + kb)
      set β : ℤ_[2] := 2 * c * x + b with hβdef
      set βi : ℤ_[2] := ↑βu⁻¹
      have hβi : βi * β = 1 := by
        rw [hβdef, hkb, show 2 * c * x + (2 * kb + 1) = 2 * (c * x + kb) + 1 by ring, ← hβ]; exact βu.inv_mul
      -- c' = c βi² is odd
      obtain ⟨kβ, hkβ⟩ := odd_of_isUnit (βu⁻¹.isUnit)
      have hc' : ∃ k, 1 - c * βi ^ 2 = 2 * k := by
        refine ⟨-(kc + 2 * kβ * (2 * kc + 1) + 2 * kβ ^ 2 * (2 * kc + 1)), ?_⟩
        rw [hkc, show βi = 2 * kβ + 1 from hkβ]; ring
      have h3 : IsUnit (3 : ℤ_[2]) := by have := isUnit_odd (1 : ℤ_[2]); norm_num at this; exact this
      obtain ⟨y, hy⟩ := exists_root_quad 3 3 (1 - c * βi ^ 2) h3 hc'
      obtain ⟨γu, hγ⟩ := isUnit_odd y
      set γi : ℤ_[2] := ↑γu⁻¹
      have hγi : γi * (2 * y + 1) = 1 := by rw [← hγ]; exact γu.inv_mul
      refine ⟨x, 1, γi * (βi + y * x), γi * y, 1, Or.inr rfl, ?_, ?_, ?_⟩
      · linear_combination 2 * hx
      · -- Q(w) = γi² (Q(w₀) + 2y B(w₀, z) + y² Q(z)) = γi² (2cβi² + 2y + 2y²) = 2
        linear_combination (2 * (γi * (2 * y + 1) + 1)) * hγi + (-(2 * γi ^ 2)) * hy +
          (2 * y * γi ^ 2) * hβi + (2 * y ^ 2 * γi ^ 2) * hx
      · linear_combination (γi * y * 2) * hx + γi * hβi + hγi

/-- The binary core in the coordinates of $L$: with $2c = \epsilon_0 + \epsilon_1$, $b = \epsilon_1$,
$2d = \epsilon_1 + \epsilon_2$. -/
theorem exists_binary (ε : Fin 3 → ℤ_[2]) (hε : ∀ i, IsUnit (ε i)) :
    ∃ z₁ z₂ w₁ w₂ a : ℤ_[2], (a = 0 ∨ a = 1) ∧
      ε 0 * z₁ ^ 2 + ε 1 * (z₁ + z₂) ^ 2 + ε 2 * z₂ ^ 2 = 2 * a ∧
      ε 0 * w₁ ^ 2 + ε 1 * (w₁ + w₂) ^ 2 + ε 2 * w₂ ^ 2 = 2 * a ∧
      ε 0 * z₁ * w₁ + ε 1 * (z₁ + z₂) * (w₁ + w₂) + ε 2 * z₂ * w₂ = 1 := by
  obtain ⟨k₀, hk₀⟩ := odd_of_isUnit (hε 0)
  obtain ⟨k₁, hk₁⟩ := odd_of_isUnit (hε 1)
  obtain ⟨k₂, hk₂⟩ := odd_of_isUnit (hε 2)
  obtain ⟨z₁, z₂, w₁, w₂, a, ha, hz, hw, hzw⟩ := exists_binary_core (k₀ + k₁ + 1) (ε 1) (k₁ + k₂ + 1) (hε 1)
  refine ⟨z₁, z₂, w₁, w₂, a, ha, ?_, ?_, ?_⟩
  · rw [← hz, hk₀, hk₂, hk₁]; ring
  · rw [← hw, hk₀, hk₂, hk₁]; ring
  · rw [← hzw, hk₀, hk₂, hk₁]; ring

/-- $t^2 + t + 1$ has no root in $\mathbb Q_2$. -/
theorem no_root_t2t1 (t : ℚ_[2]) : t ^ 2 + t + 1 ≠ 0 := by
  intro h
  by_cases ht : ‖t‖ ≤ 1
  · set s : ℤ_[2] := ⟨t, ht⟩
    have hs : s ^ 2 + s + 1 = 0 := by
      apply Subtype.ext
      simp only [PadicInt.coe_add, PadicInt.coe_pow, PadicInt.coe_one, PadicInt.coe_zero]
      exact h
    have := congrArg (PadicInt.toZMod (p := 2)) hs
    simp only [map_add, map_pow, map_one, map_zero] at this
    have key : ∀ z : ZMod 2, z ^ 2 + z + 1 ≠ 0 := by decide
    exact key _ this
  · push Not at ht
    have h1 : ‖t + 1‖ < ‖t ^ 2‖ := by
      calc ‖t + 1‖ ≤ max ‖t‖ ‖(1 : ℚ_[2])‖ := Padic.nonarchimedean t 1
        _ = ‖t‖ := by rw [norm_one, max_eq_left ht.le]
        _ < ‖t‖ * ‖t‖ := lt_mul_of_one_lt_right (by linarith) ht
        _ = ‖t ^ 2‖ := by rw [norm_pow, sq]
    have h2 : ‖t ^ 2 + (t + 1)‖ = ‖t ^ 2‖ := by
      rw [add_comm]; exact Padic.add_eq_max_of_ne (ne_of_lt h1) |>.trans (max_eq_right h1.le)
    rw [← add_assoc, h, norm_zero, norm_pow] at h2
    have : 0 < ‖t‖ := by linarith
    nlinarith

/-- **Kitaoka 1993, Proposition 5.2.3** (pp. 78–79), *proved*. -/
@[kb "kitaoka1993" "§5.2, Prop. 5.2.3, p. 78"]
theorem proposition523 : Proposition523 := by
  intro ε hε
  obtain ⟨z₁, z₂, w₁, w₂, a, ha, hz, hw, hzw⟩ := exists_binary ε hε
  set e : ℤ_[2] := ε 0 * ε 1 * ε 2 * (ε 1 * ε 2 + ε 0 * ε 2 + ε 0 * ε 1) with he
  have hεe : IsUnit (ε 1 * ε 2 + ε 0 * ε 2 + ε 0 * ε 1) := by
    obtain ⟨k₀, hk₀⟩ := odd_of_isUnit (hε 0)
    obtain ⟨k₁, hk₁⟩ := odd_of_isUnit (hε 1)
    obtain ⟨k₂, hk₂⟩ := odd_of_isUnit (hε 2)
    rw [hk₀, hk₁, hk₂]
    convert isUnit_odd (2 * k₁ * k₂ + k₁ + k₂ + 2 * k₀ * k₂ + k₀ + k₂ + 2 * k₀ * k₁ + k₀ + k₁ + 1) using 1
    ring
  have heu : IsUnit e := (((hε 0).mul (hε 1)).mul (hε 2)).mul hεe
  let P : Matrix (Fin 3) (Fin 3) ℤ_[2] :=
    !![z₁, w₁, -(ε 1 * ε 2); z₁ + z₂, w₁ + w₂, ε 0 * ε 2; z₂, w₂, -(ε 0 * ε 1)]
  have hP : Pᵀ * diagonal ε * P = !![2 * a, 1, 0; 1, 2 * a, 0; 0, 0, e] := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [P, Matrix.mul_apply, Fin.sum_univ_three, diagonal_apply, he] <;>
      first
        | linear_combination hz
        | linear_combination hw
        | linear_combination hzw
        | ring
  refine ⟨e, a, heu, ha, ⟨P, ?_, hP⟩, ?_⟩
  · have hdet := congrArg Matrix.det hP
    rw [det_mul, det_mul, det_transpose, det_diagonal, Fin.prod_univ_three] at hdet
    have hrhs : IsUnit (Matrix.det !![2 * a, 1, 0; 1, 2 * a, 0; 0, 0, e]) := by
      rw [det_fin_three]
      simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
        cons_val_fin_one, head_cons, head_fin_const, tail_cons]
      convert (isUnit_odd (2 * a ^ 2 - 1)).mul heu using 1
      ring
    rw [← hdet] at hrhs
    rw [show P.det * (ε 0 * ε 1 * ε 2) * P.det = P.det * (P.det * (ε 0 * ε 1 * ε 2)) by ring] at hrhs
    exact isUnit_of_mul_isUnit_left hrhs
  · rintro rfl x y hxy
    by_contra hne
    by_cases hy : y = 0
    · subst hy
      apply hne
      refine ⟨?_, rfl⟩
      have : (2 : ℚ_[2]) * x ^ 2 = 0 := by linear_combination hxy
      simpa using this
    · apply no_root_t2t1 (x / y)
      field_simp
      linear_combination hxy / 2

end QuadFormsKB.Kitaoka.Padic
