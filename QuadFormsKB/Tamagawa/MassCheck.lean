/-
# Cross-check of the mass formula over $\mathbb Q$: the $E_8$ lattice

**Layer:** real-number identities (no lattices).

The mass formula of `MassFormula.lean` over $F = \mathbb Q$ ($|d_\mathbb Q| = 1$, one real place) for an even unimodular
lattice of rank $8$ ($E_8$; Hessian = Gram matrix $G$, $\det G = 1$, Gram matrix of $Q$: $A = G/2$, $\det A = 2^{-8}$)
reads, with $\alpha_p = (1 - p^{-4})\prod_{i=1}^{3}(1 - p^{-2i})$ at **every** $p$ (the discriminant character is trivial),
$$\mathrm{Mass}(E_8) = \mathrm{vol}(SO_8(\mathbb R))^{-1}\,\zeta(2)\,\zeta(4)^2\,\zeta(6).$$
`e8_mass_check` proves that the right side equals $1/696729600 = 1/|W(E_8)|$, which is the known mass of $E_8$
(class number $1$, $O(E_8) = W(E_8)$; Conway–Sloane 1988, Table 2 [unverified]). This checks the conventions of
`archVolSO` (the factors $\tfrac12$, $2^{-n(n-1)/2}$ and $\det^{-(n+1)/2}$), the normalization $\mathrm{vol}(SO(L_p)) = \beta_p/2$
and the $SO$/$O$ factor $2$ together.

*Inputs not proved here:* $\alpha_p(E_8)$ at odd $p$ is generic by `volSO_good_even`; at $p = 2$ it is generic because
$E_8 \otimes \mathbb Z_2$ is even unimodular and $|O^+_8(\mathbb F_2)| = 2\cdot 2^{12}(2^4-1)\prod_{i=1}^3(2^{2i}-1)$, but our
$|O_n(\mathbb F_q)|$ (`OrthFq.lean`) covers only odd $q$. A check with $x_0^2 + x_1^2 + x_2^2 + x_3^2$ needs the dyadic
density $\alpha_2$ and is not done.
-/
import QuadFormsKB.Tamagawa.MassFormula

open Real

namespace QuadFormsKB.Tamagawa

theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd ⟨2, rfl⟩ (by norm_num)
  have c1 : Nat.choose 6 1 = 6 := by decide
  have c2 : Nat.choose 6 2 = 15 := by decide
  have c3 : Nat.choose 6 3 = 20 := by decide
  have c4 : Nat.choose 6 4 = 15 := by decide
  have c5 : Nat.choose 6 5 = 6 := by decide
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, c1, c2, c3, c4, c5, h5]

theorem zeta_two_re : (riemannZeta 2).re = π ^ 2 / 6 := by
  rw [riemannZeta_two]; norm_cast

theorem zeta_four_re : (riemannZeta 4).re = π ^ 4 / 90 := by
  rw [riemannZeta_four]; norm_cast

theorem zeta_six_re : (riemannZeta 6).re = π ^ 6 / 945 := by
  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  rw [show ((2 : ℂ) * ((3 : ℕ) : ℂ)) = 6 by norm_num] at h
  rw [h, bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_six]
  norm_num [Nat.factorial]
  norm_cast
  ring

/-- $\prod_{j=1}^{8}\pi^{j/2}/\Gamma(j/2) = 16\pi^{16}/135$. -/
theorem prod_pi_gamma_eight :
    ∏ j ∈ Finset.range 8, π ^ (((j : ℝ) + 1) / 2) / Gamma (((j : ℝ) + 1) / 2) = 16 * π ^ 16 / 135 := by
  have hs : (0 : ℝ) < √π := Real.sqrt_pos.mpr pi_pos
  have g1 : Gamma (1 / 2) = √π := Gamma_one_half_eq
  have g3 : Gamma (3 / 2) = 1 / 2 * √π := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Gamma_add_one (by norm_num), g1]
  have g5 : Gamma (5 / 2) = 3 / 2 * (1 / 2 * √π) := by
    rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Gamma_add_one (by norm_num), g3]
  have g7 : Gamma (7 / 2) = 5 / 2 * (3 / 2 * (1 / 2 * √π)) := by
    rw [show (7 / 2 : ℝ) = 5 / 2 + 1 by norm_num, Gamma_add_one (by norm_num), g5]
  have hp : ∀ k : ℕ, π ^ ((k : ℝ) + 1 / 2) = π ^ k * √π := fun k => by
    rw [Real.rpow_add pi_pos, Real.rpow_natCast, Real.sqrt_eq_rpow]
  have p1 : π ^ (1 / 2 : ℝ) = √π := (Real.sqrt_eq_rpow π).symm
  have p3 : π ^ (3 / 2 : ℝ) = π ^ 1 * √π := by rw [← hp 1]; norm_num
  have p5 : π ^ (5 / 2 : ℝ) = π ^ 2 * √π := by rw [← hp 2]; norm_num
  have p7 : π ^ (7 / 2 : ℝ) = π ^ 3 * √π := by rw [← hp 3]; norm_num
  have q : ∀ k : ℕ, π ^ (k : ℝ) = π ^ k := fun k => Real.rpow_natCast π k
  have q1 : π ^ (1 : ℝ) = π := Real.rpow_one π
  have q2 : π ^ (2 : ℝ) = π ^ 2 := by exact_mod_cast q 2
  have q3 : π ^ (3 : ℝ) = π ^ 3 := by exact_mod_cast q 3
  have q4 : π ^ (4 : ℝ) = π ^ 4 := by exact_mod_cast q 4
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  norm_num
  rw [g1, g3, g5, g7]
  field_simp
  rw [p1, p3, p5, p7]
  ring

/-- $\mathrm{vol}(SO_8(\mathbb R))$ for $\det A = 2^{-8}$ (the $E_8$ form): $2048\,\pi^{16}/135$. -/
theorem archVolSO_eight : archVolSO 8 ((2 : ℝ) ^ 8)⁻¹ = 2048 * π ^ 16 / 135 := by
  rw [archVolSO, prod_pi_gamma_eight]
  have h : (((2 : ℝ) ^ 8)⁻¹) ^ (-((8 : ℕ) + 1 : ℝ) / 2) = 2 ^ 36 := by
    rw [show ((2 : ℝ) ^ 8)⁻¹ = (2 : ℝ) ^ (-(8 : ℝ)) by
        rw [Real.rpow_neg (by norm_num), show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast],
      ← Real.rpow_mul (by norm_num), show -(8 : ℝ) * (-((8 : ℕ) + 1 : ℝ) / 2) = ((36 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  rw [h]
  norm_num
  ring

/-- **The $E_8$ cross-check of the mass formula** (see the module docstring):
$$\mathrm{vol}(SO_8(\mathbb R))^{-1}\,\zeta(2)\,\zeta(4)^2\,\zeta(6) = \frac{135}{2048\,\pi^{16}}\cdot\frac{\pi^{16}}{45927000}
  = \frac{1}{696729600} = \frac{1}{|W(E_8)|},$$
the right side of `massFormula` for $E_8$ over $\mathbb Q$ with the generic local factors
$\alpha_p = \zeta_p(2)^{-1}\zeta_p(4)^{-1}\zeta_p(6)^{-1}\cdot L_p(4, \chi_0)^{-1}$ at all $p$. -/
@[kb "conwaysloane1988" "Table 2 (mass of E8) [unverified]"]
theorem e8_mass_check :
    (archVolSO 8 ((2 : ℝ) ^ 8)⁻¹)⁻¹ * ((riemannZeta 2).re * (riemannZeta 4).re ^ 2 * (riemannZeta 6).re) =
      1 / 696729600 := by
  rw [archVolSO_eight, zeta_two_re, zeta_four_re, zeta_six_re]
  have : π ≠ 0 := pi_pos.ne'
  field_simp
  ring

end QuadFormsKB.Tamagawa
