/-
# A Möbius identity for Eisenstein constant terms

`tsum_moebius_mul`: for bounded $\varphi : \mathbb{N} \to \mathbb{C}$,
$$\sum_{g \ge 1}\frac{\mu(g)}{g^2}\sum_{n \ge 1}\frac{\varphi(gn)}{n^2} = \varphi(1)$$
(group the absolutely convergent double sum by $m = gn$ and use $\sum_{g \mid m}\mu(g) = [m = 1]$).

`moebCoeff N r` $= \sum_{g \ge 1,\ g \equiv r \bmod N}\mu(g)g^{-2}$ and `moebius_const`: for $\varphi : \mathbb{Z}/N \to \mathbb{C}$ even,
$$\sum_{r \in \mathbb{Z}/N}\mathrm{moebCoeff}(r)\sum_{n \in \mathbb{Z}}\frac{\varphi(rn)}{n^2} = 2\varphi(1).$$
This is how the "primitive" Eisenstein series $\sum_{(c,d) = 1}W(c,d)(cz+d)^{-2}$ is written as the finite combination
$\sum_r \mathrm{moebCoeff}(r)E_{W(r\,\cdot)}$ of the series $E_W$ of `EisensteinWt2`.
-/
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.PSeries
import Mathlib.Data.ZMod.Basic
import QuadFormsKB.Citation

open Complex Filter Topology ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Siegel.GenusEis

lemma summable_pnat_inv_sq : Summable fun g : ℕ+ => ((((g : ℕ) : ℝ)) ^ 2)⁻¹ :=
  (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).comp_injective PNat.coe_injective

lemma norm_inv_sq_pnat (g : ℕ+) : ‖((((g : ℕ) : ℂ)) ^ 2)⁻¹‖ = ((((g : ℕ) : ℝ)) ^ 2)⁻¹ := by
  rw [norm_inv, norm_pow, Complex.norm_natCast]

lemma summable_bdd_mul_inv_sq {φ : ℕ+ → ℂ} {B : ℝ} (hB : ∀ n, ‖φ n‖ ≤ B) :
    Summable fun n : ℕ+ => φ n * ((((n : ℕ) : ℂ)) ^ 2)⁻¹ :=
  Summable.of_norm_bounded (summable_pnat_inv_sq.mul_left B) fun n => by
    rw [norm_mul, norm_inv_sq_pnat]
    exact mul_le_mul_of_nonneg_right (hB n) (by positivity)

lemma sum_moebius_divisorsAntidiagonal (m : ℕ+) :
    ∑ x ∈ Nat.divisorsAntidiagonal (m : ℕ), (μ x.1 : ℂ) = if (m : ℕ) = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f (m : ℕ)) (coe_moebius_mul_coe_zeta (R := ℂ))
  simp only [mul_apply, natCoe_apply, zeta_apply] at h
  rw [one_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx2 : x.2 ≠ 0 := by
    have := Nat.mem_divisorsAntidiagonal.mp hx
    intro h0; rw [h0, mul_zero] at this; exact m.ne_zero this.1.symm
  simp [hx2, intCoe_apply]

/-- **The Möbius identity:** $\sum_{g \ge 1}\mu(g)g^{-2}\sum_{n \ge 1}\varphi(gn)n^{-2} = \varphi(1)$ for bounded $\varphi$. -/
theorem tsum_moebius_mul (φ : ℕ → ℂ) {B : ℝ} (hB : ∀ n, ‖φ n‖ ≤ B) :
    ∑' g : ℕ+, (μ (g : ℕ) : ℂ) * ((((g : ℕ) : ℂ)) ^ 2)⁻¹ *
        ∑' n : ℕ+, φ ((g : ℕ) * (n : ℕ)) * ((((n : ℕ) : ℂ)) ^ 2)⁻¹ = φ 1 := by
  set F : ℕ+ × ℕ+ → ℂ := fun p =>
    (μ (p.1 : ℕ) : ℂ) * (φ ((p.1 : ℕ) * (p.2 : ℕ)) * (((((p.1 : ℕ) * (p.2 : ℕ) : ℕ) : ℂ)) ^ 2)⁻¹) with hF
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hFbd : ∀ p : ℕ+ × ℕ+, ‖F p‖ ≤ B * (((((p.1 : ℕ) : ℝ)) ^ 2)⁻¹ * ((((p.2 : ℕ) : ℝ)) ^ 2)⁻¹) := by
    intro p
    simp only [hF, norm_mul]
    have hμ : ‖(μ (p.1 : ℕ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast abs_moebius_le_one
    have e : ‖(((((p.1 : ℕ) * (p.2 : ℕ) : ℕ) : ℂ)) ^ 2)⁻¹‖ =
        ((((p.1 : ℕ) : ℝ)) ^ 2)⁻¹ * ((((p.2 : ℕ) : ℝ)) ^ 2)⁻¹ := by
      rw [norm_inv, norm_pow, Complex.norm_natCast]; push_cast; rw [mul_pow, mul_inv]
    rw [e]
    calc ‖(μ (p.1 : ℕ) : ℂ)‖ * (‖φ ((p.1 : ℕ) * (p.2 : ℕ))‖ *
          (((((p.1 : ℕ) : ℝ)) ^ 2)⁻¹ * ((((p.2 : ℕ) : ℝ)) ^ 2)⁻¹))
        ≤ 1 * (B * (((((p.1 : ℕ) : ℝ)) ^ 2)⁻¹ * ((((p.2 : ℕ) : ℝ)) ^ 2)⁻¹)) := by
          gcongr; exact hB _
      _ = _ := one_mul _
  have hsum : Summable F :=
    Summable.of_norm_bounded ((summable_pnat_inv_sq.mul_of_nonneg summable_pnat_inv_sq
      (fun _ => by positivity) (fun _ => by positivity)).mul_left B) hFbd
  -- the left side is the iterated sum of `F`
  have hL : ∀ g : ℕ+, (μ (g : ℕ) : ℂ) * ((((g : ℕ) : ℂ)) ^ 2)⁻¹ *
      ∑' n : ℕ+, φ ((g : ℕ) * (n : ℕ)) * ((((n : ℕ) : ℂ)) ^ 2)⁻¹ = ∑' n : ℕ+, F (g, n) := by
    intro g
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [hF]; push_cast; rw [mul_pow, mul_inv]; ring
  rw [tsum_congr hL, ← hsum.tsum_prod' (fun g => hsum.prod_factor g)]
  -- regroup by `m = g n`
  rw [← sigmaAntidiagonalEquivProd.tsum_eq]
  have hsig : Summable (F ∘ sigmaAntidiagonalEquivProd) :=
    (sigmaAntidiagonalEquivProd.summable_iff).mpr hsum
  rw [Summable.tsum_sigma' (f := fun c => F (sigmaAntidiagonalEquivProd c))
    (fun m => (hasSum_fintype _).summable) hsig]
  have hfib : ∀ m : ℕ+, ∑' x : Nat.divisorsAntidiagonal (m : ℕ), F (sigmaAntidiagonalEquivProd ⟨m, x⟩) =
      if (m : ℕ) = 1 then φ 1 else 0 := by
    intro m
    rw [tsum_fintype]
    have hx : ∀ x : Nat.divisorsAntidiagonal (m : ℕ), F (sigmaAntidiagonalEquivProd ⟨m, x⟩) =
        (μ x.1.1 : ℂ) * (φ (m : ℕ) * ((((m : ℕ) : ℂ)) ^ 2)⁻¹) := by
      intro x
      have e1 : ((sigmaAntidiagonalEquivProd ⟨m, x⟩).1 : ℕ) = x.1.1 := rfl
      have e2 : ((sigmaAntidiagonalEquivProd ⟨m, x⟩).2 : ℕ) = x.1.2 := rfl
      have hm : x.1.1 * x.1.2 = (m : ℕ) := (Nat.mem_divisorsAntidiagonal.mp x.2).1
      simp only [hF]
      rw [e1, e2, hm]
    rw [Finset.sum_congr rfl fun x _ => hx x, ← Finset.sum_mul,
      Finset.sum_coe_sort (Nat.divisorsAntidiagonal (m : ℕ)) (fun x => (μ x.1 : ℂ)),
      sum_moebius_divisorsAntidiagonal]
    split_ifs with h1
    · rw [h1]; simp
    · simp
  rw [tsum_congr hfib]
  rw [tsum_eq_single 1 (fun m hm => by
    have : (m : ℕ) ≠ 1 := fun h => hm (PNat.coe_eq_one_iff.mp h)
    simp [this])]
  simp

variable {N : ℕ} [NeZero N]

/-- $a_r = \sum_{g \ge 1,\ g \equiv r \bmod N}\mu(g)g^{-2}$. -/
noncomputable def moebCoeff (N : ℕ) (r : ZMod N) : ℂ :=
  ∑' g : ℕ+, if (((g : ℕ) : ℤ) : ZMod N) = r then (μ (g : ℕ) : ℂ) * ((((g : ℕ) : ℂ)) ^ 2)⁻¹ else 0

lemma summable_moebTerm : Summable fun g : ℕ+ => (μ (g : ℕ) : ℂ) * ((((g : ℕ) : ℂ)) ^ 2)⁻¹ :=
  summable_bdd_mul_inv_sq (B := 1) fun g => by
    rw [Complex.norm_intCast]; exact_mod_cast abs_moebius_le_one

lemma summable_moebCoeff_term (r : ZMod N) :
    Summable fun g : ℕ+ =>
      if (((g : ℕ) : ℤ) : ZMod N) = r then (μ (g : ℕ) : ℂ) * ((((g : ℕ) : ℂ)) ^ 2)⁻¹ else 0 :=
  Summable.of_norm_bounded summable_pnat_inv_sq fun g => by
    split_ifs
    · rw [norm_mul, norm_inv_sq_pnat, Complex.norm_intCast]
      have : |((μ (g : ℕ) : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
      nlinarith [inv_nonneg.mpr (sq_nonneg (((g : ℕ) : ℝ)))]
    · simp

/-- For $\varphi$ bounded on $\mathbb{Z}/N$: $\sum_r a_r\,X(r) = \sum_{g \ge 1}\mu(g)g^{-2}X(g \bmod N)$. -/
lemma sum_moebCoeff_mul (X : ZMod N → ℂ) :
    ∑ r : ZMod N, moebCoeff N r * X r =
      ∑' g : ℕ+, (μ (g : ℕ) : ℂ) * ((((g : ℕ) : ℂ)) ^ 2)⁻¹ * X (((g : ℕ) : ℤ) : ZMod N) := by
  simp only [moebCoeff]
  rw [Finset.sum_congr rfl fun r _ => (tsum_mul_right (f := fun g : ℕ+ =>
    if (((g : ℕ) : ℤ) : ZMod N) = r then (μ (g : ℕ) : ℂ) * ((((g : ℕ) : ℂ)) ^ 2)⁻¹ else 0)).symm]
  rw [← Summable.tsum_finsetSum (fun r _ => (summable_moebCoeff_term r).mul_right _)]
  refine tsum_congr fun g => ?_
  rw [Finset.sum_eq_single (((g : ℕ) : ℤ) : ZMod N)]
  · simp
  · intro r _ hr; rw [ite_eq_right_iff.mpr (fun h => absurd h.symm hr), zero_mul]
  · simp

/-- **The constant-term identity:** for $\varphi : \mathbb{Z}/N \to \mathbb{C}$ with $\varphi(-u) = \varphi(u)$,
$\sum_r a_r\sum_{n \in \mathbb{Z}}\varphi(rn)n^{-2} = 2\varphi(1)$. -/
theorem moebius_const (φ : ZMod N → ℂ) (hφ : ∀ u, φ (-u) = φ u) :
    ∑ r : ZMod N, moebCoeff N r * ∑' n : ℤ, φ (r * (n : ZMod N)) * (((n : ℂ)) ^ 2)⁻¹ = 2 * φ 1 := by
  classical
  set B : ℝ := ∑ u, ‖φ u‖ with hBdef
  have hB : ∀ u, ‖φ u‖ ≤ B := fun u =>
    Finset.single_le_sum (f := fun u => ‖φ u‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ u)
  -- the integer sum is twice the sum over `n ≥ 1`
  have hint : ∀ r : ZMod N, ∑' n : ℤ, φ (r * (n : ZMod N)) * (((n : ℂ)) ^ 2)⁻¹ =
      2 * ∑' n : ℕ+, φ (r * (((n : ℕ) : ℤ) : ZMod N)) * ((((n : ℕ) : ℂ)) ^ 2)⁻¹ := by
    intro r
    have hev : Function.Even fun n : ℤ => φ (r * (n : ZMod N)) * (((n : ℂ)) ^ 2)⁻¹ := by
      intro n; simp only [Int.cast_neg, mul_neg, hφ, neg_sq]
    have hs : Summable fun n : ℤ => φ (r * (n : ZMod N)) * (((n : ℂ)) ^ 2)⁻¹ := by
      refine Summable.of_norm_bounded ((Real.summable_one_div_int_pow.mpr (by norm_num : 1 < 2)).mul_left B)
        fun n => ?_
      rw [norm_mul, norm_inv, norm_pow, Complex.norm_intCast, sq_abs, ← one_div]
      exact mul_le_mul_of_nonneg_right (hB _) (by positivity)
    rw [tsum_int_eq_zero_add_two_mul_tsum_pnat hev hs]
    simp
  simp_rw [hint]
  simp_rw [mul_left_comm _ (2 : ℂ)]
  rw [← Finset.mul_sum, sum_moebCoeff_mul]
  congr 1
  have := tsum_moebius_mul (fun m : ℕ => φ ((m : ℤ) : ZMod N)) (B := B) (fun m => hB _)
  convert this using 3 with g n
  · push_cast
    ring_nf
  · simp

end QuadFormsKB.Siegel.GenusEis
