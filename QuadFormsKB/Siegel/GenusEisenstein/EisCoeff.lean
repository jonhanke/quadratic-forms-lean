/-
# The $q$-coefficients of the Eisenstein part $E_f$

For $f \in M_2(\Gamma_1(N))$ and $m \ge 1$ (`hasSum_eisQCoeff`):
$$e_f(m) = -8\pi^2 m\sum_{X \ge 1}\frac{1}{X^2}\sum_{\substack{0 \le Y < X\\ \gcd(Y, X) = 1}}W(X, Y)\,e\Big(\frac{mY}{X}\Big),$$
an absolutely convergent series, where $W$ = `eisW f` (so $W(X, Y) = c_f(\gamma)/2$ for $v(\gamma) = (X, Y)$, by
`kappa_eq_zero`). This is the $q$-expansion of the "primitive" Eisenstein series $\sum_{(c,d)=1}W(c,d)(cz+d)^{-2}$.

*Proof.* $E_f = \sum_r a_rE_{W_r}$ and `hasSum_eis2` give $e_f(m) = 2\sum_{g \ge 1}\mu(g)g^{-2}\sum_{c \ge 1}a_{W_g}(c, m)$. The
double series over $(g, c)$ is absolutely convergent ($a_{W_g}(c, m) = 0$ unless $c \mid mN$); grouping it by $X = gc$ and
using $\sum_{g \mid \gcd(X, Y)}\mu(g) = [\gcd(X, Y) = 1]$ (`sum_antidiag_moebius`) gives the formula.
-/
import QuadFormsKB.Siegel.GenusEisenstein.QExpansion
import QuadFormsKB.Siegel.Thm63Inputs

open Complex Filter Topology ModularForm ArithmeticFunction
open UpperHalfPlane hiding I
open scoped MatrixGroups Real Manifold ArithmeticFunction.Moebius ArithmeticFunction.zeta

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Siegel.GenusEis

open EisensteinWt2

/-! ### A Möbius identity over the divisor antidiagonal -/

lemma sum_divisors_moebius (n : ℕ) : ∑ g ∈ n.divisors, (μ g : ℂ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun F : ArithmeticFunction ℂ => F n) (coe_moebius_mul_coe_zeta (R := ℂ))
  simp only [coe_mul_zeta_apply, intCoe_apply] at h
  rw [h, one_apply]

/-- $\sum_{gc = X}\mu(g)\sum_{d < c}F(gd) = \sum_{Y < X,\ \gcd(Y, X) = 1}F(Y)$. -/
theorem sum_antidiag_moebius {X : ℕ} (hX : X ≠ 0) (F : ℕ → ℂ) :
    ∑ x ∈ Nat.divisorsAntidiagonal X, (μ x.1 : ℂ) * ∑ d ∈ Finset.range x.2, F (x.1 * d) =
      ∑ Y ∈ (Finset.range X).filter (fun Y => Nat.Coprime Y X), F Y := by
  classical
  rw [Nat.sum_divisorsAntidiagonal (fun g c => (μ g : ℂ) * ∑ d ∈ Finset.range c, F (g * d))]
  -- the inner sum is over the multiples of `g` below `X`
  have hin : ∀ g ∈ X.divisors, ∑ d ∈ Finset.range (X / g), F (g * d) =
      ∑ Y ∈ (Finset.range X).filter (fun Y => g ∣ Y), F Y := by
    intro g hg
    have hgX : g ∣ X := Nat.dvd_of_mem_divisors hg
    have hg0 : 0 < g := Nat.pos_of_mem_divisors hg
    refine Finset.sum_nbij' (fun d => g * d) (fun Y => Y / g) ?_ ?_ ?_ ?_ ?_
    · intro d hd
      simp only [Finset.mem_range, Finset.mem_filter] at hd ⊢
      refine ⟨?_, dvd_mul_right g d⟩
      have : d < X / g := hd
      calc g * d < g * (X / g) := Nat.mul_lt_mul_of_pos_left this hg0
        _ = X := Nat.mul_div_cancel' hgX
    · intro Y hY
      simp only [Finset.mem_range, Finset.mem_filter] at hY ⊢
      exact Nat.div_lt_div_of_lt_of_dvd hgX hY.1
    · intro d _; simp [Nat.mul_div_cancel_left d hg0]
    · intro Y hY
      simp only [Finset.mem_range, Finset.mem_filter] at hY
      exact Nat.mul_div_cancel' hY.2
    · intro d _; rfl
  rw [Finset.sum_congr rfl fun g hg => by rw [hin g hg]]
  simp_rw [Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Y _ => ?_
  have e : ∑ g ∈ X.divisors, (if g ∣ Y then (μ g : ℂ) * F Y else 0) =
      (∑ g ∈ (Nat.gcd X Y).divisors, (μ g : ℂ)) * F Y := by
    rw [Finset.sum_mul, ← Finset.sum_filter]
    congr 1
    ext g
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨Nat.dvd_gcd h1 h2, Nat.gcd_ne_zero_left hX⟩
    · rintro ⟨h, _⟩; exact ⟨⟨h.trans (Nat.gcd_dvd_left X Y), hX⟩, h.trans (Nat.gcd_dvd_right X Y)⟩
  rw [e, sum_divisors_moebius]
  simp only [Nat.Coprime, Nat.gcd_comm Y X]
  split_ifs <;> simp

/-! ### The coefficients -/

variable {N : ℕ} [NeZero N]

local notation "Γ₁" => CongruenceSubgroup.Gamma1

variable (f : ModularForm (Γ₁ N) 2)

lemma isTInv_eisWr (r : ZMod N) : IsTInv (eisWr f r) := fun x y => by
  have := eisW_shift f (r * x) (r * y) 1
  simp only [eisWr]
  rwa [one_mul, ← mul_add] at this

lemma isEvenW_eisWr (r : ZMod N) : IsEvenW (eisWr f r) := fun x y => by
  simp only [eisWr, mul_neg]; exact eisW_neg f _ _

/-- The $q$-coefficients of $E_f$. -/
noncomputable def eisQCoeff (n : ℕ) : ℂ := ∑ r : ZMod N, moebCoeff N r * eisCoeff (eisWr f r) n

theorem hasSum_eisQ (τ : ℍ) :
    HasSum (fun n : ℕ => eisQCoeff f n * cexp (2 * π * I * τ) ^ n) (eisQ f τ) := by
  rw [eisQ_apply]
  have h := hasSum_sum fun r (_ : r ∈ (Finset.univ : Finset (ZMod N))) =>
    (hasSum_eis2 (isTInv_eisWr f r) (isEvenW_eisWr f r) τ).mul_left (moebCoeff N r)
  refine h.congr_fun fun n => ?_
  simp only [eisQCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

/-- **The $q$-expansion coefficients of $E_f$** (period $1$). -/
theorem qExpansion_eisQ_coeff (n : ℕ) : (UpperHalfPlane.qExpansion 1 (eisQ f)).coeff n = eisQCoeff f n := by
  refine (ModularFormClass.qExpansion_coeff_unique (k := 2) (c := eisQCoeff f) one_pos
    (one_mem_strictPeriods_Gamma1 N) (f := eisQ f) (fun τ => ?_) n).symm
  have h := hasSum_eisQ f τ
  refine h.congr_fun fun m => ?_
  simp [Function.Periodic.qParam, smul_eq_mul]

lemma norm_eisWr_le (r x y : ZMod N) : ‖eisWr f r x y‖ ≤ ∑ a, ∑ b, ‖eisW f a b‖ := by
  simp only [eisWr]
  exact (Finset.single_le_sum (f := fun b => ‖eisW f (r * x) b‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ (r * y))).trans (Finset.single_le_sum (f := fun a => ∑ b, ‖eisW f a b‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ (r * x)))

lemma wtBound_eisWr_le (r : ZMod N) : wtBound (eisWr f r) ≤ (N : ℝ) ^ 2 * ∑ a, ∑ b, ‖eisW f a b‖ := by
  rw [wtBound]
  calc ∑ a, ∑ b, ‖eisWr f r a b‖ ≤ ∑ _a : ZMod N, ∑ _b : ZMod N, ∑ a, ∑ b, ‖eisW f a b‖ :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => norm_eisWr_le f r a b
    _ = _ := by simp [ZMod.card]; ring

/-- The summand $T(g, c) = \mu(g)g^{-2}a_{W_g}(c, m)$. -/
noncomputable def termGC (m : ℕ) (p : ℕ+ × ℕ+) : ℂ :=
  (μ (p.1 : ℕ) : ℂ) * ((((p.1 : ℕ) : ℂ)) ^ 2)⁻¹ *
    rowCoeff (eisWr f (((p.1 : ℕ) : ℤ) : ZMod N)) p.2 m

lemma summable_termGC (m : ℕ) : Summable (termGC f m) := by
  set B₀ := ∑ a, ∑ b, ‖eisW f a b‖
  have hB₀ : 0 ≤ B₀ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hs1 : Summable fun c : ℕ+ => (((c : ℕ) : ℝ) ^ 2)⁻¹ := summable_pnat_inv_sq
  refine Summable.of_norm_bounded ((hs1.mul_of_nonneg hs1 (fun _ => by positivity)
    (fun _ => by positivity)).mul_left (4 * π ^ 2 * ((N : ℝ) ^ 2 * B₀) * N * (m : ℝ) ^ 2)) fun p => ?_
  have h := norm_rowCoeff_le (isTInv_eisWr f (((p.1 : ℕ) : ℤ) : ZMod N)) p.2 m p.2.pos
  have hw := wtBound_eisWr_le f (((p.1 : ℕ) : ℤ) : ZMod N)
  have hμ : ‖(μ (p.1 : ℕ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]; exact_mod_cast abs_moebius_le_one
  simp only [termGC, norm_mul, norm_inv_sq_pnat]
  have hc : 0 ≤ (((p.2 : ℕ) : ℝ) ^ 2)⁻¹ := by positivity
  have hg : 0 ≤ (((p.1 : ℕ) : ℝ) ^ 2)⁻¹ := by positivity
  calc ‖(μ (p.1 : ℕ) : ℂ)‖ * (((p.1 : ℕ) : ℝ) ^ 2)⁻¹ * ‖rowCoeff (eisWr f (((p.1 : ℕ) : ℤ) : ZMod N)) p.2 m‖
      ≤ 1 * (((p.1 : ℕ) : ℝ) ^ 2)⁻¹ * (4 * π ^ 2 * ((N : ℝ) ^ 2 * B₀) * N * (m : ℝ) ^ 2 *
          (((p.2 : ℕ) : ℝ) ^ 2)⁻¹) := by
        gcongr
        refine h.trans ?_
        gcongr
    _ = _ := by ring

/-- $e_f(m) = 2\sum_{(g, c)}T(g, c)$ for $m \ge 1$. -/
lemma eisQCoeff_eq_tsum {m : ℕ} (hm : 1 ≤ m) : eisQCoeff f m = 2 * ∑' p : ℕ+ × ℕ+, termGC f m p := by
  rw [eisQCoeff, sum_moebCoeff_mul (fun r => eisCoeff (eisWr f r) m)]
  have hs := summable_termGC f m
  rw [hs.tsum_prod' (fun g => hs.prod_factor g), ← tsum_mul_left]
  refine tsum_congr fun g => ?_
  rw [eisCoeff, if_neg (by omega), zero_add]
  simp only [termGC]
  rw [tsum_mul_left]
  ring

/-- The fibre of $T$ over $X = gc$. -/
lemma sum_fiber_termGC (m : ℕ) (X : ℕ+) :
    ∑ x ∈ Nat.divisorsAntidiagonal (X : ℕ), (μ x.1 : ℂ) * ((x.1 : ℂ) ^ 2)⁻¹ *
        rowCoeff (eisWr f ((x.1 : ℤ) : ZMod N)) x.2 m =
      (-4 * (π : ℂ) ^ 2) * m * (((X : ℕ) : ℂ) ^ 2)⁻¹ *
        ∑ Y ∈ (Finset.range X).filter (fun Y => Nat.Coprime Y X),
          eisW f (((X : ℕ) : ℤ) : ZMod N) ((Y : ℤ) : ZMod N) * cexp (2 * π * I * ((m : ℂ) * Y / X)) := by
  rw [← sum_antidiag_moebius X.ne_zero (fun Y => eisW f (((X : ℕ) : ℤ) : ZMod N) ((Y : ℤ) : ZMod N) *
    cexp (2 * π * I * ((m : ℂ) * Y / X))), Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hX := (Nat.mem_divisorsAntidiagonal.mp hx).1
  have hg0 : (x.1 : ℂ) ≠ 0 := by
    have : x.1 ≠ 0 := fun h => by rw [h, zero_mul] at hX; exact X.ne_zero hX.symm
    exact_mod_cast this
  have hc0 : (x.2 : ℂ) ≠ 0 := by
    have : x.2 ≠ 0 := fun h => by rw [h, mul_zero] at hX; exact X.ne_zero hX.symm
    exact_mod_cast this
  have hXc : ((X : ℕ) : ℂ) = (x.1 : ℂ) * x.2 := by rw [← hX]; push_cast; ring
  simp only [rowCoeff, rowFC, eisWr, wt]
  rw [Fin.sum_univ_eq_sum_range (fun d => eisW f (((x.1 : ℤ) : ZMod N) * ((x.2 : ℤ) : ZMod N))
      (((x.1 : ℤ) : ZMod N) * ((d : ℤ) : ZMod N)) * cexp (2 * π * I * ((m : ℂ) * d / x.2)))]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have e1 : ((x.1 : ℤ) : ZMod N) * ((x.2 : ℤ) : ZMod N) = (((X : ℕ) : ℤ) : ZMod N) := by
    rw [← hX]; push_cast; ring
  have e2 : ((x.1 : ℤ) : ZMod N) * ((d : ℤ) : ZMod N) = (((x.1 * d : ℕ) : ℤ) : ZMod N) := by push_cast; ring
  have e3 : (m : ℂ) * d / x.2 = (m : ℂ) * ((x.1 * d : ℕ) : ℂ) / X := by
    rw [hXc]; push_cast; field_simp
  rw [e1, e2, e3, hXc]
  field_simp

/-- **The $q$-coefficients of $E_f$ as a primitive Eisenstein series**, $m \ge 1$. -/
theorem hasSum_eisQCoeff {m : ℕ} (hm : 1 ≤ m) :
    HasSum (fun X : ℕ+ => (-8 * (π : ℂ) ^ 2) * m * (((X : ℕ) : ℂ) ^ 2)⁻¹ *
        ∑ Y ∈ (Finset.range X).filter (fun Y => Nat.Coprime Y X),
          eisW f (((X : ℕ) : ℤ) : ZMod N) ((Y : ℤ) : ZMod N) * cexp (2 * π * I * ((m : ℂ) * Y / X)))
      (eisQCoeff f m) := by
  rw [eisQCoeff_eq_tsum f hm]
  have hs := summable_termGC f m
  have hsig : Summable (termGC f m ∘ sigmaAntidiagonalEquivProd) :=
    (sigmaAntidiagonalEquivProd.summable_iff).mpr hs
  have hfib : ∀ X : ℕ+, HasSum (fun x : Nat.divisorsAntidiagonal (X : ℕ) =>
      termGC f m (sigmaAntidiagonalEquivProd ⟨X, x⟩))
      ((-4 * (π : ℂ) ^ 2) * m * (((X : ℕ) : ℂ) ^ 2)⁻¹ *
        ∑ Y ∈ (Finset.range X).filter (fun Y => Nat.Coprime Y X),
          eisW f (((X : ℕ) : ℤ) : ZMod N) ((Y : ℤ) : ZMod N) * cexp (2 * π * I * ((m : ℂ) * Y / X))) := by
    intro X
    rw [← sum_fiber_termGC f m X]
    convert hasSum_fintype _ using 1
    rw [← Finset.sum_coe_sort (Nat.divisorsAntidiagonal (X : ℕ))]
    rfl
  have h := (hsig.hasSum.sigma hfib)
  rw [show (∑' b, (termGC f m ∘ sigmaAntidiagonalEquivProd) b) = ∑' p, termGC f m p from
    sigmaAntidiagonalEquivProd.tsum_eq (termGC f m)] at h
  refine (h.mul_left 2).congr_fun fun X => ?_
  ring

end QuadFormsKB.Siegel.GenusEis
