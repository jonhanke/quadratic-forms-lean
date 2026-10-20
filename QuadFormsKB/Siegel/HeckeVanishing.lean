/-
# A weight-2 cusp form with $T(p^2)$-type growth vanishes

**Theorem** (`coeff_eq_zero_of_sq_growth`). Let $f$ be a weight-2 cusp form for an arithmetic group $\Gamma$ with
$1$ a strict period, $f = \sum_n a(n)q^n$. If there is $M \ge 1$ such that
$$\|a(p^2m)\| \ge \tfrac{p^2}{2}\,\|a(m)\| \qquad (p \text{ prime},\ p \nmid M,\ m \ge 1,\ p \nmid m),$$
then $a(m) = 0$ for every $m \ge 1$ (and $f = 0$, `eq_zero_of_sq_growth`).

This is the vanishing step of the Hecke/Kneser route to Siegel's formula: if $c(p^2m) = (p^2 + 1 + \varepsilon p)c(m)$
with $|\varepsilon| \le 1$, then $|p^2 + 1 + \varepsilon p| \ge p^2 - p + 1 \ge p^2/2$ (`norm_sq_add_one_add_mul_ge`).

*Proof.* If $a(m_0) \ne 0$, the primes $p \in (Y/4, Y]$ (for $Y$ large they are prime to $Mm_0$) give distinct
$n = p^2m_0 \le Y^2m_0$ with $\|a(n)\|^2 \ge \tfrac14 (Y/4)^4\|a(m_0)\|^2$. Their number is unbounded as $Y \to \infty$
(Chebyshev: $\theta(Y) - \theta(Y/4) \ge \tfrac{\log 2}{2}Y - O(\sqrt Y\log Y)$, Mathlib's `Chebyshev.theta_ge`,
`Chebyshev.theta_le_log4_mul_x`), so $\sum_{n \le Y^2m_0}\|a(n)\|^2/Y^4$ is unbounded, against Hecke's mean-square bound
$\sum_{n < X}\|a(n)\|^2 \le CX^2$ for weight-2 cusp forms (Mathlib's
`CuspFormClass.exists_sum_range_norm_sq_qExpansion_coeff_le_of_mem_strictPeriods`, from Parseval and
$|f(\tau)| \le C/\operatorname{Im}\tau$).

This is an elementary substitute for Deligne's bound in the vanishing argument (only Hecke's mean-square bound is
used; cf. Rankin 1939). No published antecedent of exactly this argument was found (see `docs/siegel.md`).
-/
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.Chebyshev
import QuadFormsKB.Citation

open Filter Topology Finset ModularForm
open UpperHalfPlane hiding I
open scoped UpperHalfPlane

namespace QuadFormsKB.Siegel.HeckeVanishing

/-- The primes $p$ with $\lfloor Y/4\rfloor < p \le Y$. -/
def primesQuarter (Y : ℕ) : Finset ℕ := (Finset.Ioc (Y / 4) Y).filter Nat.Prime

lemma mem_primesQuarter {Y p : ℕ} : p ∈ primesQuarter Y ↔ Y / 4 < p ∧ p ≤ Y ∧ p.Prime := by
  simp [primesQuarter, and_assoc]

/-- $\sum_{Y/4 < p \le Y}\log p = \theta(Y) - \theta(\lfloor Y/4 \rfloor)$. -/
lemma sum_log_primesQuarter (Y : ℕ) :
    ∑ p ∈ primesQuarter Y, Real.log p = Chebyshev.theta Y - Chebyshev.theta ((Y / 4 : ℕ) : ℝ) := by
  unfold Chebyshev.theta
  simp only [Nat.floor_natCast]
  rw [eq_sub_iff_add_eq, ← Finset.sum_union]
  · congr 1
    ext p
    simp only [primesQuarter, Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨⟨by omega, h2⟩, h3⟩
      · exact ⟨⟨h1, by omega⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_cases h : Y / 4 < p
      · exact Or.inl ⟨⟨h, h2⟩, h3⟩
      · exact Or.inr ⟨⟨h1, by omega⟩, h3⟩
  · rw [Finset.disjoint_left]
    intro p hp hq
    simp only [primesQuarter, Finset.mem_filter, Finset.mem_Ioc] at hp hq
    omega

/-- $\#\{Y/4 < p \le Y\}\cdot\log Y \ge \tfrac{\log 2}{2}Y - \log(Y+1) - 2\sqrt Y\log Y$. -/
lemma card_primesQuarter_mul_log_ge (Y : ℕ) :
    (Y : ℝ) * Real.log 2 / 2 - Real.log (Y + 1) - 2 * Real.sqrt Y * Real.log Y ≤
      (primesQuarter Y).card * Real.log Y := by
  have h1 : ∑ p ∈ primesQuarter Y, Real.log p ≤ (primesQuarter Y).card * Real.log Y := by
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun p hp => ?_
    have hp' := mem_primesQuarter.mp hp
    exact Real.log_le_log (by exact_mod_cast hp'.2.2.pos) (by exact_mod_cast hp'.2.1)
  have h2 := Chebyshev.theta_ge Y
  have h3 := Chebyshev.theta_le_log4_mul_x (x := ((Y / 4 : ℕ) : ℝ)) (by positivity)
  have h4 : (((Y / 4 : ℕ) : ℕ) : ℝ) ≤ (Y : ℝ) / 4 := by
    rw [le_div_iff₀ (by norm_num)]
    exact_mod_cast (by omega : Y / 4 * 4 ≤ Y)
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h5 : Real.log 4 * (((Y / 4 : ℕ) : ℕ) : ℝ) ≤ Real.log 4 * ((Y : ℝ) / 4) :=
    mul_le_mul_of_nonneg_left h4 (by rw [hl4]; positivity)
  rw [sum_log_primesQuarter] at h1
  rw [hl4] at h5
  nlinarith

/-- $(2\sqrt x + c)\log x = o(x)$: eventually $(2\sqrt x + c)\log x \le \kappa x$. -/
lemma eventually_sqrt_log_le {c κ : ℝ} (hc : 0 ≤ c) (hκ : 0 < κ) :
    ∀ᶠ x : ℝ in atTop, (2 * Real.sqrt x + c) * Real.log x ≤ κ * x := by
  have hlo := isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)
  have hε : 0 < κ / (2 + c) := div_pos hκ (by linarith)
  filter_upwards [hlo.bound hε, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg (by positivity), ← Real.sqrt_eq_rpow] at hx
  have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have hsx : Real.sqrt x ≤ x := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  calc (2 * Real.sqrt x + c) * Real.log x ≤ (2 * Real.sqrt x + c) * (κ / (2 + c) * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left hx (by positivity)
    _ = κ / (2 + c) * (2 * (Real.sqrt x * Real.sqrt x) + c * Real.sqrt x) := by ring
    _ ≤ κ / (2 + c) * (2 * x + c * x) := by
        rw [hs]; gcongr
    _ = κ * x := by field_simp

/-- **There are arbitrarily many primes in $(Y/4, Y]$:** for every $B$, eventually $\#\{Y/4 < p \le Y\} \ge B$. -/
lemma eventually_card_primesQuarter_ge (B : ℝ) :
    ∀ᶠ Y : ℕ in atTop, B ≤ (primesQuarter Y).card := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hev := eventually_sqrt_log_le (c := 2 + |B| + 1) (κ := Real.log 2 / 2) (by positivity) (by positivity)
  have hev' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hev
  filter_upwards [hev', eventually_ge_atTop 2] with Y hY hY2
  have hY2' : (2 : ℝ) ≤ Y := by exact_mod_cast hY2
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hlog1 : Real.log ((Y : ℝ) + 1) ≤ 2 * Real.log Y := by
    rw [← Real.log_rpow (by linarith)]
    refine Real.log_le_log (by linarith) ?_
    rw [show ((Y : ℝ) ^ (2 : ℝ)) = (Y : ℝ) * Y by rw [Real.rpow_two]; ring]
    nlinarith
  have hc := card_primesQuarter_mul_log_ge Y
  have hB : B ≤ |B| := le_abs_self B
  have key : (B + 1) * Real.log Y ≤ (primesQuarter Y).card * Real.log Y := by
    nlinarith [Real.sqrt_nonneg (Y : ℝ)]
  have := le_of_mul_le_mul_right key hlogY
  linarith

/-- $|p^2 + 1 + \varepsilon p| \ge p^2/2$ for $|\varepsilon| \le 1$, $p \ge 1$. -/
lemma norm_sq_add_one_add_mul_ge {p : ℝ} (hp : 1 ≤ p) {ε : ℂ} (hε : ‖ε‖ ≤ 1) :
    p ^ 2 / 2 ≤ ‖((p : ℂ) ^ 2 + 1 + ε * p)‖ := by
  have h1 : ‖((p : ℂ) ^ 2 + 1)‖ = p ^ 2 + 1 := by
    rw [show ((p : ℂ) ^ 2 + 1) = ((p ^ 2 + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  have h2 : ‖ε * p‖ ≤ p := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    nlinarith [norm_nonneg ε]
  have h3 := norm_sub_norm_le ((p : ℂ) ^ 2 + 1) (-(ε * p))
  rw [norm_neg, sub_neg_eq_add, h1] at h3
  nlinarith

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]

/-- **A weight-2 cusp form with $T(p^2)$-type growth has vanishing coefficients.** Let $f \in S_2(\Gamma)$ ($\Gamma$
arithmetic, $1$ a strict period), $a(n)$ its $q$-expansion coefficients (`qExpansion 1 f`). If for some $M \ge 1$,
$\|a(p^2m)\| \ge \frac{p^2}{2}\|a(m)\|$ for all primes $p \nmid M$ and $m \ge 1$ with $p \nmid m$, then $a(m) = 0$ for all
$m \ge 1$. -/
@[kb "iwaniec1997" "Hecke's mean-square bound, §5 [unverified]; vanishing argument new"]
theorem coeff_eq_zero_of_sq_growth (f : CuspForm Γ 2) (h1 : (1 : ℝ) ∈ Γ.strictPeriods) {M : ℕ} (hM : 0 < M)
    (hrel : ∀ p m : ℕ, p.Prime → ¬ p ∣ M → 1 ≤ m → ¬ p ∣ m →
      (p : ℝ) ^ 2 / 2 * ‖(qExpansion 1 f).coeff m‖ ≤ ‖(qExpansion 1 f).coeff (p ^ 2 * m)‖)
    {m : ℕ} (hm : 1 ≤ m) : (qExpansion 1 f).coeff m = 0 := by
  by_contra ha
  set a : ℕ → ℂ := fun n => (qExpansion 1 f).coeff n with hadef
  obtain ⟨C, hC⟩ := CuspFormClass.exists_sum_range_norm_sq_qExpansion_coeff_le_of_mem_strictPeriods
    (k := 2) f one_pos h1
  have hδ : 0 < ‖a m‖ ^ 2 := by
    have : 0 < ‖a m‖ := norm_pos_iff.mpr ha
    positivity
  set δ := ‖a m‖ ^ 2 with hδdef
  set B : ℝ := 1024 * |C| * ((m : ℝ) + 1) ^ 2 / δ + 1 with hBdef
  obtain ⟨Y, hYB, hYge⟩ := ((eventually_card_primesQuarter_ge B).and
    (eventually_ge_atTop (4 * (M + m + 1)))).exists
  set S := primesQuarter Y with hSdef
  have hY1 : (1 : ℝ) ≤ Y := by exact_mod_cast (by omega : 1 ≤ Y)
  -- each prime of `S` exceeds `M + m`
  have hbig : ∀ p ∈ S, M + m < p := by
    intro p hp
    have := (mem_primesQuarter.mp hp).1
    omega
  -- the lower bound for a single prime
  have hlow : ∀ p ∈ S, ((Y : ℝ) / 4) ^ 4 / 4 * δ ≤ ‖a (p ^ 2 * m)‖ ^ 2 := by
    intro p hp
    have hp' := mem_primesQuarter.mp hp
    have hpM : ¬ p ∣ M := fun h => by
      have := Nat.le_of_dvd hM h; have := hbig p hp; omega
    have hpm : ¬ p ∣ m := fun h => by
      have := Nat.le_of_dvd hm h; have := hbig p hp; omega
    have hr := hrel p m hp'.2.2 hpM hm hpm
    have hpY : (Y : ℝ) / 4 ≤ p := by
      rw [div_le_iff₀ (by norm_num)]
      exact_mod_cast (by omega : Y ≤ p * 4)
    have hY0 : (0 : ℝ) ≤ Y / 4 := by positivity
    have h4 : ((Y : ℝ) / 4) ^ 4 ≤ (p : ℝ) ^ 4 := pow_le_pow_left₀ hY0 hpY 4
    have hsq : ((p : ℝ) ^ 2 / 2 * ‖a m‖) ^ 2 ≤ ‖a (p ^ 2 * m)‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hr 2
    calc ((Y : ℝ) / 4) ^ 4 / 4 * δ ≤ (p : ℝ) ^ 4 / 4 * δ := by gcongr
      _ = ((p : ℝ) ^ 2 / 2 * ‖a m‖) ^ 2 := by rw [hδdef]; ring
      _ ≤ _ := hsq
  -- the sum over `S` embeds in the mean square up to `Y² m`
  have hinj : Set.InjOn (fun p : ℕ => p ^ 2 * m) S := by
    intro p _ q _ h
    simp only at h
    have hm0 : 0 < m := hm
    have := Nat.eq_of_mul_eq_mul_right hm0 h
    exact Nat.pow_left_injective (by norm_num) this
  have hsub : S.image (fun p : ℕ => p ^ 2 * m) ⊆ Finset.range (Y ^ 2 * m + 1) := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    have hpY := (mem_primesQuarter.mp hp).2.1
    simp only [Finset.mem_range]
    have : p ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left hpY 2
    nlinarith
  have hsum : ∑ p ∈ S, ‖a (p ^ 2 * m)‖ ^ 2 ≤ C * ((Y ^ 2 * m + 1 : ℕ) : ℝ) ^ 2 := by
    calc ∑ p ∈ S, ‖a (p ^ 2 * m)‖ ^ 2 = ∑ n ∈ S.image (fun p : ℕ => p ^ 2 * m), ‖a n‖ ^ 2 :=
          (Finset.sum_image (f := fun n => ‖a n‖ ^ 2) hinj).symm
      _ ≤ ∑ n ∈ Finset.range (Y ^ 2 * m + 1), ‖a n‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ ≤ _ := hC (Y ^ 2 * m + 1)
  have hlowsum : (S.card : ℝ) * (((Y : ℝ) / 4) ^ 4 / 4 * δ) ≤ ∑ p ∈ S, ‖a (p ^ 2 * m)‖ ^ 2 := by
    rw [← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ hlow
  have hcast : ((Y ^ 2 * m + 1 : ℕ) : ℝ) ≤ (Y : ℝ) ^ 2 * ((m : ℝ) + 1) := by
    push_cast; nlinarith
  have hupper : C * ((Y ^ 2 * m + 1 : ℕ) : ℝ) ^ 2 ≤ |C| * ((Y : ℝ) ^ 2 * ((m : ℝ) + 1)) ^ 2 := by
    calc C * ((Y ^ 2 * m + 1 : ℕ) : ℝ) ^ 2 ≤ |C| * ((Y ^ 2 * m + 1 : ℕ) : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ _ := by gcongr
  have hY4 : (0 : ℝ) < (Y : ℝ) ^ 4 := by positivity
  have hfin : (S.card : ℝ) * δ ≤ 1024 * |C| * ((m : ℝ) + 1) ^ 2 := by
    have := hlowsum.trans (hsum.trans hupper)
    have e : (S.card : ℝ) * (((Y : ℝ) / 4) ^ 4 / 4 * δ) = (S.card * δ) * (Y : ℝ) ^ 4 / 1024 := by ring
    have e2 : |C| * ((Y : ℝ) ^ 2 * ((m : ℝ) + 1)) ^ 2 = (|C| * ((m : ℝ) + 1) ^ 2) * (Y : ℝ) ^ 4 := by ring
    rw [e, e2] at this
    have := (div_le_iff₀ (by norm_num : (0 : ℝ) < 1024)).mp this
    nlinarith
  have hcard : (S.card : ℝ) ≤ 1024 * |C| * ((m : ℝ) + 1) ^ 2 / δ := by
    rw [le_div_iff₀ hδ]; exact hfin
  linarith

/-- **A weight-2 cusp form with $T(p^2)$-type growth is zero** (`coeff_eq_zero_of_sq_growth` plus $a(0) = 0$). -/
theorem eq_zero_of_sq_growth (f : CuspForm Γ 2) (h1 : (1 : ℝ) ∈ Γ.strictPeriods) {M : ℕ} (hM : 0 < M)
    (hrel : ∀ p m : ℕ, p.Prime → ¬ p ∣ M → 1 ≤ m → ¬ p ∣ m →
      (p : ℝ) ^ 2 / 2 * ‖(qExpansion 1 f).coeff m‖ ≤ ‖(qExpansion 1 f).coeff (p ^ 2 * m)‖) :
    f = 0 := by
  have hq : qExpansion 1 f = 0 := by
    ext m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simpa using CuspFormClass.qExpansion_coeff_zero f one_pos h1
    · simpa using coeff_eq_zero_of_sq_growth f h1 hM hrel hm
  have hf := (UpperHalfPlane.qExpansion_eq_zero_iff one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f h1) (ModularFormClass.holo f)
    (ModularFormClass.bdd_at_infty f)).mp hq
  ext τ
  simpa using congrFun hf τ

end QuadFormsKB.Siegel.HeckeVanishing
