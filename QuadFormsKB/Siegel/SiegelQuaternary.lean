/-
# Siegel's formula for positive definite quaternary forms over $\mathbb{Q}$

**Theorem** (`siegelFormula_quaternary`). For every positive definite integral quadratic form $Q$ in $4$ variables,
$$r_{\mathrm{Gen}(Q)}(m) = \beta_\infty(m)\prod_p\beta_p(m) \qquad (m \ge 1),$$
i.e. `SiegelFormula Q` (Siegel 1935, Hauptsatz, for $n = 4$). Consequently Hanke's Thm 6.3 holds with the single cited
input (4.7) + Deligne (`thm_6_3_quaternary''`).

**Proof (the Hecke/Kneser route).** Let $N = |\det H|$ and $\Theta_{\mathrm{Gen}} \in M_2(\Gamma_1(N))$ (`thetaGenMF`).
1. *(S1)* $E_Q := E_{\Theta_{\mathrm{Gen}}}$ (`eisQ`, built in `GenusEisenstein/Construction.lean` from the constant terms of
   $\Theta_{\mathrm{Gen}}$ at all cusps) makes $\Theta_{\mathrm{Gen}} - E_Q$ a cusp form (`cuspPart`).
2. *(S4)* The $q$-coefficients of $E_Q$ are $a_E(m) = \beta_\infty(m)\prod_p\beta_p(m)$ (`eisQCoeff_thetaGen`): by
   `hasSum_eisQCoeff` they are the primitive Eisenstein series of the cusp constants, which are the theta multipliers
   $M_A(a, c) = -\frac{1}{4c^2\sqrt{\det A}}G_A(a, c)$ (`eisW_thetaGen`); this is $\beta_\infty(m)\sum_c A_c(m)$ with $A_c$ the
   singular-series terms (`ssTerm`), and $\sum_cA_c(m) = \prod_p\beta_p(m)$ (`hasSum_ssTerm`).
3. *(S2)* At good $p \nmid m$, both $r_{\mathrm{Gen}}$ (Kneser neighbours, `genusRepAvg_neighbor_four`) and $a_E$
   (`aE_prime_sq_mul`) satisfy $x(p^2m) = (p^2 + 1 + \varepsilon p)\,x(m)$, $\varepsilon = (\det H/p)$.
4. *(S3)* A weight-2 cusp form with this growth vanishes (`HeckeVanishing.coeff_eq_zero_of_sq_growth`, Hecke's
   mean-square bound against Chebyshev's count of primes; an elementary substitute for Deligne).
-/
import QuadFormsKB.Siegel.GenusEisenstein.EisCoeff
import QuadFormsKB.Siegel.GenusEisenstein.ThetaGen
import QuadFormsKB.Siegel.SingularSeries
import QuadFormsKB.Siegel.GoodPrimeShift
import QuadFormsKB.Siegel.HeckeVanishing
import QuadFormsKB.Siegel.EichlerGenus

open Complex Filter Topology ModularForm
open UpperHalfPlane hiding I
open scoped MatrixGroups Real Manifold

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Siegel.GenusEis

open EisensteinWt2 SingularSeries

variable {Q : IntQF 4}

lemma neZeroN (hQ : Q.PosDef) : NeZero Q.hessian.det.natAbs := ⟨(natAbs_det_pos hQ).ne'⟩

/-- **The cusp constants of $\Theta_{\mathrm{Gen}}$ as the Eisenstein weight:** for $X \ge 1$ and $\gcd(Y, X) = 1$,
$W(X, Y) = \tfrac12 M_A(-Y, X) = -\frac{G_A(-Y, X)}{8X^2\sqrt{\det A}}$. -/
theorem eisW_thetaGen (hQ : Q.PosDef) {X Y : ℕ} [NeZero X] (hcop : Nat.Coprime Y X) :
    haveI := neZeroN hQ
    eisW (thetaGenMF hQ) (((X : ℕ) : ℤ) : ZMod Q.hessian.det.natAbs) ((Y : ℤ) : ZMod Q.hessian.det.natAbs) =
      -(1 / (8 * (X : ℂ) ^ 2 * Real.sqrt (gramMatrix Q).det)) * gaussSum (gramMatrix Q) (-(Y : ℤ)) X 0 := by
  haveI := neZeroN hQ
  have hco : IsCoprime (X : ℤ) (Y : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  obtain ⟨γ, h10, h00⟩ := exists_SL_of_isCoprime hco
  have hv : cuspVec Q.hessian.det.natAbs γ =
      ((((X : ℕ) : ℤ) : ZMod Q.hessian.det.natAbs), ((Y : ℤ) : ZMod Q.hessian.det.natAbs)) := by
    simp [cuspVec, h10, h00]
  have h1 := eisW_cuspVec (thetaGenMF hQ) γ
  rw [hv] at h1
  simp only at h1
  rw [h1, kappa_eq_zero, sub_zero, ← cuspVal_neg]
  have hc : (-γ) 1 0 = ((X : ℕ) : ℤ) := by
    simp [Matrix.SpecialLinearGroup.coe_neg, h10]
  have h0 : (-γ) 0 0 = -(Y : ℤ) := by
    simp [Matrix.SpecialLinearGroup.coe_neg, h00]
  have := cuspVal_thetaGenMF hQ (γ := -γ) (c := X) hc
  rw [this, h0, thetaMult_two_eq]
  ring

/-- Reindexing the Ramanujan-type sum by $Y \mapsto a \equiv -Y$. -/
lemma sum_coprime_neg (X : ℕ) [NeZero X] (m : ℕ) :
    ∑ Y ∈ (Finset.range X).filter (fun Y => Nat.Coprime Y X),
        gaussSum (gramMatrix Q) (-(Y : ℤ)) X 0 * cexp (2 * π * I * ((m : ℂ) * Y / X)) =
      ∑ a ∈ (Finset.range X).filter (fun a => Nat.Coprime a X),
        gaussSum (gramMatrix Q) (a : ℤ) X 0 * cexp (-(2 * π * I * (a : ℂ) * (m : ℂ) / X)) := by
  have hX0 : X ≠ 0 := NeZero.ne X
  have hXc : (X : ℂ) ≠ 0 := by exact_mod_cast hX0
  refine Finset.sum_nbij' (fun Y => (X - Y) % X) (fun a => (X - a) % X) ?_ ?_ ?_ ?_ ?_
  · intro Y hY
    simp only [Finset.mem_filter, Finset.mem_range] at hY ⊢
    refine ⟨Nat.mod_lt _ (Nat.pos_of_ne_zero hX0), ?_⟩
    rw [Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_comm, ← Nat.Coprime, Nat.coprime_self_sub_left hY.1.le]
    exact hY.2
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    refine ⟨Nat.mod_lt _ (Nat.pos_of_ne_zero hX0), ?_⟩
    rw [Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_comm, ← Nat.Coprime, Nat.coprime_self_sub_left ha.1.le]
    exact ha.2
  · intro Y hY
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hY
    rcases Nat.eq_zero_or_pos Y with rfl | hY0
    · show (X - (X - 0) % X) % X = 0
      simp only [Nat.sub_zero, Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (by omega : X - Y < X), Nat.mod_eq_of_lt (by omega : X - (X - Y) < X)]
      omega
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha
    rcases Nat.eq_zero_or_pos a with rfl | ha0
    · show (X - (X - 0) % X) % X = 0
      simp only [Nat.sub_zero, Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (by omega : X - a < X), Nat.mod_eq_of_lt (by omega : X - (X - a) < X)]
      omega
  · intro Y hY
    simp only [Finset.mem_filter, Finset.mem_range] at hY
    -- `a = (X - Y) % X ≡ -Y`
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (X - Y) % X + Y = X * k := by
      have : X ∣ (X - Y) % X + Y := by
        rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_add_mod, Nat.sub_add_cancel hY.1.le, Nat.mod_self]
      exact this
    have ha : (((X - Y) % X : ℕ) : ℤ) = -(Y : ℤ) + X * k := by
      have := congrArg (Nat.cast (R := ℤ)) hk
      simp only [Nat.cast_add, Nat.cast_mul] at this; linarith
    rw [gaussSum_eq_gz, gaussSum_eq_gz]
    congr 1
    · congr 1; rw [ha]; push_cast; simp
    · have hak : (((X - Y) % X : ℕ) : ℂ) = -(Y : ℂ) + X * k := by
        have := congrArg (Nat.cast (R := ℂ)) hk
        simp only [Nat.cast_add, Nat.cast_mul] at this; linear_combination this
      rw [hak]
      have : -(2 * π * I * (-(Y : ℂ) + X * k) * (m : ℂ) / X) =
          2 * π * I * ((m : ℂ) * Y / X) + 2 * π * I * (-((k : ℂ) * m)) := by
        field_simp; ring
      have h1 : cexp (2 * π * I * (-((k : ℂ) * m))) = 1 := by
        have := cexp_two_pi_I_int (-(k * m : ℤ)); push_cast at this; exact this
      rw [this, Complex.exp_add, h1, mul_one]

lemma gramDet_eq_det (Q : QuadForm ℤ 4) : gramDet Q = (gramMatrix Q).det := by
  rw [det_gramMatrix, gramDet]; ring

lemma gramDet_pos (hQ : Q.PosDef) : 0 < gramDet Q := by
  rw [gramDet]; have := det_hessian_pos hQ; positivity

/-- **The $q$-coefficients of $E_Q$ are $a_E(m) = \beta_\infty(m)\prod_p\beta_p(m)$**. -/
@[kb "siegel1935" "Eisenstein coefficients = β_∞ · singular series, n = 4 [unverified]"]
theorem eisQCoeff_thetaGen (hQ : Q.PosDef) {m : ℕ} (hm : 1 ≤ m) :
    haveI := neZeroN hQ
    eisQCoeff (thetaGenMF hQ) m = ((aE Q m : ℝ) : ℂ) := by
  haveI := neZeroN hQ
  set d : ℝ := Real.sqrt (gramMatrix Q).det with hd
  have hd0 : 0 < d := Real.sqrt_pos.mpr (by rw [← gramDet_eq_det]; exact gramDet_pos hQ)
  set K : ℂ := (π : ℂ) ^ 2 * m / d with hK
  have hK0 : K ≠ 0 := by
    have h1 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    have h2 : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    have h3 : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [hK]; exact div_ne_zero (mul_ne_zero (pow_ne_zero _ h3) h1) h2
  have hH := hasSum_eisQCoeff (thetaGenMF hQ) hm
  have hterm : ∀ X : ℕ+, (-8 * (π : ℂ) ^ 2) * m * (((X : ℕ) : ℂ) ^ 2)⁻¹ *
      ∑ Y ∈ (Finset.range X).filter (fun Y => Nat.Coprime Y X),
        eisW (thetaGenMF hQ) ((((X : ℕ) : ℤ)) : ZMod Q.hessian.det.natAbs) ((Y : ℤ) : ZMod _) *
          cexp (2 * π * I * ((m : ℂ) * Y / X)) = K * ssTerm Q m X := by
    intro X
    haveI : NeZero (X : ℕ) := ⟨X.ne_zero⟩
    have hX0 : ((X : ℕ) : ℂ) ≠ 0 := by exact_mod_cast X.ne_zero
    rw [Finset.sum_congr rfl fun Y hY => by
      rw [eisW_thetaGen hQ (Finset.mem_filter.mp hY).2, mul_assoc]]
    rw [← Finset.mul_sum, sum_coprime_neg X m, ssTerm, dif_neg X.ne_zero]
    simp only [← hd]
    rw [hK]
    have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    push_cast
    field_simp
  have hH' : HasSum (fun X : ℕ+ => K * ssTerm Q m X) (eisQCoeff (thetaGenMF hQ) m) :=
    hH.congr_fun fun X => (hterm X).symm
  have hss : HasSum (fun X : ℕ+ => ssTerm Q m X) (eisQCoeff (thetaGenMF hQ) m / K) := by
    have := hH'.mul_left K⁻¹
    rw [show K⁻¹ * eisQCoeff (thetaGenMF hQ) m = eisQCoeff (thetaGenMF hQ) m / K by
      rw [div_eq_inv_mul]] at this
    refine this.congr_fun fun X => ?_
    rw [← mul_assoc, inv_mul_cancel₀ hK0, one_mul]
  have hss' : HasSum (ssTerm Q m) (eisQCoeff (thetaGenMF hQ) m / K) := by
    rw [← (PNat.coe_injective).hasSum_iff (f := ssTerm Q m) (fun x hx => by
      have : x = 0 := by
        by_contra h; exact hx ⟨⟨x, Nat.pos_of_ne_zero h⟩, rfl⟩
      rw [this]; exact ssTerm_zero Q m)]
    exact hss
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have heul := hasSum_ssTerm (IntQF.PosDef.nondegenerate hQ) (le_refl 4) hm0 hss'.summable
  have hval := hss'.unique heul
  rw [div_eq_iff hK0] at hval
  rw [hval, aE, aEWith, betaInf_four, gramDet_eq_det, hK]
  have hdet0 : 0 ≤ (gramMatrix Q).det := by rw [← gramDet_eq_det]; exact (gramDet_pos hQ).le
  rw [Real.rpow_neg hdet0, ← Real.sqrt_eq_rpow, ← hd]
  push_cast
  field_simp

/-- The $q$-coefficients of the cusp form $\Theta_{\mathrm{Gen}} - E_Q$: $c(m) = r_{\mathrm{Gen}}(m) - a_E(m)$, $m \ge 1$. -/
theorem qExpansion_cuspPart_thetaGen (hQ : Q.PosDef) {m : ℕ} (hm : 1 ≤ m) :
    haveI := neZeroN hQ
    (UpperHalfPlane.qExpansion 1 (cuspPart (thetaGenMF hQ))).coeff m =
      ((genusRepAvg Q m : ℝ) : ℂ) - ((aE Q m : ℝ) : ℂ) := by
  haveI := neZeroN hQ
  set f := thetaGenMF hQ
  have h1 := one_mem_strictPeriods_Gamma1 Q.hessian.det.natAbs
  have hu := ModularFormClass.qExpansion_coeff_unique (k := 2)
    (c := fun n => (UpperHalfPlane.qExpansion 1 f).coeff n - eisQCoeff f n) one_pos h1
    (f := cuspPart f) (fun τ => by
      have ha := ModularForm.hasSum_qExpansion (f := f) one_pos h1 τ
      have hb := hasSum_eisQ f τ
      rw [cuspPart_apply]
      refine (ha.sub hb).congr_fun fun n => ?_
      simp [Function.Periodic.qParam, smul_eq_mul, sub_mul]) m
  rw [← hu, qExpansion_thetaGenMF_coeff, eisQCoeff_thetaGen hQ hm]

/-- **Siegel's formula for positive definite quaternary forms**, coefficientwise: $r_{\mathrm{Gen}(Q)}(m) = a_E(m)$. -/
theorem genusRepAvg_eq_aE_nat (hQ : Q.PosDef) {m : ℕ} (hm : 1 ≤ m) : genusRepAvg Q m = aE Q m := by
  haveI := neZeroN hQ
  set N := Q.hessian.det.natAbs
  have hN0 : 0 < N := natAbs_det_pos hQ
  have h1 := one_mem_strictPeriods_Gamma1 N
  have hrel : ∀ p m' : ℕ, p.Prime → ¬ p ∣ 2 * N → 1 ≤ m' → ¬ p ∣ m' →
      (p : ℝ) ^ 2 / 2 * ‖(UpperHalfPlane.qExpansion 1 (cuspPart (thetaGenMF hQ))).coeff m'‖ ≤
        ‖(UpperHalfPlane.qExpansion 1 (cuspPart (thetaGenMF hQ))).coeff (p ^ 2 * m')‖ := by
    intro p m' hp hpM hm' hpm'
    haveI := Fact.mk hp
    have hp2 : p ≠ 2 := fun h => hpM (h ▸ dvd_mul_right 2 N)
    have hdet : ¬ (p : ℤ) ∣ Q.hessian.det := fun h =>
      hpM (dvd_mul_of_dvd_right (Int.natCast_dvd.mp h) 2)
    have hpm'' : ¬ (p : ℤ) ∣ (m' : ℤ) := fun h => hpm' (Int.natCast_dvd_natCast.mp h)
    have hpm2 : ¬ (p : ℤ) ^ 2 ∣ (m' : ℤ) := fun h => hpm'' ((dvd_pow_self _ two_ne_zero).trans h)
    set ε : ℝ := (legendreSym p Q.hessian.det : ℝ)
    -- the neighbour relation for `r_Gen` at `p ∤ m'`
    have hr := Kneser.genusRepAvg_neighbor_four hQ hp2 hdet (m' : ℤ)
    rw [if_neg hpm'', if_neg hpm2] at hr
    have hr' : genusRepAvg Q ((p : ℤ) ^ 2 * m') = ((p : ℝ) ^ 2 + 1 + ε * p) * genusRepAvg Q m' := by
      linarith
    have ha := aE_prime_sq_mul hQ hp2 hdet (m := (m' : ℤ)) (by exact_mod_cast hm') hpm''
    have hpm1 : 1 ≤ p ^ 2 * m' := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hp.ne_zero)
      (by omega))
    rw [qExpansion_cuspPart_thetaGen hQ hpm1, qExpansion_cuspPart_thetaGen hQ hm']
    have hcast : ((p ^ 2 * m' : ℕ) : ℤ) = (p : ℤ) ^ 2 * m' := by push_cast; ring
    rw [hcast, hr', ha]
    have hε : ‖(ε : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have := legendreSym.eq_one_or_neg_one p (a := Q.hessian.det) (by
        intro h0; exact hdet ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0))
      rcases this with h | h <;> simp [ε, h]
    have hb := HeckeVanishing.norm_sq_add_one_add_mul_ge (p := (p : ℝ))
      (by exact_mod_cast hp.one_lt.le) hε
    have e : (((((p : ℝ) ^ 2 + 1 + ε * p) * genusRepAvg Q m' : ℝ)) : ℂ) -
        (((((p : ℝ) ^ 2 + 1 + ε * p) * aE Q m' : ℝ)) : ℂ) =
        (((p : ℝ) : ℂ) ^ 2 + 1 + (ε : ℂ) * ((p : ℝ) : ℂ)) *
          (((genusRepAvg Q m' : ℝ) : ℂ) - ((aE Q m' : ℝ) : ℂ)) := by
      push_cast; ring
    rw [e, norm_mul]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  have h0 := HeckeVanishing.coeff_eq_zero_of_sq_growth (cuspPart (thetaGenMF hQ)) h1
    (by omega : 0 < 2 * N) hrel hm
  rw [qExpansion_cuspPart_thetaGen hQ hm, sub_eq_zero] at h0
  exact_mod_cast h0

/-- **Siegel's formula for positive definite quaternary forms** (Siegel 1935, Hauptsatz, $n = 4$; Hanke 2004, (5.3)):
`SiegelFormula Q` holds for every positive definite integral quadratic form $Q$ in $4$ variables. -/
@[kb "siegel1935" "Hauptsatz, n = 4 (proved via the Hecke/Kneser route)"]
theorem siegelFormula_quaternary (hQ : Q.PosDef) : SiegelFormula Q :=
  ⟨fun m hm => by
    lift m to ℕ using (by omega)
    exact genusRepAvg_eq_aE_nat hQ (by exact_mod_cast hm)⟩

end QuadFormsKB.Siegel.GenusEis

namespace QuadFormsKB.Siegel

open LocalDensity

open Classical in
/-- **Theorem 6.3 for quaternary forms, with (4.7) + Deligne as the only cited input** (Hanke 2004, Thm 6.3, p. 381):
`thm_6_3_quaternary'` with `SiegelFormula Q` discharged by `GenusEis.siegelFormula_quaternary`. The remaining input is
`hED : EigenformDecompDeligne |det H| χ_Q`. -/
@[kb "hanke2004" "Thm 6.3, p. 381 (modulo (4.7) + Deligne only)"]
theorem thm_6_3_quaternary'' (Q : IntQF 4) (hQ : IntQF.PosDef Q)
    (hED : EigenformDecompDeligne Q.hessian.det.natAbs (chiQuat hQ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {S : Finset ℕ}, (∀ p ∈ S, p.Prime) → ∀ (S₀ : Finset (Fin 4)) {T : ℕ}, 0 < T →
        (∀ p ∈ S, IsPStable Q S₀ p T) → (∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T) →
        (∀ p ∈ badPrimes Q, IsLocallyRepresentedAt Q p T) →
        ∀ (ν : ℕ → ℕ), (∀ p ∈ S, 1 ≤ ν p) → ∀ {m : ℕ}, m = T * (∏ p ∈ S, p ^ ν p) ^ 2 →
        C / lambdaHat4 Q S T * divCount (anisoPart Q m) * √(anisoPart Q m : ℝ) <
          √(isoPart Q m : ℝ) / divCount (isoPart Q m) *
            ∏ p ∈ m.primeFactors.filter (fun p => IsGoodPrime Q p ∧ jacobiSym Q.hessian.det p = -1),
              ((p : ℝ) - 1) / ((p : ℝ) + 1) →
        IntQF.Represents Q m :=
  thm_6_3_quaternary' Q hQ (GenusEis.siegelFormula_quaternary hQ) hED

end QuadFormsKB.Siegel
