/-
# The unit volumes of $x_0^2+x_1^2$ and $x_0^2-2x_1^2$ via $L(1,\chi_D)$

**Layer:** $\mathbb Q$.

The binary headline `siegelIndefinite_binary_uncond` at $m = 1$ ($\sum_in(M_i,1) = 1$, `tsum_repCount_one_sumTwoSq`)
reads
$c^{(1)}_\infty = \frac12B(1)\sum_iv(M_i)$ with $c^{(1)}_\infty = |\det H|^{-1}$ and
$B(1) = L(1,\chi_E)^{-1}\prod_p\beta_p(1)\,(1-\chi_E(p)/p)^{-1}$ (`binDensityProduct`). The character $\chi_E$ of the
discriminant field is the Kronecker character $\chi_D$ outside a finite set (`chiP_eq_chiE`, and `chiP` is the
Legendre symbol $(D/p)$ at odd $p$), and changing $\chi_E$ on a finite set moves $L(1,\chi_E)$ and the local factors by the
same finite product (`binDensityProduct_unary_eq`). With $\beta_p(1) = 1-\chi_D(p)/p$ at odd $p$, $\beta_2(1) = 2$ and
$\chi_D(2) = 0$: $B(1) = 2/L(1,\chi_D)$, hence
$$\sum_iv(M_i) = \frac{L(1,\chi_D)}{|\det H|}:\qquad \frac{L(1,\chi_{-4})}4\ \ (x_0^2+x_1^2),\qquad \frac{L(1,\chi_8)}8\ \ (x_0^2-2x_1^2)$$
(**`unitVolume_sum_sumTwoSq`**, **`unitVolume_sum_pell2`**), and with Dirichlet's class number formula
$\pi h(-4)/(4w(-4))$ and $h(8)R(8)/(8\sqrt2)$ (`unitVolume_sum_sumTwoSq_classNumber`, `unitVolume_sum_pell2_classNumber`;
$R(8) = \log\varepsilon_8$ the regulator of the units of $\mathbb Z[\sqrt2]$). Unconditional.
-/
import QuadFormsKB.Tamagawa.Classical.Binary
import QuadFormsKB.Tamagawa.Classical.TernaryReg
import QuadFormsKB.Binary.ClassNumberFormula

open NumberField NumberField.Units IsDedekindDomain
open scoped ENNReal Real

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Classical

open QuadFormsKB.Binary QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.Tamagawa.BinaryTauRat RatBridge LocalDensity QuadFormsKB.RegProd QuadFormsKB.NFEuler

local notation "natGen" => Rat.HeightOneSpectrum.natGenerator

/-! ### Changing the character on a finite set -/

section General

variable {F : Type} [Field F] [NumberField F]

/-- **The regularized binary product with another character.** If $\chi = \chi_E$ outside a finite set $S$,
$L(1,\chi) = c$, and $\beta_v(m) = (1-\chi(v)/Nv)\,r_v$ with $(r_v)$ of finite support, then
$B(m) = |d_F|^{-1/2}c^{-1}\prod_vr_v$. -/
theorem binDensityProduct_unary_eq (Q₀ : QuadForm (𝓞 F) 2) (E : Type) [Field E] [NumberField E] [Algebra F E]
    (hdeg : Module.finrank F E = 2) {χ : HeightOneSpectrum (𝓞 F) → ℝ} (hχ : ∀ v, |χ v| ≤ 1) {c : ℝ}
    (hc : HasLOne χ c) (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, chiE F E v = χ v)
    {m : 𝓞 F} (r : HeightOneSpectrum (𝓞 F) → ℝ) (hr : (Function.mulSupport r).Finite)
    (hβ : ∀ v, NF.localDensity v Q₀ m = lamL χ v * r v) :
    binDensityProduct Q₀ (DVR.unary m) E = |(discr F : ℝ)| ^ (-(1 / 2 : ℝ)) * c⁻¹ * ∏' v, r v := by
  have hE : ∀ v, |chiE F E v| ≤ 1 := abs_chiE_le hdeg
  have hL := hc.congr_finite (χ := chiE F E) hE hχ S hS
  set g : HeightOneSpectrum (𝓞 F) → ℝ := fun v => lamL χ v / lamL (chiE F E) v with hg
  have hg1 : ∀ v ∉ S, g v = 1 := fun v hv => by
    simp only [hg, lamL, hS v hv]
    exact div_self (lamL_pos hχ v).ne'
  have hgS : (Function.mulSupport g).Finite :=
    S.finite_toSet.subset fun v hv => by
      by_contra h; exact hv (hg1 v h)
  have hP : ∏ v ∈ S, lFactor (chiE F E) 1 v / lFactor χ 1 v = ∏ v ∈ S, g v := by
    refine Finset.prod_congr rfl fun v _ => ?_
    simp only [hg, lamL_eq_inv_lFactor]
    rw [inv_div_inv]
  have hPpos : 0 < ∏ v ∈ S, g v := Finset.prod_pos fun v _ => div_pos (lamL_pos hχ v) (lamL_pos hE v)
  have htg : ∏' v, g v = ∏ v ∈ S, g v := tprod_eq_prod fun v hv => hg1 v hv
  have hprod : ∏' v, NF.localDensity v Q₀ m / lamL (chiE F E) v = (∏ v ∈ S, g v) * ∏' v, r v := by
    rw [← htg, ← (multipliable_of_hasFiniteMulSupport hgS).tprod_mul (multipliable_of_hasFiniteMulSupport hr)]
    refine tprod_congr fun v => ?_
    rw [hβ v]
    simp only [hg]
    ring
  unfold binDensityProduct
  simp only [NF.localDensityForm_unary]
  rw [hprod, hL.lOne_eq, hP, mul_inv]
  field_simp

end General

/-! ### Over $\mathbb Q$ -/

/-- A prime of $\mathcal O_\mathbb Q$ other than the one above $2$ lies over an odd prime. -/
theorem natGen_ne_two_of_not_mem {v v₂ : HeightOneSpectrum (𝓞 ℚ)} (hv₂ : natGen v₂ = 2)
    (hv : v ∉ ({v₂} : Finset _)) : natGen v ≠ 2 := by
  intro h
  apply hv
  rw [Finset.mem_singleton]
  exact (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective (Subtype.ext (show natGen v = natGen v₂ by rw [h, hv₂]))

theorem two_not_mem_of_natGen_ne_two {v : HeightOneSpectrum (𝓞 ℚ)} (hp2 : natGen v ≠ 2) :
    (2 : 𝓞 ℚ) ∉ v.asIdeal := by
  intro h
  have h' := (RatHeadline3.intCast_mem_iff v 2).mp (by exact_mod_cast h)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) Nat.prime_two).mp
    (by exact_mod_cast h'))

/-- **The character `chiP` of $a x_0^2 + b x_1^2$ is $\chi_D$ at the odd primes not dividing $D = -4ab$.** -/
theorem chiP_up_diag_odd (a b : ℤ) {D : ℤ} [IsQuadDisc D] (hD : -(4 * a * b) = D) (v : HeightOneSpectrum (𝓞 ℚ))
    (hp2 : natGen v ≠ 2) (hpD : ¬ (natGen v : ℤ) ∣ D) :
    chiP v (up (QuadForm.diag ![a, b])) = kronChi D v := by
  have : Fact (natGen v).Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have hd : (up (QuadForm.diag ![a, b])).hessian.det ∉ v.asIdeal := by
    rw [hessian_det_up_diag]
    intro h
    exact hpD (by rw [← hD, Int.dvd_neg]; exact (RatHeadline3.intCast_mem_iff v _).mp h)
  rw [chiP_binary_eq_charNF v _ (two_not_mem_of_natGen_ne_two hp2) hd, hessian_det_up_diag,
    show -(((4 * a * b : ℤ)) : 𝓞 ℚ) = ((D : ℤ) : 𝓞 ℚ) by rw [← hD]; push_cast; ring,
    charNF_intCast_eq_legendreSym', kronChi, kronR, kronZ_odd_prime _ hp2]

/-- **$\chi_E = \chi_D$ outside a finite set** for $a x_0^2 + b x_1^2$, $D = -4ab$ a power of $2$ up to sign. -/
theorem exists_chiE_eq_kronChi (a b : ℤ) {D : ℤ} [IsQuadDisc D] (hD : -(4 * a * b) = D)
    (hDodd : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ (p : ℤ) ∣ D) (E : Type) [Field E] [NumberField E] [Algebra ℚ E]
    (hE : IsDiscField (up (QuadForm.diag ![a, b])) E) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 ℚ)), ∀ v ∉ S, chiE ℚ E v = kronChi D v := by
  classical
  obtain ⟨S₀, hS₀⟩ := chiP_eq_chiE _ hE
  obtain ⟨v₂, hv₂⟩ := exists_natGen_eq_two
  refine ⟨S₀ ∪ {v₂}, fun v hv => ?_⟩
  rw [Finset.mem_union, not_or] at hv
  have hp2 := natGen_ne_two_of_not_mem hv₂ hv.2
  rw [← hS₀ v hv.1, chiP_up_diag_odd a b hD v hp2 (hDodd _ (Rat.HeightOneSpectrum.prime_natGenerator v) hp2)]

/-- $c_\infty^{(1)} = |k|^{-1}$ over $\mathbb Q$ when $\det H = k$. -/
theorem cInfCorankOne_rat (Q₀ : QuadForm (𝓞 ℚ) 2) {k : ℤ} (hk : Q₀.hessian.det = (k : 𝓞 ℚ)) :
    cInfCorankOne Q₀ = ENNReal.ofReal (|(k : ℝ)|⁻¹) := by
  have hR : ∀ w : {w : NumberField.InfinitePlace ℚ // w.IsReal},
      |σR w (algebraMap (𝓞 ℚ) ℚ Q₀.hessian.det)|⁻¹ = |(k : ℝ)|⁻¹ := fun w => by
    rw [hk, map_intCast, map_intCast]
  have hcard : Fintype.card {w : NumberField.InfinitePlace ℚ // w.IsReal} = 1 :=
    Fintype.card_eq_one_iff.2 ⟨⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩,
      fun w => Subtype.ext (Subsingleton.elim _ _)⟩
  have hC : ∀ w : {w : NumberField.InfinitePlace ℚ // w.IsComplex}, False := fun w =>
    NumberField.InfinitePlace.not_isComplex_iff_isReal.2
      (Subsingleton.elim Rat.infinitePlace w.1 ▸ Rat.isReal_infinitePlace) w.2
  have kR : ∀ [Fintype {w : NumberField.InfinitePlace ℚ // w.IsReal}],
      ∏ w : {w : NumberField.InfinitePlace ℚ // w.IsReal}, |σR w (algebraMap (𝓞 ℚ) ℚ Q₀.hessian.det)|⁻¹ =
        |(k : ℝ)|⁻¹ := by
    intro _
    rw [Finset.prod_eq_single (⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩ :
      {w : NumberField.InfinitePlace ℚ // w.IsReal})
      (fun b _ hb => (hb (Subtype.ext (Subsingleton.elim _ _))).elim) (fun h => (h (Finset.mem_univ _)).elim), hR]
  have kC : ∀ [Fintype {w : NumberField.InfinitePlace ℚ // w.IsComplex}],
      ∏ w : {w : NumberField.InfinitePlace ℚ // w.IsComplex},
        (‖σC w (algebraMap (𝓞 ℚ) ℚ Q₀.hessian.det)‖ ^ 2)⁻¹ = 1 := by
    intro _
    exact Finset.prod_eq_one (fun w _ => (hC w).elim)
  rw [cInfCorankOne_eq, cF_two, NumberField.discr_rat, @kR (_), @kC (_)]
  norm_num

/-- **$B(1) = 2/L(1,\chi_D)$** for $a x_0^2 + b x_1^2$ with $D = -4ab$ when $\beta_p(1) = 1-\chi_D(p)/p$ at odd $p$,
$\beta_2(1) = 2$, $\chi_D(2) = 0$. -/
theorem binDensityProduct_one_diag (a b : ℤ) {D : ℤ} [IsQuadDisc D] (hD : -(4 * a * b) = D)
    (hDodd : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ (p : ℤ) ∣ D) (E : Type) [Field E] [NumberField E] [Algebra ℚ E]
    (hE : IsDiscField (up (QuadForm.diag ![a, b])) E)
    (hodd : ∀ p : ℕ, p.Prime → p ≠ 2 → localDensity (QuadForm.diag ![a, b]) p 1 = 1 - kronR D p / p)
    (h2 : localDensity (QuadForm.diag ![a, b]) 2 1 = 2) (hD2 : kronR D 2 = 0) :
    binDensityProduct (up (QuadForm.diag ![a, b])) (DVR.unary 1) E = 2 / Binary.LOne D := by
  classical
  obtain ⟨S, hS⟩ := exists_chiE_eq_kronChi a b hD hDodd E hE
  obtain ⟨v₂, hv₂⟩ := exists_natGen_eq_two
  set r : HeightOneSpectrum (𝓞 ℚ) → ℝ := fun v => if natGen v = 2 then 2 else 1 with hrdef
  have hr1 : ∀ v ∉ ({v₂} : Finset _), r v = 1 := fun v hv => by
    simp only [hrdef, natGen_ne_two_of_not_mem hv₂ hv, ite_false]
  have hr : (Function.mulSupport r).Finite :=
    (({v₂} : Finset _) : Set _).toFinite.subset fun v hv => by
      by_contra h; exact hv (hr1 v h)
  have hβ : ∀ v, NF.localDensity v (up (QuadForm.diag ![a, b])) 1 = lamL (kronChi D) v * r v := by
    intro v
    have e1 : ((1 : ℤ) : 𝓞 ℚ) = 1 := Int.cast_one
    have hloc := nfLocalDensity_up v (QuadForm.diag ![a, b]) 1
    rw [e1] at hloc
    rw [hloc, lamL, kronChi, normP_rat]
    by_cases hp2 : natGen v = 2
    · simp only [hrdef, hp2, ite_true, hD2, h2]
      norm_num
    · simp only [hrdef, hp2, ite_false, mul_one]
      exact hodd _ (Rat.HeightOneSpectrum.prime_natGenerator v) hp2
  rw [binDensityProduct_unary_eq _ E (IsDiscField.finrank_eq_two hE) (fun v => abs_kronChi_le v)
      hasLOne_kronChi S hS r hr hβ, NumberField.discr_rat,
    tprod_eq_prod (s := {v₂}) fun v hv => hr1 v hv, Finset.prod_singleton]
  simp only [hrdef, hv₂, ite_true]
  norm_num
  ring

theorem kronR_neg_four_two : kronR (-4) 2 = 0 := by rw [kronR_neg_four]; simp

theorem kronR_eight_two : kronR 8 2 = 0 := by rw [kronR_eight]; simp

theorem odd_not_dvd_neg_four (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : ¬ (p : ℤ) ∣ -4 := not_dvd_neg_four hp hp2

/-- **$B(1) = 2/L(1,\chi_{-4})$ for $x_0^2+x_1^2$.** -/
theorem binDensityProduct_one_sumTwoSq :
    binDensityProduct (up sumTwoSqZ) (DVR.unary 1) (QField (-4)) = 2 / Binary.LOne (-4) := by
  refine binDensityProduct_one_diag 1 1 (by norm_num) (fun p hp hp2 => not_dvd_neg_four hp hp2) _
    isDiscField_sumTwoSq (fun p hp hp2 => ?_) localDensity_sumTwoSq_one_two kronR_neg_four_two
  have : Fact p.Prime := ⟨hp⟩
  rw [show QuadForm.diag ![(1 : ℤ), 1] = sumTwoSqZ from rfl, localDensity_sumTwoSq_one_odd hp2, goodFactor_zero,
    kronR_neg_four]

/-- **$B(1) = 2/L(1,\chi_8)$ for $x_0^2-2x_1^2$.** -/
theorem binDensityProduct_one_pell2 :
    binDensityProduct (up pell2Z) (DVR.unary 1) (QField 8) = 2 / Binary.LOne 8 := by
  refine binDensityProduct_one_diag 1 (-2) (by norm_num) (fun p hp hp2 => not_dvd_eight hp hp2) _
    isDiscField_pell2 (fun p hp hp2 => ?_) localDensity_pell2_one_two kronR_eight_two
  have : Fact p.Prime := ⟨hp⟩
  rw [show QuadForm.diag ![(1 : ℤ), -2] = pell2Z from rfl, localDensity_pell2_one_odd hp2, goodFactor_zero,
    kronR_eight]

/-- **The unit volume from the headline at $m = 1$**: $c^{(1)}_\infty = \frac12B(1)\sum_iv(M_i)$ when
$\sum_in(M_i,1) = 1$. -/
theorem tsum_unitVolume_of_one (Q₀ : QuadForm (𝓞 ℚ) 2) (hQ : Q₀.Nondegenerate) (hA : AnisotropicF Q₀)
    (E : Type) [Field E] [NumberField E] [Algebra ℚ E] (hE : IsDiscField Q₀ E)
    (Ξ₁ : RatFrame Q₀ (DVR.unary 1)) (h1 : ∑' i, Indefinite.repCount Q₀ (DVR.unary (1 : 𝓞 ℚ)) i = 1)
    {k : ℤ} (hk : Q₀.hessian.det = (k : 𝓞 ℚ)) {B : ℝ} (hB : binDensityProduct Q₀ (DVR.unary 1) E = B)
    (hB0 : 0 < B) :
    ∑' i, unitVolume Q₀ hQ i = ENNReal.ofReal (2 * |(k : ℝ)|⁻¹ / B) := by
  have hT1 : (DVR.unary (1 : 𝓞 ℚ)).Nondegenerate := unary_nondegenerate (by simp)
  have e1 := siegelIndefinite_binary_uncond Q₀ hQ hA E hE (DVR.unary 1) hT1 Ξ₁
  rw [h1, mul_one, cInfCorankOne_rat Q₀ hk, hB] at e1
  set V := ∑' i, unitVolume Q₀ hQ i
  have hB' : ENNReal.ofReal B ≠ 0 := (ENNReal.ofReal_pos.2 hB0).ne'
  have h2B : (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal B ≠ 0 := mul_ne_zero (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top) hB'
  have h2Bt : (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal B ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 two_ne_zero) ENNReal.ofReal_ne_top
  have hV : V = ENNReal.ofReal (|(k : ℝ)|⁻¹) / (2⁻¹ * ENNReal.ofReal B) := by
    exact (ENNReal.eq_div_iff h2B h2Bt).2 e1.symm
  rw [hV, ENNReal.ofReal_div_of_pos hB0, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.mul_inv
      (Or.inl (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)) (Or.inl (ENNReal.inv_ne_top.2 two_ne_zero)), inv_inv,
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  ring

theorem LOne_pos_of_binDensityProduct {D : ℤ} [IsQuadDisc D] {B : ℝ} (hB : B = 2 / Binary.LOne D) (hB0 : 0 < B) :
    0 < Binary.LOne D := by
  rw [hB] at hB0
  exact (div_pos_iff_of_pos_left two_pos).1 hB0

/-- The rational frame $e_0$ of $\langle1\rangle$ for $x_0^2+x_1^2$. -/
def ratFrameOne_sumTwoSq : RatFrame (up sumTwoSqZ) (DVR.unary (1 : 𝓞 ℚ)) :=
  Int.cast_one (R := 𝓞 ℚ) ▸ (ratFrameOfInt 1 1 (x := 1) (y := 0) (by norm_num) :
    RatFrame (up sumTwoSqZ) (DVR.unary ((1 : ℤ) : 𝓞 ℚ)))

/-- The rational frame $e_0$ of $\langle1\rangle$ for $x_0^2-2x_1^2$. -/
def ratFrameOne_pell2 : RatFrame (up pell2Z) (DVR.unary (1 : 𝓞 ℚ)) :=
  Int.cast_one (R := 𝓞 ℚ) ▸ (ratFrameOfInt 1 (-2) (x := 1) (y := 0) (by norm_num) :
    RatFrame (up pell2Z) (DVR.unary ((1 : ℤ) : 𝓞 ℚ)))

/-- $B(1) > 0$ from the headline (`tsum_repCount_eq_ratio`). -/
theorem binDensityProduct_one_pos_sumTwoSq : 0 < binDensityProduct (up sumTwoSqZ) (DVR.unary 1) (QField (-4)) :=
  (tsum_repCount_eq_ratio (up sumTwoSqZ) nondegenerate_up_sumTwoSq anisotropicF_up_sumTwoSq (QField (-4))
    isDiscField_sumTwoSq ratFrameOne_sumTwoSq
    tsum_repCount_one_sumTwoSq (m := 1) (by simp)
    ratFrameOne_sumTwoSq).1

theorem binDensityProduct_one_pos_pell2 : 0 < binDensityProduct (up pell2Z) (DVR.unary 1) (QField 8) :=
  (tsum_repCount_eq_ratio (up pell2Z) nondegenerate_up_pell2 anisotropicF_up_pell2 (QField 8)
    isDiscField_pell2 ratFrameOne_pell2
    tsum_repCount_one_pell2 (m := 1) (by simp)
    ratFrameOne_pell2).1

/-- **The unit volume of $x_0^2+x_1^2$** (the genus of $\mathbb Z^2$; $v(M_i)$ = `unitVolume`, the covolume of the unit
group $SO(M_i)$ in $SO(2)(\mathbb R)$ for Weil's measure):
$$\sum_iv(M_i) = \frac{L(1,\chi_{-4})}4,$$
$L(1,\chi_{-4})$ = `Binary.LOne (-4)` (Mathlib's Dirichlet $L$-function at $s = 1$). From Siegel's formula for binary
forms at $m = 1$ (`siegelIndefinite_binary_uncond`). Unconditional. -/
@[kb "siegel1935" "Hauptsatz, n = 2, m = 1, at the number 1 (unit volume via L(1, χ)) [unverified]"]
theorem unitVolume_sum_sumTwoSq :
    ∑' i, unitVolume (up sumTwoSqZ) nondegenerate_up_sumTwoSq i = ENNReal.ofReal (Binary.LOne (-4) / 4) := by
  have hpos := binDensityProduct_one_pos_sumTwoSq
  have hL := LOne_pos_of_binDensityProduct binDensityProduct_one_sumTwoSq hpos
  rw [tsum_unitVolume_of_one (up sumTwoSqZ) nondegenerate_up_sumTwoSq anisotropicF_up_sumTwoSq (QField (-4))
    isDiscField_sumTwoSq ratFrameOne_sumTwoSq
    tsum_repCount_one_sumTwoSq (k := 4) (by rw [sumTwoSqZ, hessian_det_up_diag]; norm_num)
    binDensityProduct_one_sumTwoSq (binDensityProduct_one_sumTwoSq ▸ hpos)]
  congr 1
  field_simp
  norm_num

/-- **The unit volume of $x_0^2-2x_1^2$** (the genus of $\mathbb Z^2$; $v(M_i)$ = `unitVolume`, the covolume of the unit
group $SO(M_i)$, infinite: $\pm(3+2\sqrt2)^k$ for $\mathbb Z^2$, in $SO(1,1)(\mathbb R)$ for Weil's measure):
$$\sum_iv(M_i) = \frac{L(1,\chi_8)}8,$$
$L(1,\chi_8)$ = `Binary.LOne 8`. From Siegel's formula for binary forms at $m = 1$. Unconditional. -/
@[kb "siegel1935" "Hauptsatz, n = 2, m = 1, at the number 1 (unit volume via L(1, χ)) [unverified]"]
theorem unitVolume_sum_pell2 :
    ∑' i, unitVolume (up pell2Z) nondegenerate_up_pell2 i = ENNReal.ofReal (Binary.LOne 8 / 8) := by
  have hpos := binDensityProduct_one_pos_pell2
  have hL := LOne_pos_of_binDensityProduct binDensityProduct_one_pell2 hpos
  rw [tsum_unitVolume_of_one (up pell2Z) nondegenerate_up_pell2 anisotropicF_up_pell2 (QField 8)
    isDiscField_pell2 ratFrameOne_pell2
    tsum_repCount_one_pell2 (k := -8) (by rw [pell2Z, hessian_det_up_diag]; norm_num)
    binDensityProduct_one_pell2 (binDensityProduct_one_pell2 ▸ hpos)]
  congr 1
  field_simp
  norm_num

/-- **The unit volume of $x_0^2+x_1^2$ with Dirichlet's class number formula:**
$\sum_iv(M_i) = \pi\,h(-4)/(4\,w(-4))$, $h(-4)$ = `classNumber (QField (-4))`, $w(-4)$ = `torsionOrder (QField (-4))`
(the number of roots of unity of $\mathbb Q(i)$). -/
theorem unitVolume_sum_sumTwoSq_classNumber :
    ∑' i, unitVolume (up sumTwoSqZ) nondegenerate_up_sumTwoSq i =
      ENNReal.ofReal (π * classNumber (QField (-4)) / (4 * torsionOrder (QField (-4)))) := by
  rw [unitVolume_sum_sumTwoSq, Binary.LOne, classNumberFormula_neg (by norm_num), Complex.ofReal_re]
  congr 1
  have h4 : |((-4 : ℤ) : ℝ)| = 2 ^ 2 := by norm_num
  rw [h4, Real.sqrt_sq (by norm_num)]
  have hw : (torsionOrder (QField (-4)) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (torsionOrder_pos _).ne'
  field_simp

/-- **The unit volume of $x_0^2-2x_1^2$ with Dirichlet's class number formula:**
$\sum_iv(M_i) = h(8)\,R(8)/(8\sqrt2)$, $h(8)$ = `classNumber (QField 8)`, $R(8)$ = `regulator (QField 8)`
$=\log\varepsilon$, $\varepsilon$ the fundamental unit of $\mathbb Z[\sqrt2]$. -/
theorem unitVolume_sum_pell2_classNumber :
    ∑' i, unitVolume (up pell2Z) nondegenerate_up_pell2 i =
      ENNReal.ofReal (classNumber (QField 8) * regulator (QField 8) / (8 * Real.sqrt 2)) := by
  rw [unitVolume_sum_pell2, Binary.LOne, classNumberFormula_pos (by norm_num), Complex.ofReal_re]
  congr 1
  have h8 : Real.sqrt ((8 : ℤ) : ℝ) = 2 * Real.sqrt 2 := by
    rw [show ((8 : ℤ) : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [h8]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp

end QuadFormsKB.Tamagawa.Classical
