import QuadFormsKB.Tamagawa.BinaryFrameStep
import QuadFormsKB.Tamagawa.RatBridge3
import QuadFormsKB.Binary.EulerProductAtOne
import QuadFormsKB.Binary.GenusMass

/-!
# $\tau^{\mathrm{reg}}(SO_2) = 2$ over $\mathbb Q$

**Layer:** binary forms over $\mathcal O_{\mathbb Q} = \mathbb Z$. The binary Siegel formula (`Binary.siegelFormula_binary`,
$\varepsilon = \frac12$, $D < 0$ fundamental, $f$ primitive positive definite of discriminant $D$) is moved to $\mathcal O_{\mathbb Q}$
(`RatBridge.up`) and fed into part 1's backwards step $1 \to 2$ (`tauSOReg_eq_two_of_siegel`).

**The bridge (§1–2).**
* `kronChi D` $= \chi_D(p)$ on the primes $\mathfrak p = (p)$ of $\mathcal O_{\mathbb Q}$, and **`hasLOne_kronChi`**: the
  $L_{\mathbb Q}(1,\chi) := \lim_{s\to1^+}\prod_p(1-\chi(p)p^{-s})^{-1}$ is $L(1,\chi_D)$ (Mathlib's Euler product of
  $L(s,\chi_D)$ for $s > 1$ and the continuity of `DirichletCharacter.LFunction` at $1$).
* **`regProd_up_eq_binaryEulerValue`**: the regularized product of part 1, $L(1,\chi_f)^{-1}\prod_p\beta_p(f,m)(1-\chi_f(p)/p)^{-1}$
  with the character $\chi_f$ = `chiP · up f`, is `binaryEulerValue f D m`
  $= L(1,\chi_D)^{-1}\prod_{p\mid mD}\beta_p(m)/(1-\chi_D(p)/p)$.
  The characters $\chi_f$ and $\chi_D$ are compared **without residue symbols**: both $1 - \chi_f(p)/p$ (part 1,
  `localDensity_eq_one_sub_chiP`) and $1 - \chi_D(p)/p$ (`localDensity_good_binary`) equal $\beta_p(f, m)$ at almost all $p$.
* `siegelProduct2Reg_up`: $S^{\mathrm{reg}}_2(f\otimes\mathcal O_{\mathbb Q}, m) = \beta_\infty(m)\cdot$ `binaryEulerValue f D m` (`aEWith`).

**Results (§3–4).**
* **`tauSOReg_up_posForms`**: $\tau^{\mathrm{reg}}(SO(f\otimes\mathcal O_{\mathbb Q})) = 2$ for every $f \in$ `PosForms D`, $D < 0$
  fundamental. *Proof:* at one $m$ with $r_{\mathcal G}(m) \ne 0$ (`exists_genusRepAvg_ne_zero`),
  the binary Siegel formula
  $r_{\mathcal G}(m) = \frac12\beta_\infty(m)P_f(m)$ reads $\mathrm{repMass}(m) = \frac12\mathrm{Mass}\cdot S^{\mathrm{reg}}_2(m)$ (`mass_rat`,
  `repMass_rat`), and part 1 gives $\tau^{\mathrm{reg}} = 2$.
* **`binaryTamagawaTwoReg_rat : BinaryTamagawaTwoReg ℚ`** and `binaryTamagawaTwoRegDiag_rat` (**unconditional**): every
  totally definite binary $Q'$ over $\mathcal O_{\mathbb Q}$ has $\det H'$ in the square class of $-D$ for a fundamental
  $D < 0$ (`exists_isQuadDisc_sq`), whose principal form (`princForm D`) is in `PosForms D`;
  `binaryTamagawaTwoReg_of_family` finishes.
* **The ℚ rank-3 interface:** `siegelFormulaAt3_rat_of_tau` — `TamagawaNumberTwo Q₀` $\Rightarrow$
  `SiegelFormulaAt3 Q₀ m` for every totally positive $m$; `siegelFormulaAt3_rat` — the same from
  `TernaryTamagawaTwo ℚ`; and `siegelFormula3_rat` — Hanke's `SiegelFormula3 Q (eulerProductReg3 Q)` for every positive
  definite ternary $Q$ over $\mathbb Z$, from `TernaryTamagawaTwo ℚ`. The rank-3 Siegel formula over $\mathbb Q$ is now
  conditional only on $\tau(SO_3) = 2$.
-/

open NumberField IsDedekindDomain Matrix Filter Topology
open scoped Real

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.BinaryTauRat

open QuadFormsKB.Lattices NFEuler RegProd LocalDensity QuadForm QuadFormsKB.HilbertModular RatBridge
open QuadFormsKB.Binary

/-! ### 1. $L_{\mathbb Q}(1, \chi_D)$ -/

section LOne

variable {D : ℤ} [IsQuadDisc D]

/-- **$\chi_D$ on the primes of $\mathcal O_{\mathbb Q}$:** `kronChi D 𝔭` $= \chi_D(p)$ (`kronR`), $p$ the prime under $\mathfrak p$
(`Rat.HeightOneSpectrum.natGenerator`). -/
def kronChi (D : ℤ) (v : HeightOneSpectrum (𝓞 ℚ)) : ℝ := kronR D (Rat.HeightOneSpectrum.natGenerator v)

theorem normP_rat (v : HeightOneSpectrum (𝓞 ℚ)) : (normP v : ℕ) = Rat.HeightOneSpectrum.natGenerator v :=
  NF.absNorm_rat v

theorem abs_kronChi_le (v : HeightOneSpectrum (𝓞 ℚ)) : |kronChi D v| ≤ 1 := by
  unfold kronChi
  rcases kronR_trichotomy (D := D) (Rat.HeightOneSpectrum.natGenerator v) with h | h | h <;> rw [h] <;> norm_num

/-- **For $s > 1$, $L_{\mathbb Q}(s, \chi_D)$ (`LFunctionNF`, the Euler product over the primes of $\mathcal O_{\mathbb Q}$) is
Mathlib's $L(s,\chi_D)$.** -/
theorem LFunctionNF_kronChi {s : ℝ} (hs : 1 < s) :
    ((LFunctionNF (kronChi D) s : ℝ) : ℂ) = (kroneckerChar D).LFunction s := by
  have hs' : 1 < (s : ℂ).re := by simpa using hs
  rw [DirichletCharacter.LFunction_eq_LSeries _ hs']
  have h1 := (hasProd_LFunctionNF (fun v => abs_kronChi_le (D := D) v) hs).map Complex.ofRealHom
    Complex.continuous_ofReal
  have h2 := ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm.hasProd_iff).mpr h1
  refine h2.unique ((kroneckerChar D).LSeries_eulerProduct_hasProd hs' |>.congr_fun fun p => ?_)
  have hp : Rat.HeightOneSpectrum.natGenerator ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p) = p := by
    have := congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply p)
    exact this
  simp only [Function.comp_apply, Complex.ofRealHom_eq_coe, lFactor, kronChi, normP_rat, hp]
  rw [kroneckerChar_apply]
  push_cast
  rw [cpow_neg_eq]
  simp [kronR]

/-- **$L_{\mathbb Q}(1, \chi_D)$ is `Binary.LOne D`** $= L(1,\chi_D)$ (`hasLOne_kronChi`): $L(s,\chi_D)$ is continuous
at $s = 1$ ($\chi_D \ne 1$, `kroneckerChar_ne_one`) and equals the Euler product for $s > 1$. -/
theorem hasLOne_kronChi : HasLOne (kronChi D) (Binary.LOne D) := by
  have hcont := (DirichletCharacter.differentiable_LFunction (kroneckerChar_ne_one (D := D))).continuous
  have h1 : Tendsto (fun s : ℝ => ((kroneckerChar D).LFunction (s : ℂ)).re) (𝓝[>] 1)
      (𝓝 ((kroneckerChar D).LFunction ((1 : ℝ) : ℂ)).re) :=
    ((Complex.continuous_re.comp (hcont.comp Complex.continuous_ofReal)).tendsto 1).mono_left nhdsWithin_le_nhds
  rw [Complex.ofReal_one] at h1
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [← LFunctionNF_kronChi (D := D) hs, Complex.ofReal_re]

end LOne

/-! ### 2. The regularized product of $\beta_p(f, m)$ is `binaryEulerValue` -/

section Bridge

variable {D : ℤ} [IsQuadDisc D]

theorem natGenerator_injective :
    Function.Injective fun v : HeightOneSpectrum (𝓞 ℚ) => Rat.HeightOneSpectrum.natGenerator v :=
  fun _ _ h => (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective (Subtype.ext h)

theorem natGenerator_primesEquiv_symm (p : Nat.Primes) :
    Rat.HeightOneSpectrum.natGenerator ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p) = p :=
  congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply p)

/-- The primes of $\mathcal O_{\mathbb Q}$ over the prime divisors of $N \ne 0$ form a finite set. -/
theorem finite_natGenerator_dvd {N : ℕ} (hN : N ≠ 0) :
    {v : HeightOneSpectrum (𝓞 ℚ) | Rat.HeightOneSpectrum.natGenerator v ∣ N}.Finite :=
  ((Nat.divisors N).finite_toSet.preimage natGenerator_injective.injOn).subset fun v hv => by
    simp only [Finset.mem_coe, Set.mem_preimage, Nat.mem_divisors]
    exact ⟨hv, hN⟩

/-- **The good densities on $\mathcal O_{\mathbb Q}$:** at $\mathfrak p = (p)$ with $p \nmid mD$,
$\beta_\mathfrak p(f\otimes\mathcal O_{\mathbb Q}, m) = 1 - \chi_D(p)/p$ (`localDensity_good_binary`, `NF.localDensity_rat`). -/
theorem localDensity_up_good {f : BinQF} (hD : f.disc = D) {m : ℤ} (hm : m ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ¬ (Rat.HeightOneSpectrum.natGenerator v : ℤ) ∣ m * D) :
    NF.localDensity v (up f) (m : 𝓞 ℚ) = 1 - kronChi D v / (normP v : ℝ) := by
  set p := Rat.HeightOneSpectrum.natGenerator v
  have : Fact p.Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have hpD : ¬ (p : ℤ) ∣ D := fun h => hv (dvd_mul_of_dvd_right h m)
  have hpm : ¬ p ∣ m.natAbs := fun h => hv (dvd_mul_of_dvd_left (Int.natCast_dvd.mpr h) D)
  rw [NF.localDensity_rat, localDensity_good_binary f hD p hpD m hm,
    Nat.factorization_eq_zero_of_not_dvd hpm, goodFactor_zero, normP_rat]
  rfl

/-- **The regularized binary product over $\mathbb Q$ is the value `binaryEulerValue`**: for $f$ of
fundamental discriminant $D$ with $f\otimes\mathcal O_{\mathbb Q}$ positive definite, and an integer $m \ge 1$ represented by $f$
over $\mathbb Q$,
$$L(1,\chi_f)^{-1}\prod_p\beta_p(f,m)\Bigl(1-\frac{\chi_f(p)}p\Bigr)^{-1} = L(1,\chi_D)^{-1}\prod_{p\mid mD}\frac{\beta_p(m)}{1-\chi_D(p)/p}
\quad(=\texttt{binaryEulerValue}\ f\ D\ m),$$
$\chi_f$ = `chiP · up f`. *Proof:* $\chi_f = \chi_D$ off a finite set
(both $1-\chi(p)/p$ equal $\beta_p$ at almost all $p$:
`localDensity_eq_one_sub_chiP`, `localDensity_up_good`), so `regProd_congr_finite` switches to $\chi_D$, whose $L(1,\cdot)$ is
`Binary.LOne D` (`hasLOne_kronChi`); the corrected product is the finite product over $p \mid mD$, reindexed by
`primesEquiv`. -/
@[kb "siegel1935" "§§1–2 (n = 2, regularized product over ℚ) [unverified locator]"]
theorem regProd_up_eq_binaryEulerValue {f : BinQF} (hD : f.disc = D) (hpd : IsTotallyPosDef (formF (up f)))
    {m : ℤ} (hm : 1 ≤ m) (hrep : ∃ ξ, (formF (up f)).eval ξ = algebraMap (𝓞 ℚ) ℚ (m : 𝓞 ℚ)) :
    regProd (fun v => chiP v (up f)) (-1) (fun v => NF.localDensity v (up f) (m : 𝓞 ℚ)) =
      binaryEulerValue f D m := by
  classical
  have hm0 : m ≠ 0 := by omega
  have hD0 : D ≠ 0 := by have := three_le_natAbs (D := D); omega
  have hN : (m * D).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (mul_ne_zero hm0 hD0)
  set T := (finite_natGenerator_dvd hN).toFinset
  have hT : ∀ v, v ∉ T → ¬ (Rat.HeightOneSpectrum.natGenerator v : ℤ) ∣ m * D := fun v hv h =>
    hv ((Set.Finite.mem_toFinset _).mpr (Int.natCast_dvd.mp h))
  obtain ⟨S, hS⟩ := localDensity_eq_one_sub_chiP (up f) hpd (realEmb_intCast_pos hm) hrep
  set β : HeightOneSpectrum (𝓞 ℚ) → ℝ := fun v => NF.localDensity v (up f) (m : 𝓞 ℚ)
  have hNpos : ∀ v : HeightOneSpectrum (𝓞 ℚ), (normP v : ℝ) ≠ 0 := fun v => by
    have := two_le_normP v; positivity
  have hchi : ∀ v ∉ S ∪ T, chiP v (up f) = kronChi D v := fun v hv => by
    rw [Finset.mem_union, not_or] at hv
    have h1 := (hS v hv.1).symm.trans (localDensity_up_good hD hm0 v (hT v hv.2))
    have h2 : chiP v (up f) / (normP v : ℝ) = kronChi D v / (normP v : ℝ) := by linarith
    rwa [div_left_inj' (hNpos v)] at h2
  have hone : ∀ v ∉ T, β v * (1 - kronChi D v / (normP v : ℝ)) ^ (-1 : ℤ) = 1 := fun v hv => by
    simp only [β]
    rw [localDensity_up_good hD hm0 v (hT v hv), _root_.zpow_neg_one,
      mul_inv_cancel₀ (one_sub_div_pos (abs_kronChi_le v) v).ne']
  have hmul : Multipliable fun v => β v * (1 - kronChi D v / (normP v : ℝ)) ^ (-1 : ℤ) :=
    multipliable_of_ne_finset_one hone
  have hL := (hasLOne_kronChi (D := D))
  rw [regProd_congr_finite (fun v => abs_chiP_le (up f) v) (fun v => abs_kronChi_le v) (S ∪ T) hchi
    (by rw [hL.lOne_eq]; exact hL) (-1) β hmul]
  unfold regProd
  rw [hL.lOne_eq, tprod_eq_prod hone, _root_.zpow_neg_one, binaryEulerValue]
  congr 1
  unfold binaryEulerCorr
  refine Finset.prod_bij' (fun v _ => Rat.HeightOneSpectrum.natGenerator v)
    (fun p hp => (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
      (⟨p, Nat.prime_of_mem_primeFactors hp⟩ : Nat.Primes))
    (fun v hv => ?_) (fun p hp => ?_) (fun v _ => ?_) (fun p hp => ?_) (fun v _ => ?_)
  · exact Nat.mem_primeFactors.mpr ⟨Rat.HeightOneSpectrum.prime_natGenerator v,
      (Set.Finite.mem_toFinset (finite_natGenerator_dvd hN)).mp hv, hN⟩
  · refine (Set.Finite.mem_toFinset _).mpr ?_
    show Rat.HeightOneSpectrum.natGenerator _ ∣ _
    rw [natGenerator_primesEquiv_symm (⟨p, Nat.prime_of_mem_primeFactors hp⟩ : Nat.Primes)]
    exact Nat.dvd_of_mem_primeFactors hp
  · exact (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm_apply_apply v
  · exact natGenerator_primesEquiv_symm _
  · simp only [β]
    rw [NF.localDensity_rat, normP_rat, _root_.zpow_neg_one, ← div_eq_mul_inv]
    rfl

/-- **The rank-2 regularized Siegel product over $\mathbb Q$ is the binary Siegel value $\beta_\infty(m)P_f(m)$:**
$S^{\mathrm{reg}}_2(f\otimes\mathcal O_{\mathbb Q}, m) = $ `aEWith f m (binaryEulerValue f D m)` ($|d_{\mathbb Q}| = 1$, one real place,
`siegelProductWith_eq_discr_mul_aEWithNF`, `aEWithNF_rat`). -/
theorem siegelProduct2Reg_up {f : BinQF} (hD : f.disc = D) (hf : IntQF.PosDef f) {m : ℤ} (hm : 1 ≤ m)
    (hrep : ∃ ξ, (formF (up f)).eval ξ = algebraMap (𝓞 ℚ) ℚ (m : 𝓞 ℚ)) :
    siegelProduct2Reg (up f) (m : 𝓞 ℚ) = Siegel.aEWith f m (binaryEulerValue f D m) := by
  have hpd := (isTotallyPosDef_up_iff f).mpr hf
  rw [siegelProduct2Reg, siegelProductWith_eq_discr_mul_aEWithNF (isTotPosGram_Q₀ hpd) (by norm_num)
    (realEmb_intCast_pos hm), discrFactor_rat, one_mul, regProd_up_eq_binaryEulerValue hD hpd hm hrep]
  exact Siegel.aEWithNF_rat f m _

end Bridge

/-! ### 3. $\tau^{\mathrm{reg}}(SO_2) = 2$ for the forms of fundamental discriminant -/

section Tau

variable {D : ℤ} [IsQuadDisc D]

/-- **$\tau^{\mathrm{reg}}(SO(f\otimes\mathcal O_{\mathbb Q})) = 2$ for every primitive positive definite $f$ of fundamental
discriminant $D < 0$** (`PosForms D`). The backwards Weil step $1 \to 2$ (`tauSOReg_eq_two_of_siegel`, with $\tau(SO_1) = 1$)
applied to The binary Siegel formula (`siegelFormula_binary`, $\varepsilon = \frac12$) at one $m$ with
$r_{\mathcal G}(m) \ne 0$ (`exists_genusRepAvg_ne_zero`). Unconditional. -/
@[kb "weil1982" "Thm. 3.7.1 (τ = 2), rank 2 with convergence factors, over ℚ [unverified]"]
theorem tauSOReg_up_posForms [Fact (D < 0)] (f : PosForms D) : tauSOReg (up f.1) = 2 := by
  obtain ⟨m, hm0, -, hne⟩ := exists_genusRepAvg_ne_zero f
  have hf : IntQF.PosDef f.1 := (intQF_posDef_iff _).mpr ((BinQF.posDef_iff_posDef' _).mpr f.2.2.2)
  have hpd := (isTotallyPosDef_up_iff f.1).mpr hf
  have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0
  have hmass : 0 < Lattices.mass (formF (up f.1)) (stdLat ℚ 2) := mass_pos hpd _ (isIntegral_stdLat _)
  have hrepne : repMass (formF (up f.1)) (stdLat ℚ 2) (algebraMap (𝓞 ℚ) ℚ ((m : ℤ) : 𝓞 ℚ)) ≠ 0 := by
    rw [map_intCast, ← repMass_rat f.1 hf]
    intro h; apply hne; rw [Siegel.genusRepAvg, h, zero_div]
  have hrep : ∃ ξ, (formF (up f.1)).eval ξ = algebraMap (𝓞 ℚ) ℚ ((m : ℤ) : 𝓞 ℚ) := by
    by_contra h; exact hrepne (repMass_eq_zero_of_not_rep _ _ h)
  refine tauSOReg_eq_two_of_siegel (up f.1) hpd (realEmb_intCast_pos hm1) hrepne ?_
  rw [siegelProduct2Reg_up f.2.2.1 hf hm1 hrep]
  have hS := siegelFormula_binary f hm0
  rw [Siegel.genusRepAvg, mass_rat f.1 hf, repMass_rat f.1 hf, div_eq_iff hmass.ne'] at hS
  rw [map_intCast, hS]
  ring

end Tau

/-! ### 4. Every square class: `BinaryTamagawaTwoReg ℚ` -/

section Cover

/-- **The principal form of discriminant $D$** ($D \equiv 0, 1 \bmod 4$): $x^2 + xy + \frac{1-D}4y^2$ if $D \equiv 1 \pmod 4$,
$x^2 - \frac D4y^2$ if $D \equiv 0 \pmod 4$. -/
def princForm (D : ℤ) : BinQF :=
  if D % 4 = 1 then BinQF.mk 1 1 ((1 - D) / 4) else BinQF.mk 1 0 (-(D / 4))

/-- The principal form of a discriminant $D < 0$ is primitive, positive definite, of discriminant $D$ (`PosForms D`). -/
theorem princForm_mem {D : ℤ} (hD4 : D % 4 = 0 ∨ D % 4 = 1) (hneg : D < 0) :
    Primitive (princForm D) ∧ (princForm D).disc = D ∧ (princForm D).PosDef' := by
  unfold princForm
  split_ifs with h
  · refine ⟨by simp [Primitive], ?_, by simp, ?_⟩
    · simp only [BinQF.disc, BinQF.a_mk, BinQF.b_mk, BinQF.c_mk]; omega
    · simp only [BinQF.disc, BinQF.a_mk, BinQF.b_mk, BinQF.c_mk]; omega
  · refine ⟨by simp [Primitive], ?_, by simp, ?_⟩
    · simp only [BinQF.disc, BinQF.a_mk, BinQF.b_mk, BinQF.c_mk]; omega
    · simp only [BinQF.disc, BinQF.a_mk, BinQF.b_mk, BinQF.c_mk]; omega

/-- **Every positive integer is $-D$ times a square, up to squares, for a fundamental discriminant $D < 0$:** for $k \ge 1$ there
are $D$ with `IsQuadDisc D`, $D < 0$, and nonzero $u, w \in \mathbb Z$ with $-D\,u^2 = k\,w^2$ (write $k = b^2a$ with $a$ squarefree;
$D = -a$ if $-a \equiv 1 \pmod 4$, else $D = -4a$). -/
theorem exists_isQuadDisc_sq {k : ℤ} (hk : 1 ≤ k) :
    ∃ D : ℤ, IsQuadDisc D ∧ D < 0 ∧ ∃ u w : ℤ, u ≠ 0 ∧ w ≠ 0 ∧ -D * u ^ 2 = k * w ^ 2 := by
  obtain ⟨b, a, hb2a, hsq⟩ := exists_sq_mul_squarefree k.toNat
  have hk' : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg (by omega)
  have hkz : k = (b : ℤ) ^ 2 * a := by rw [← hk', ← hb2a]; push_cast; ring
  have ha0 : (a : ℤ) ≠ 0 := by exact_mod_cast hsq.ne_zero
  have hb0 : (b : ℤ) ≠ 0 := by rintro h; rw [h] at hkz; omega
  have ha1 : (1 : ℤ) ≤ a := by have := hsq.ne_zero; omega
  have hsqZ : Squarefree (-(a : ℤ)) := Int.squarefree_natAbs.mp (by simpa using hsq)
  have h4 : ¬ (4 : ℤ) ∣ a := by
    intro h
    have h4' : (2 * 2 : ℕ) ∣ a := by exact_mod_cast h
    exact absurd (Nat.isUnit_iff.mp (hsq 2 h4')) (by norm_num)
  by_cases h : (-(a : ℤ)) % 4 = 1
  · refine ⟨-(a : ℤ), ⟨Int.isFundamentalDiscr_iff_squarefree.mpr (Or.inl ⟨h, hsqZ⟩), by omega⟩, by omega,
      b, 1, hb0, one_ne_zero, by rw [hkz]; ring⟩
  · have e : -4 * (a : ℤ) / 4 = -(a : ℤ) := by omega
    refine ⟨-4 * (a : ℤ), ⟨Int.isFundamentalDiscr_iff_squarefree.mpr (Or.inr ⟨by omega, by rwa [e], by omega⟩),
      by omega⟩, by omega, b, 2, hb0, two_ne_zero, by rw [hkz]; ring⟩

theorem hessian_det_up (f : QuadForm ℤ 2) : (up f).hessian.det = ((f.hessian.det : ℤ) : 𝓞 ℚ) := by
  have e : (up f).hessian = f.hessian.map (Int.castRingHom (𝓞 ℚ)) := by
    ext i j; simp [QuadForm.hessian, QuadForm.map]
  rw [e, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rfl

/-- **$\tau^{\mathrm{reg}}(SO_2) = 2$ over $\mathbb Q$: `BinaryTamagawaTwoReg ℚ` is a theorem** (the rank-2 input, unconditional).
Every totally definite binary $Q'$ over $\mathcal O_{\mathbb Q}$ has $\det H' = k \ge 1$, and $k$ is in the square class of $-D$ for a
fundamental $D < 0$ (`exists_isQuadDisc_sq`); the principal form of $D$ has $\det H = -D$ and $\tau^{\mathrm{reg}} = 2$
(`tauSOReg_up_posForms`), so `binaryTamagawaTwoReg_of_family` applies. Source of the value: Weil 1982, Thm. 3.7.1
(rank 2, with convergence factors) [unverified]; here *derived* from Siegel's binary formula and $\tau(SO_1) = 1$. -/
@[kb "weil1982" "Thm. 3.7.1 (τ = 2), rank 2 with convergence factors, over ℚ [unverified]"]
theorem binaryTamagawaTwoReg_rat : BinaryTamagawaTwoReg ℚ := by
  refine binaryTamagawaTwoReg_of_family {R | ∃ D : ℤ, ∃ _ : IsQuadDisc D, D < 0 ∧ R = up (princForm D)} ?_ ?_
  · rintro R ⟨D, hD, hneg, rfl⟩ -
    have : Fact (D < 0) := ⟨hneg⟩
    exact tauSOReg_up_posForms ⟨princForm D, princForm_mem hD.fund.1 hneg⟩
  · intro Q' hpd
    obtain ⟨k, hk, hkQ⟩ := exists_int_of_pos (realEmb_det_hessian_pos hpd)
    obtain ⟨D, hD, hneg, u, w, hu, hw, h⟩ := exists_isQuadDisc_sq hk
    have hmem := princForm_mem hD.fund.1 hneg
    refine ⟨up (princForm D), ⟨D, hD, hneg, rfl⟩,
      (isTotallyPosDef_up_iff _).mpr ((intQF_posDef_iff _).mpr ((BinQF.posDef_iff_posDef' _).mpr hmem.2.2)),
      (u : 𝓞 ℚ), (w : 𝓞 ℚ), by exact_mod_cast hu, by exact_mod_cast hw, ?_⟩
    rw [hessian_det_up, hessian_det_eq_neg_disc, hmem.2.1, ← hkQ]
    have := congrArg (Int.cast : ℤ → 𝓞 ℚ) h
    push_cast at this
    exact this

/-- **The diagonal form of the input over $\mathbb Q$:** $\tau^{\mathrm{reg}}\langle1, D\rangle = 2$ for every
totally definite
$\langle1, D\rangle$ over $\mathcal O_{\mathbb Q}$. -/
theorem binaryTamagawaTwoRegDiag_rat : BinaryTamagawaTwoRegDiag ℚ :=
  binaryTamagawaTwoReg_rat.toDiag

end Cover

/-! ### 5. The rank-3 Siegel formula over $\mathbb Q$: conditional only on $\tau(SO_3) = 2$ -/

section Rank3

/-- **Siegel's formula in rank 3 over $\mathbb Q$ from $\tau(SO(Q_0)) = 2$ alone:** for $Q_0$ totally positive definite ternary over
$\mathcal O_{\mathbb Q}$ with `TamagawaNumberTwo Q₀`, `SiegelFormulaAt3 Q₀ m` holds for every totally positive $m$ (via
`siegelFormulaAt3_of_tau` with `binaryTamagawaTwoReg_rat`). -/
@[kb "siegel1935" "Hauptsatz, n = 3, over ℚ (regularized; from τ(SO_3) = 2) [unverified]"]
theorem siegelFormulaAt3_rat_of_tau (Q₀ : QuadForm (𝓞 ℚ) 3) (hpd : IsTotallyPosDef (formF Q₀))
    (hτ : TamagawaNumberTwo Q₀) {m : 𝓞 ℚ} (hm : ∀ v : InfinitePlace ℚ, 0 < realEmb ℚ v (algebraMap (𝓞 ℚ) ℚ m)) :
    SiegelFormulaAt3 Q₀ m :=
  siegelFormulaAt3_of_tau Q₀ hpd hτ binaryTamagawaTwoReg_rat hm

/-- **Siegel's formula in rank 3 over $\mathbb Q$, conditional only on `TernaryTamagawaTwo ℚ`** ($\tau(SO_3) = 2$ for the
ternary forms over $\mathcal O_{\mathbb Q}$): `SiegelFormulaAt3 Q₀ m` for every totally positive definite ternary $Q_0$ and every
totally positive $m$. -/
@[kb "siegel1935" "Hauptsatz, n = 3, over ℚ (regularized; conditional on τ(SO_3) = 2) [unverified]"]
theorem siegelFormulaAt3_rat (hT : TernaryTamagawaTwo ℚ) (Q₀ : QuadForm (𝓞 ℚ) 3) (hpd : IsTotallyPosDef (formF Q₀))
    {m : 𝓞 ℚ} (hm : ∀ v : InfinitePlace ℚ, 0 < realEmb ℚ v (algebraMap (𝓞 ℚ) ℚ m)) : SiegelFormulaAt3 Q₀ m :=
  siegelFormulaAt3_rat_of_tau Q₀ hpd
    (hT.tau_eq_two Q₀ (nondegenerate_of_map hpd.nondegenerate) hpd (isIntegral_stdLat Q₀)) hm

/-- **Hanke's rank-3 input over $\mathbb Z$ with the regularized product, conditional only on `TernaryTamagawaTwo ℚ`:**
`Siegel.SiegelFormula3 Q (eulerProductReg3 Q)` ($r_{\mathrm{Gen}(Q)}(m) = \beta_\infty(m)P_{\mathrm{reg}}(m)$ for all $m \ge 1$) for every
positive definite ternary $Q$ over $\mathbb Z$ (via the bridge `siegelFormula3_iff_siegelFormulaAt3`). -/
@[kb "siegel1935" "Hauptsatz, n = 3, over ℤ (Hanke's form, regularized; conditional on τ(SO_3) = 2) [unverified]"]
theorem siegelFormula3_rat (hT : TernaryTamagawaTwo ℚ) (Q : QuadForm ℤ 3) (hQ : IntQF.PosDef Q) :
    Siegel.SiegelFormula3 Q (Siegel.eulerProductReg3 Q) :=
  (RatBridge3.siegelFormula3_iff_siegelFormulaAt3 Q hQ).mpr fun _ hm =>
    siegelFormulaAt3_rat hT (up Q) ((isTotallyPosDef_up_iff Q).mpr hQ) (realEmb_intCast_pos hm)

end Rank3

end QuadFormsKB.Tamagawa.BinaryTauRat
