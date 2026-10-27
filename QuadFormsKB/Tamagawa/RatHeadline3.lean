import QuadFormsKB.Tamagawa.BinaryTauRat
import QuadFormsKB.Siegel.MainResults
import QuadFormsKB.Siegel.FourSquaresClassNumber

/-!
# The rank-3 headline over $\mathbb Q$

**Layer:** positive definite ternary forms over $\mathbb Z$; the number field $\mathbb Q$ (primes of $\mathcal O_{\mathbb Q}$ $\leftrightarrow$
rational primes by `primesEquiv`). This completes the ℚ part of the rank-3 treatment.

**Results (all proved; none adds a hypothesis).**
* `prod_primesNormLe_rat`, `eulerPartialProdNF_rat`: partial products over $\{N\mathfrak p \le X\}$ are products over $p \le X$.
* `isEulerProductValueNF_kronChi`, **`naturalOrderEulerOne_of_almost_kron`**: `NaturalOrderEulerOne χ` (the input, a prime
  ideal theorem) is a theorem over $\mathbb Q$ for every $\chi$ equal to a Kronecker character $\chi_D$ off a finite set
  (`EulerOne.tendsto_prod_primesBelow` transferred).
* `charNF_intCast_eq_legendreSym` ($(x/\mathfrak p) = (x/p)$ over $\mathcal O_{\mathbb Q}$), **`exists_chiTern_eq_kronChi`**
  ($\chi_m$ is $\chi_D$ off a finite set, $D<0$ fundamental, via `exists_isQuadDisc_sq` and `kronZ_odd_prime`).
* **`isEulerProductValue_eulerProductReg3`** (unconditional): $\prod_{p \le X}\beta_p(m) \to P_{\mathrm{reg}}(m)$ =
  `eulerProductReg3 Q m` for $Q$ positive definite ternary, $m \ge 1$.

**Conditional on `TernaryTamagawaTwo ℚ` only** (`(hT : TernaryTamagawaTwo ℚ)`): `siegelFormula3_natural_rat`,
`genusRepAvg_eq_aEWith_of_isEulerProductValue`, `siegelFormula3_and_natural_rat`, and Hanke's rank-3 corollaries
`thm_5_4_genus3_rat`, `thm_5_7_a_genus_rat`, `thm_5_7_a_genus_nat_rat`, `thm_6_1_rat`, `thm_6_2_rat` (no `SiegelFormula3 Q P` and no
`IsEulerProductValue` hypotheses), and Gauss's $r_3$: `repNum_sumSq_three_rat` (class number one, `genusClasses_sumSq`).

-/

open NumberField IsDedekindDomain Matrix Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.RatHeadline3

open QuadFormsKB.Lattices NFEuler RegProd LocalDensity QuadForm QuadFormsKB.HilbertModular RatBridge
open QuadFormsKB.Binary QuadFormsKB.Tamagawa.BinaryTauRat

/-! ### 1. Natural order over $\mathbb Q$ versus $p \le X$ -/

/-- **Partial products over the primes of $\mathcal O_{\mathbb Q}$ of norm $\le X$ are the products over $p \le X$.** -/
theorem prod_primesNormLe_rat (g : ℕ → ℝ) (X : ℕ) :
    ∏ v ∈ primesNormLe ℚ X, g (Rat.HeightOneSpectrum.natGenerator v) = ∏ p ∈ Siegel.primesUpTo X, g p := by
  refine Finset.prod_bij (fun v _ => (⟨Rat.HeightOneSpectrum.natGenerator v,
    Rat.HeightOneSpectrum.prime_natGenerator v⟩ : AWS.PrimeIdx)) (fun v hv => ?_) (fun v _ w _ h => ?_)
    (fun p hp => ?_) (fun v _ => rfl)
  · simp only [mem_primesNormLe, normP_rat] at hv
    simp only [Siegel.primesUpTo, Finset.mem_subtype, Finset.mem_range]
    omega
  · exact natGenerator_injective (congrArg Subtype.val h)
  · refine ⟨(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p.1, p.2⟩, ?_, ?_⟩
    · simp only [Siegel.primesUpTo, Finset.mem_subtype, Finset.mem_range] at hp
      have h : Rat.HeightOneSpectrum.natGenerator
          ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p.1, p.2⟩) = p.1 :=
        natGenerator_primesEquiv_symm ⟨p.1, p.2⟩
      rw [mem_primesNormLe, normP_rat, h]
      omega
    · exact Subtype.ext (natGenerator_primesEquiv_symm ⟨p.1, p.2⟩)

/-- Natural-order partial products of a function of the underlying rational prime. -/
theorem eulerPartialProdNF_rat (g : ℕ → ℝ) :
    eulerPartialProdNF (fun v : HeightOneSpectrum (𝓞 ℚ) => g (Rat.HeightOneSpectrum.natGenerator v)) =
      fun X => ∏ p ∈ Siegel.primesUpTo X, g p :=
  funext fun X => prod_primesNormLe_rat g X

/-! ### 2. The natural-order Euler product of $L(1,\chi)$ over $\mathbb Q$ -/

section Kron

variable {D : ℤ} [IsQuadDisc D]

theorem LOne_ne_zero : Binary.LOne D ≠ 0 := by
  intro h
  have h1 := LFunction_one_eq_ofReal (D := D)
  rw [h, Complex.ofReal_zero] at h1
  exact DirichletCharacter.LFunction_apply_one_ne_zero (kroneckerChar_ne_one (D := D)) h1

/-- **The natural-order Euler product of $L(1,\chi_D)$ over $\mathbb Q$** (`EulerOne.tendsto_prod_primesBelow` transferred
along `primesEquiv`): $\prod_{N\mathfrak p \le X}(1-\chi_D(\mathfrak p)/N\mathfrak p)^{-1} \to L(1,\chi_D)$. -/
theorem isEulerProductValueNF_kronChi : IsEulerProductValueNF (lFactor (kronChi D) 1) (Binary.LOne D) := by
  have h := (tendsto_prod_one_sub_kronR_div (D := D)).inv₀ (inv_ne_zero LOne_ne_zero)
  rw [inv_inv] at h
  have e : lFactor (kronChi D) 1 = fun v : HeightOneSpectrum (𝓞 ℚ) =>
      (fun p : ℕ => (1 - kronR D p / p)⁻¹) (Rat.HeightOneSpectrum.natGenerator v) := by
    funext v
    simp only [lFactor, kronChi, Real.rpow_neg_one, div_eq_mul_inv]
    rw [← normP_rat]
  unfold IsEulerProductValueNF
  rw [e]
  refine h.congr fun X => ?_
  rw [← Finset.prod_inv_distrib]
  exact (congrFun (eulerPartialProdNF_rat fun p : ℕ => (1 - kronR D p / p)⁻¹) X).symm

/-- **`NaturalOrderEulerOne` over $\mathbb Q$ for a character that is $\chi_D$ off a finite set.** -/
theorem naturalOrderEulerOne_of_almost_kron {χ : HeightOneSpectrum (𝓞 ℚ) → ℝ} (hχ : ∀ v, |χ v| ≤ 1)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS : ∀ v ∉ S, χ v = kronChi D v) :
    NaturalOrderEulerOne χ ∧ HasLOne χ (LOne χ) := by
  have hL := (hasLOne_kronChi (D := D)).congr_finite hχ (fun v => abs_kronChi_le v) S hS
  set r : HeightOneSpectrum (𝓞 ℚ) → ℝ := fun v => lFactor χ 1 v / lFactor (kronChi D) 1 v with hr
  have h3 : HasProd r (∏ v ∈ S, r v) := hasProd_prod_of_ne_finset_one fun v hv => by
    simp only [hr, lFactor, hS v hv]
    exact div_self (lFactor_pos_of_one_le (fun v => abs_kronChi_le v) le_rfl v).ne'
  have h4 := (hasProd_normOrder_iff.mpr (isEulerProductValueNF_kronChi (D := D))).mul h3.normOrder
  have h5 : HasProd (lFactor χ 1) (Binary.LOne D * ∏ v ∈ S, r v) (normOrder ℚ) := by
    refine h4.congr_fun fun v => ?_
    simp only [hr]
    exact mul_div_cancel₀ _ (lFactor_pos_of_one_le (fun v => abs_kronChi_le v) le_rfl v).ne' |>.symm
  have h6 : IsEulerProductValueNF (lFactor χ 1) (LOne χ) := by
    rw [hL.lOne_eq]; exact hasProd_normOrder_iff.mp h5
  exact ⟨(naturalOrderEulerOne_iff χ).mpr h6, by rw [hL.lOne_eq]; exact hL⟩

end Kron

/-! ### 3. The ternary character over $\mathbb Q$ is a Kronecker character off a finite set -/

section CharQ

theorem intEquiv_symm_intCast (n : ℤ) :
    (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm n = (n : 𝓞 ℚ) := by
  simpa using map_intCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm n

/-- A rational integer lies in the prime $\mathfrak p$ iff $p$ divides it. -/
theorem intCast_mem_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℤ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ (Rat.HeightOneSpectrum.natGenerator w : ℤ) ∣ n := by
  rw [← Ideal.mem_span_singleton, Rat.HeightOneSpectrum.span_natGenerator, ← Ideal.comap_symm,
    Ideal.mem_comap, intEquiv_symm_intCast]

theorem charNF_dichotomy {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {δ : 𝓞 F}
    (hδ : δ ∉ v.asIdeal) : Siegel.charNF v δ = 1 ∨ Siegel.charNF v δ = -1 := by
  have hne : IsLocalRing.residue _ (LocalDensity.NF.ι v δ) ≠ 0 := by
    rw [Ne, LocalDensity.DVR.residue_eq_zero_iff_dvd (LocalDensity.NF.irreducible_π v),
      LocalDensity.NF.π_dvd_ι_iff]
    exact hδ
  rw [Siegel.charNF]
  exact quadraticChar_dichotomy hne

/-- **The residue symbol over $\mathcal O_{\mathbb Q}$ is the Legendre symbol:** $(x/\mathfrak p) = \left(\frac{x}{p}\right)$ for
$x \in \mathbb Z$, $p \nmid x$. -/
theorem charNF_intCast_eq_legendreSym (w : HeightOneSpectrum (𝓞 ℚ))
    [Fact (Rat.HeightOneSpectrum.natGenerator w).Prime] {x : ℤ}
    (hx : ¬ (Rat.HeightOneSpectrum.natGenerator w : ℤ) ∣ x) :
    Siegel.charNF w (x : 𝓞 ℚ) = legendreSym (Rat.HeightOneSpectrum.natGenerator w) x := by
  set p := Rat.HeightOneSpectrum.natGenerator w
  have hxz : (x : ZMod p) ≠ 0 := fun h => hx ((ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp h)
  have hxI : (x : 𝓞 ℚ) ∉ w.asIdeal := fun h => hx ((intCast_mem_iff w x).mp h)
  by_cases hsq : IsSquare (x : ZMod p)
  · obtain ⟨y, hy⟩ := hsq
    have h1 : Siegel.charNF w (x : 𝓞 ℚ) = 1 := by
      refine (Binary.Rel.charNF_eq_one_iff w hxI).mpr ⟨(y.val : ℤ), ?_⟩
      have : ((x - (y.val : ℤ) ^ 2 : ℤ) : 𝓞 ℚ) = (x : 𝓞 ℚ) - ((y.val : ℤ) : 𝓞 ℚ) ^ 2 := by push_cast; ring
      rw [← this, intCast_mem_iff, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val, hy]; ring
    rw [h1, (legendreSym.eq_one_iff p hxz).mpr ⟨y, hy⟩]
  · have h1 : Siegel.charNF w (x : 𝓞 ℚ) ≠ 1 := by
      intro h
      obtain ⟨c, hc⟩ := (Binary.Rel.charNF_eq_one_iff w hxI).mp h
      set z : ℤ := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) c
      have hcz : c = (z : 𝓞 ℚ) := by
        rw [← intEquiv_symm_intCast]
        exact ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm_apply_apply c).symm
      rw [hcz] at hc
      have : ((x - z ^ 2 : ℤ) : 𝓞 ℚ) ∈ w.asIdeal := by push_cast; exact hc
      rw [intCast_mem_iff, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      push_cast at this
      exact hsq ⟨z, by linear_combination this⟩
    rw [(legendreSym.eq_neg_one_iff p).mpr hsq]
    exact (charNF_dichotomy w hxI).resolve_left h1

theorem hessian_det_up3 (f : QuadForm ℤ 3) : (up f).hessian.det = ((f.hessian.det : ℤ) : 𝓞 ℚ) := by
  have e : (up f).hessian = f.hessian.map (Int.castRingHom (𝓞 ℚ)) := by
    ext i j; simp [QuadForm.hessian, QuadForm.map]
  rw [e, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rfl

/-- **$\chi_m$ is a Kronecker character off a finite set** ($\mathbb Q$): for $Q$ positive definite ternary over $\mathbb Z$ and $m \ge 1$
there are a fundamental discriminant $D < 0$ and a finite set $S$ of primes with `chiTern (up Q) m v = kronChi D v` for
$v \notin S$ (the square class of $\delta_m = -2\det H\cdot m$ is that of $D$; `exists_isQuadDisc_sq`, the Legendre symbol
`charNF_intCast_eq_legendreSym`, `kronZ_odd_prime`). -/
theorem exists_chiTern_eq_kronChi (Q : QuadForm ℤ 3) (hQ : IntQF.PosDef Q) {m : ℤ} (hm : 1 ≤ m) :
    ∃ (D : ℤ) (_ : IsQuadDisc D) (S : Finset (HeightOneSpectrum (𝓞 ℚ))),
      ∀ v ∉ S, chiTern (up Q) (m : 𝓞 ℚ) v = kronChi D v := by
  have hpd := (isTotallyPosDef_up_iff Q).mpr hQ
  obtain ⟨k0, hk0, hk0eq⟩ := exists_int_of_pos (realEmb_det_hessian_pos hpd)
  rw [hessian_det_up3] at hk0eq
  have hdet : Q.hessian.det = k0 := (Int.cast_injective hk0eq).symm
  set k : ℤ := 2 * k0 * m with hk
  have hk1 : 1 ≤ k := by rw [hk]; have : 0 ≤ k0 * m := by positivity
                         nlinarith
  obtain ⟨D, hD, hneg, u, w, hu, hw, hDuw⟩ := exists_isQuadDisc_sq hk1
  have hδ : deltaTern (up Q) (m : 𝓞 ℚ) = ((-k : ℤ) : 𝓞 ℚ) := by
    unfold deltaTern
    rw [hessian_det_up3, hdet, hk]
    push_cast
    norm_num
  have hN : (2 * k * u * w).natAbs ≠ 0 := by
    refine Int.natAbs_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (by omega)) hu) hw)
  refine ⟨D, hD, (finite_natGenerator_dvd hN).toFinset, fun v hv => ?_⟩
  set p := Rat.HeightOneSpectrum.natGenerator v with hpdef
  have hpp : p.Prime := Rat.HeightOneSpectrum.prime_natGenerator v
  have : Fact p.Prime := ⟨hpp⟩
  have hndiv : ¬ (p : ℤ) ∣ 2 * k * u * w := fun h =>
    hv ((Set.Finite.mem_toFinset _).mpr (Int.natCast_dvd.mp h))
  have h2 : ¬ (p : ℤ) ∣ 2 := fun h => hndiv (Dvd.dvd.mul_right (Dvd.dvd.mul_right
    (Dvd.dvd.mul_right h _) _) _)
  have hkd : ¬ (p : ℤ) ∣ k := fun h => hndiv (Dvd.dvd.mul_right (Dvd.dvd.mul_right
    (Dvd.dvd.mul_left h _) _) _)
  have hud : ¬ (p : ℤ) ∣ u := fun h => hndiv (Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _)
  have hwd : ¬ (p : ℤ) ∣ w := fun h => hndiv (Dvd.dvd.mul_left h _)
  have hp2 : p ≠ 2 := fun h => h2 (by rw [h]; norm_num)
  have hnk : ¬ (p : ℤ) ∣ -k := fun h => hkd (by simpa using h)
  have h2I : (2 : 𝓞 ℚ) ∉ v.asIdeal := by
    have := (intCast_mem_iff v 2).not.mpr h2
    simpa using this
  have hδI : deltaTern (up Q) (m : 𝓞 ℚ) ∉ v.asIdeal := by
    rw [hδ]; exact (intCast_mem_iff v (-k)).not.mpr hnk
  rw [chiTern_eq_charNF_of_not_mem (up Q) (m : 𝓞 ℚ) v h2I hδI, hδ,
    charNF_intCast_eq_legendreSym v hnk]
  have hleg : legendreSym p (-k) = legendreSym p D := by
    have e : D * u ^ 2 = (-k) * w ^ 2 := by linarith
    have hu' : (u : ZMod p) ≠ 0 := fun h => hud ((ZMod.intCast_zmod_eq_zero_iff_dvd u p).mp h)
    have hw' : (w : ZMod p) ≠ 0 := fun h => hwd ((ZMod.intCast_zmod_eq_zero_iff_dvd w p).mp h)
    have := congrArg (legendreSym p) e
    rwa [legendreSym.mul, legendreSym.mul, legendreSym.sq_one' p hu', legendreSym.sq_one' p hw', mul_one,
      mul_one, eq_comm] at this
  rw [kronChi, kronR, kronZ_odd_prime p hp2, hleg]

end CharQ

/-! ### 4. The natural-order Euler product is the regularized one -/

theorem nondegenerate_up {Q : QuadForm ℤ 3} (hQ : IntQF.PosDef Q) : (up Q).Nondegenerate := by
  have hpd := (isTotallyPosDef_up_iff Q).mpr hQ
  have := hpd.nondegenerate
  rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
  exact fun h => this (by rw [h, map_zero])

/-- **The natural-order Euler product exists and is the regularized value** (the regularized value versus Siegel/Hanke's reading
of $\prod_p\beta_p(m)$, over $\mathbb Q$; **unconditional**): for $Q$ positive definite ternary over $\mathbb Z$ and $m \ge 1$,
$$\prod_{p \le X}\beta_p(m) \longrightarrow P_{\mathrm{reg}}(m) = L(1,\chi_m)\prod_p\beta_p(m)\Bigl(1-\frac{\chi_m(p)}{p}\Bigr)
\qquad(X \to \infty).$$
Inputs used: `EulerOne.tendsto_prod_primesBelow` for $\chi_D$ (Mertens-type Euler product at $1$, `eulerProductAtOne`), the
identification of $\chi_m$ with $\chi_D$ off a finite set (`exists_chiTern_eq_kronChi`), and the absolute convergence of
$\prod\beta_p(1-\chi_m(p)/p)$ (`multipliable_localDensity_mul_chiTern`). In particular `NaturalOrderEulerOne (chiTern …)` is a
theorem over $\mathbb Q$. -/
@[kb "siegel1935" "Hauptsatz, n = 3: natural-order Euler product over ℚ [unverified]"]
theorem isEulerProductValue_eulerProductReg3 (Q : QuadForm ℤ 3) (hQ : IntQF.PosDef Q) {m : ℤ} (hm : 1 ≤ m) :
    Siegel.IsEulerProductValue Q m (Siegel.eulerProductReg3 Q m) := by
  obtain ⟨D, hD, S, hS⟩ := exists_chiTern_eq_kronChi Q hQ hm
  have hN := (naturalOrderEulerOne_of_almost_kron (D := D) (fun v => abs_chiTern_le v (up Q) (m : 𝓞 ℚ)) S hS).1
  have hf := (multipliable_localDensity_mul_chiTern (nondegenerate_up hQ)
    (show (m : 𝓞 ℚ) ≠ 0 by exact_mod_cast (by omega : m ≠ 0))).hasProd
  simp only [zpow_one] at hf
  have hreg := hasProd_normOrder_regProd hN (fun v => abs_chiTern_le v (up Q) (m : 𝓞 ℚ)) hf
  have h' := hasProd_normOrder_iff.mp hreg
  have e : (fun v : HeightOneSpectrum (𝓞 ℚ) => NF.localDensity v (up Q) (m : 𝓞 ℚ)) =
      fun v => (fun p : ℕ => LocalDensity.localDensity Q p m) (Rat.HeightOneSpectrum.natGenerator v) := by
    funext v; exact NF.localDensity_rat v Q m
  unfold IsEulerProductValueNF at h'
  unfold Siegel.IsEulerProductValue Siegel.eulerProductReg3
  refine h'.congr fun X => ?_
  exact (congrFun (congrArg eulerPartialProdNF e) X).trans
    (congrFun (eulerPartialProdNF_rat fun p : ℕ => LocalDensity.localDensity Q p m) X)

/-! ### 5. The headline: Siegel's formula in rank 3 over $\mathbb Q$, conditional only on $\tau(SO_3) = 2$ -/

section Headline

open QuadFormsKB.Siegel (SiegelFormula3 eulerProductReg3 IsEulerProductValue genusRepAvg aEWith)

/-- **Siegel's formula for ternary forms over $\mathbb Z$ in the natural order of the primes** (Hanke 2004, (5.3) with $n = 3$,
Siegel's convention), conditional only on `TernaryTamagawaTwo ℚ`: for every positive definite ternary $Q$ and $m \ge 1$ the
partial products $\prod_{p \le X}\beta_p(m)$ converge, to the regularized value $P_{\mathrm{reg}}(m)$
(`eulerProductReg3`), and
$$a_E(m) = \beta_\infty(m)\cdot\lim_{X\to\infty}\prod_{p\le X}\beta_p(m).$$
The limit is unique, so the formula holds with *any* $P$ satisfying `IsEulerProductValue Q m P`
(`genusRepAvg_eq_aEWith_of_isEulerProductValue`). -/
@[kb "siegel1935" "Hauptsatz, n = 3, natural-order Euler product (conditional on τ(SO_3) = 2) [unverified]"]
theorem siegelFormula3_natural_rat (hT : TernaryTamagawaTwo ℚ) (Q : QuadForm ℤ 3) (hQ : IntQF.PosDef Q) {m : ℤ}
    (hm : 1 ≤ m) :
    ∃ P : ℝ, IsEulerProductValue Q m P ∧ genusRepAvg Q m = aEWith Q m P :=
  ⟨eulerProductReg3 Q m, isEulerProductValue_eulerProductReg3 Q hQ hm,
    (siegelFormula3_rat hT Q hQ).genusRepAvg_eq m hm⟩

/-- **Siegel's formula with any natural-order value** (conditional on `TernaryTamagawaTwo ℚ`). -/
theorem genusRepAvg_eq_aEWith_of_isEulerProductValue (hT : TernaryTamagawaTwo ℚ) (Q : QuadForm ℤ 3)
    (hQ : IntQF.PosDef Q) {m : ℤ} (hm : 1 ≤ m) {P : ℝ} (hP : IsEulerProductValue Q m P) :
    genusRepAvg Q m = aEWith Q m P := by
  have h := isEulerProductValue_eulerProductReg3 Q hQ hm
  rw [(siegelFormula3_rat hT Q hQ).genusRepAvg_eq m hm, hP.unique h]

/-- **The conjunction of the two ingredients of the headline:** Hanke's `SiegelFormula3` with $P = P_{\mathrm{reg}}$ and the
natural-order identification at every $m \ge 1$. This is the form that the rank-3 corollaries consume. -/
theorem siegelFormula3_and_natural_rat (hT : TernaryTamagawaTwo ℚ) (Q : QuadForm ℤ 3) (hQ : IntQF.PosDef Q) :
    SiegelFormula3 Q (eulerProductReg3 Q) ∧ ∀ m : ℤ, 1 ≤ m → IsEulerProductValue Q m (eulerProductReg3 Q m) :=
  ⟨siegelFormula3_rat hT Q hQ, fun _ hm => isEulerProductValue_eulerProductReg3 Q hQ hm⟩

/-! #### Hanke's rank-3 corollaries, discharged -/

open QuadFormsKB.Siegel in
open Classical in
/-- **Theorem 5.4** (Hanke 2004, p. 369) for the genus average, $n = 3$, **conditional only on `TernaryTamagawaTwo ℚ`**
(`thm_5_4_genus3` with $P = P_{\mathrm{reg}}$; the Siegel formula and the natural-order hypotheses are discharged). -/
@[kb "hanke2004" "Thm 5.4, p. 369"]
theorem thm_5_4_genus3_rat (hT : TernaryTamagawaTwo ℚ) (Q : QuadForm ℤ 3) (hQ : IntQF.PosDef Q)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin 3)) {T : ℤ} (hT0 : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T) (ν : ℕ → ℕ) :
    genusRepAvg Q (T * sqPart S ν ^ 2) = genusRepAvg Q T *
      (∏ p ∈ S.filter (IsIsotropicPrime Q),
        (localConstC Q p T + (1 - localConstC Q p T) / (p : ℝ) ^ ((3 - 2) * ν p))) *
      (∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p) ^ (3 - 2) :=
  thm_5_4_genus3 Q (siegelFormula3_rat hT Q hQ) (IntQF.PosDef.nondegenerate hQ) le_rfl hS S₀ hT0 hst ν
    (isEulerProductValue_eulerProductReg3 Q hQ (by omega))
    (isEulerProductValue_eulerProductReg3 Q hQ (by have := one_le_mul_sqPart hS ν hT0; omega))

open QuadFormsKB.Siegel in
open Classical in
/-- **Theorem 5.7(a), first part** (Hanke 2004, p. 372) for the genus average, $n = 3$, conditional only on
`TernaryTamagawaTwo ℚ` (`thm_5_7_a_genus` discharged). -/
@[kb "hanke2004" "Thm 5.7(a), p. 372 (first part)"]
theorem thm_5_7_a_genus_rat (hT : TernaryTamagawaTwo ℚ) (Q : IntQF 3) (hQ : IntQF.PosDef Q)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin 3)) {T : ℤ}
    (hT0 : 0 < T) (hst : ∀ p ∈ S, IsPStable Q S₀ p T)
    (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ → ℕ) :
    genusRepAvg Q T *
        (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T) *
        ∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p ≤
      genusRepAvg Q (T * sqPart S ν ^ 2) :=
  thm_5_7_a_genus Q (siegelFormula3_rat hT Q hQ) hQ hS S₀ hT0 hst hT2 ν
    (isEulerProductValue_eulerProductReg3 Q hQ (by omega))
    (isEulerProductValue_eulerProductReg3 Q hQ (by have := one_le_mul_sqPart hS ν hT0; omega))

open QuadFormsKB.Siegel in
open Classical in
/-- **Theorem 5.7(a), first part, in $\mathbb N$** (square-class form), conditional only on `TernaryTamagawaTwo ℚ`
(`thm_5_7_a_genus_nat` discharged). -/
@[kb "hanke2004" "Thm 5.7(a), p. 372 (first part)"]
theorem thm_5_7_a_genus_nat_rat (hT : TernaryTamagawaTwo ℚ) (Q : IntQF 3) (hQ : IntQF.PosDef Q)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin 3))
    {T : ℕ} (hT0 : 0 < T) (hst : ∀ p ∈ S, IsPStable Q S₀ p T)
    (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T) (ν : ℕ → ℕ) {m : ℕ}
    (hm : m = T * (∏ p ∈ S, p ^ ν p) ^ 2) :
    genusRepAvg Q T *
        (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T) *
        ∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p ≤ genusRepAvg Q m := by
  have hm0 : 0 < m := by
    rw [hm]; exact Nat.mul_pos hT0 (pow_pos (Finset.prod_pos fun p hp => pow_pos (hS p hp).pos _) 2)
  exact thm_5_7_a_genus_nat Q hQ (siegelFormula3_rat hT Q hQ) hS S₀ hT0 hst hT2 ν hm
    (isEulerProductValue_eulerProductReg3 Q hQ (by exact_mod_cast hT0))
    (isEulerProductValue_eulerProductReg3 Q hQ (by exact_mod_cast hm0))

open QuadFormsKB.Siegel in
open Classical in
/-- **Theorem 6.1, first case** (Hanke 2004, p. 380) for positive definite ternary forms over $\mathbb Z$, conditional only on
`TernaryTamagawaTwo ℚ` and the stated analytic hypotheses (`thm_6_1` with Siegel's formula and the natural-order Euler
products discharged; the remaining hypotheses are those of `thm_6_1`: theta decomposition, the cusp bound, `hH`, `hbound`). -/
@[kb "hanke2004" "Thm 6.1, p. 380 (first case)"]
theorem thm_6_1_rat (hT : TernaryTamagawaTwo ℚ) (Q : IntQF 3) (hQ : IntQF.PosDef Q)
    {aH c : ℕ → ℝ} (hTS : ThetaSplit Q aH c) {t : ℕ} {C : ℝ}
    (hCB : CuspBoundSqClass c t (1 / 2) C)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin 3)) {T : ℕ} (hT0 : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T) (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T)
    (ν : ℕ → ℕ) {s : ℕ} (hTts : T = t * s ^ 2)
    {m m₀ : ℕ} (hm : m = T * (∏ p ∈ S, p ^ ν p) ^ 2) (hm₀ : m₀ = s * ∏ p ∈ S, p ^ ν p) {K : ℝ}
    (hpos : 0 < min (genusRepAvg Q T *
        ∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T) K)
    (hH : 0 ≤ aH m ∨
      K * ∏ p ∈ S.filter (IsIsotropicPrime Q), (p : ℝ) ^ ν p ≤ genusRepAvg Q m + aH m)
    (hbound : C * isoPart Q s / min (genusRepAvg Q T *
          ∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
            localConstC' Q p T) K *
        (divCount (anisoPart Q m₀) : ℝ) ^ 2 * √(anisoPart Q m₀ : ℝ) <
      √(isoPart Q m₀ : ℝ) / (divCount (isoPart Q m₀) : ℝ) ^ 2) :
    IntQF.Represents Q m := by
  have hm0 : 0 < m := by
    rw [hm]; exact Nat.mul_pos hT0 (pow_pos (Finset.prod_pos fun p hp => pow_pos (hS p hp).pos _) 2)
  exact thm_6_1 Q hQ (siegelFormula3_rat hT Q hQ) hTS hCB hS S₀ hT0 hst hT2 ν hTts hm hm₀
    (isEulerProductValue_eulerProductReg3 Q hQ (by exact_mod_cast hT0))
    (isEulerProductValue_eulerProductReg3 Q hQ (by exact_mod_cast hm0)) hpos hH hbound

open QuadFormsKB.Siegel in
open Classical in
/-- **Theorem 6.2** (Hanke 2004, p. 381) for positive definite ternary forms over $\mathbb Z$, conditional only on
`TernaryTamagawaTwo ℚ` and the stated analytic hypotheses (`thm_6_2` with Siegel's formula and the natural-order Euler
products discharged; remaining hypotheses: theta decomposition, uniform cusp bound, `hglob`, `hbound`). -/
@[kb "hanke2004" "Thm 6.2, p. 381"]
theorem thm_6_2_rat (hT : TernaryTamagawaTwo ℚ) (Q : IntQF 3) (hQ : IntQF.PosDef Q)
    {aH c : ℕ → ℝ} (hTS : ThetaSplit Q aH c) {B η ε ε' : ℝ}
    (hCB : CuspBoundUniform c (1 / 2) (1 / 2 - η + ε') B)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (S₀ : Finset (Fin 3)) {T : ℕ} (hT0 : 0 < T)
    (hst : ∀ p ∈ S, IsPStable Q S₀ p T) (hT2 : ∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T)
    (ν : ℕ → ℕ) {t s : ℕ} (ht : Squarefree t) (hTts : T = t * s ^ 2)
    (hspin : ¬ IsSpinorSquareClass aH t) {Λ : ℝ} (hΛ : 0 < Λ)
    (hglob : Λ * (t : ℝ) ^ (1 / 2 - ε) * isoPart Q s ≤ genusRepAvg Q T *
        ∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T)
    {m m₀ : ℕ} (hm : m = T * (∏ p ∈ S, p ^ ν p) ^ 2) (hm₀ : m₀ = s * ∏ p ∈ S, p ^ ν p)
    (hbound : B / Λ * (divCount (anisoPart Q m₀) : ℝ) ^ 2 * √(anisoPart Q m₀ : ℝ) <
      (t : ℝ) ^ (η - (ε + ε')) * √(isoPart Q m₀ : ℝ) / (divCount (isoPart Q m₀) : ℝ) ^ 2) :
    IntQF.Represents Q m := by
  have hm0 : 0 < m := by
    rw [hm]; exact Nat.mul_pos hT0 (pow_pos (Finset.prod_pos fun p hp => pow_pos (hS p hp).pos _) 2)
  exact thm_6_2 Q hQ (siegelFormula3_rat hT Q hQ) hTS hCB hS S₀ hT0 hst hT2 ν ht hTts hspin hΛ hglob hm hm₀
    (isEulerProductValue_eulerProductReg3 Q hQ (by exact_mod_cast hT0))
    (isEulerProductValue_eulerProductReg3 Q hQ (by exact_mod_cast hm0)) hbound

/-! #### Gauss: sums of three squares -/

open QuadFormsKB.Siegel in
/-- **Gauss's $r_3$, Siegel's formula for $x^2+y^2+z^2$** (class number one, `genusClasses_sumSq`), conditional only on
`TernaryTamagawaTwo ℚ`: for $m \ge 1$,
$$r_3(m) = \#\{(x,y,z) \in \mathbb Z^3 : x^2+y^2+z^2 = m\} = \beta_\infty(m)\cdot P_{\mathrm{reg}}(m),\qquad
P_{\mathrm{reg}}(m) = \lim_{X\to\infty}\prod_{p \le X}\beta_p(m),$$
$\beta_\infty$ = `betaInf` (for $I_3$: $\frac{3\omega_3}{2}\sqrt m = 2\pi\sqrt m$, not evaluated here). -/
@[kb "siegel1935" "Hauptsatz for x²+y²+z² (Gauss's r_3), conditional on τ(SO_3) = 2 [unverified]"]
theorem repNum_sumSq_three_rat (hT : TernaryTamagawaTwo ℚ) {m : ℤ} (hm : 1 ≤ m) :
    ∃ P : ℝ, IsEulerProductValue (sumSq 3) m P ∧ (repNum (sumSq 3) m : ℝ) = betaInf (sumSq 3) m * P := by
  obtain ⟨P, hP, h⟩ := siegelFormula3_natural_rat hT (sumSq 3) posDef_sumSq hm
  refine ⟨P, hP, ?_⟩
  rw [← genusRepAvg_of_classNumber_one posDef_sumSq (genusClasses_sumSq (by norm_num)) m, h]
  rfl

end Headline

end QuadFormsKB.Tamagawa.RatHeadline3
