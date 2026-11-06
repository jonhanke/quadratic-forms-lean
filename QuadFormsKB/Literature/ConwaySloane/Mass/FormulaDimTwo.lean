/-
# Conway–Sloane, formula (2) in dimension $n = 2$

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §4, formula (2), p. 263: for a positive definite integral form $f$ of dimension $n \ge 2$,
$$m(f) = 2\,\pi^{-n(n+1)/4}\prod_{j=1}^n\Gamma(j/2)\prod_p 2\,m_p(f),$$
"where $p$ runs through all primes $2, 3, \dots$". `Density.lean` proves it for $n \ge 3$ (`mass_formula_two`), where the
product converges absolutely. For $n = 2$ the product converges only conditionally: at the primes $p \nmid 2\det f$,
$2m_p(f) = (1 - \chi(p)/p)^{-1}$ with $\chi$ the quadratic character of $\mathbb Q(\sqrt{-\det f})$ (Conway–Sloane (6),
$n = 2$, $s = 1$), so $\prod_p 2m_p(f)$ is an Euler product of $L(1,\chi)$ at the edge of absolute convergence.

**The two readings of the product, both proved (unconditional).**
* **Regularized** (the library's regularization convention, `RegProd.regProd`): `regTwoPMass A`
  $= L(1,\chi_f)\cdot\prod_p 2m_p(f)\,(1-\chi_f(p)/p)$, the last product absolutely convergent (all but finitely many factors
  are $1$), $\chi_f$ = `chiP · up f` (the character of the library's regularized binary mass formula).
* **Natural order, as printed** ("$p$ runs through all primes $2, 3, \dots$"): the partial products
  $\prod_{p \le X} 2m_p(f)$ converge, as $X \to \infty$, to `regTwoPMass A` (third conjunct of `mass_formula_two_dimTwo`).

**Proves.**
* **`mass_formula_two_dimTwo`**: $m(f) = 2\pi^{-3/2}\Gamma(\tfrac12)\Gamma(1)\cdot$ `regTwoPMass A`, with `regTwoPMass A` $> 0$ and
  equal to the natural-order limit;
* **`mass_formula_two_dimTwo_natural`**: the statement exactly as printed, read in the natural order of the primes:
  $2\pi^{-3/2}\Gamma(\tfrac12)\Gamma(1)\prod_{p\le X}2m_p(f) \to m(f)$.

**Proof.** The library's regularized binary mass formula over $\mathbb Q$: $\tau^{\mathrm{reg}}(SO_2) = 2$
(`BinaryTauRat.binaryTamagawaTwoReg_rat`, unconditional, derived from Siegel's binary formula) and `tauSOReg_eq` give
$\mu^{\mathrm{reg}}_{\mathrm{Tam}}(K_{SO})\cdot\mathrm{Mass} = 1$, i.e.
$$\mathrm{Mass} = \Bigl(\mathrm{vol}(SO_2(\mathbb R))\cdot L(1,\chi_f)^{-1}\prod_p\alpha'_p(f)\,(1-\chi_f(p)/p)^{-1}\Bigr)^{-1},$$
$\mathrm{vol}(SO_2(\mathbb R)) = \frac{\pi}{4}(\det f)^{-3/2}$ (`archVolSO`), $\alpha'_p$ = `NF.siegelDensity` (Kitaoka's normalization of
the local density). The bridge of `Density.lean` gives $\alpha'_p = \alpha_p(f)/(2|2|_p)$ (`localBeta_ofMatrixZ`,
`Hanke2005.hankeBeta_gramV`), hence
$2m_p(f)(1-\chi_f(p)/p) = p^{3s_p/2}\cdot|2|_p^{-1}\cdot[\alpha'_p(1-\chi_f(p)/p)^{-1}]^{-1}$, $p^{s_p} \,\|\, \det f$; the three products
are $(\det f)^{3/2}$ (`hasProd_pow_det`), $2$ (the product formula, `Hanke2005.tprod_norm_two`) and the inverse of the
corrected product of the $\alpha'_p$ (all but finitely many factors are $1$). The natural order is `RegProd.hasProd_normOrder_regProd` with `NaturalOrderEulerOne χ_f`, a
theorem over $\mathbb Q$ ($\chi_f$ is a Kronecker character off a finite set: `BinaryAllRat.chiP_up_eq_kronChi`,
`RatHeadline3.naturalOrderEulerOne_of_almost_kron`).

**Numerical check** ($f = x^2 + y^2$, $A = I_2$, $\det f = 1$): $\alpha_2(f) = 8$ ($N(2^r) = 2^{r+3}$ for $r \ge 3$), so
$2m_2 = \frac14$; for odd $p$, $2m_p = (1-\chi_{-4}(p)/p)^{-1}$, whose product is $L(1,\chi_{-4}) = \pi/4$. Formula (2) gives
$\frac2\pi\cdot\frac14\cdot\frac\pi4 = \frac18 = 1/|\mathrm{Aut}(f)|$, $\mathrm{Aut}(f)$ the dihedral group of order $8$ (improper
automorphs included, as in `Siegel.mass`; the class number is $1$). The partial products at $X = 10^6$ give $0.1250003$.

*Convention note.* Indices are 0-based; `Finset.Icc 1 2` is the paper's $j = 1, 2$.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.Density
import QuadFormsKB.Tamagawa.SiegelBinaryAllRat
import QuadFormsKB.Tamagawa.RatHeadline3

open QuadFormsKB IsDedekindDomain NumberField Filter Matrix Topology

noncomputable section
namespace QuadFormsKB.ConwaySloane.Mass

open Real Hanke2011Structure Tamagawa Tamagawa.RatBridge RegProd LocalDensity Lattices NFEuler HilbertModular

/-- **The regularized product $\prod_p 2\,m_p(f)$ in dimension 2** (Conway–Sloane (2), p. 263, $n = 2$; regularization
convention of `RegProd.regProd` with exponent $e = 1$):
$$\texttt{regTwoPMass}\ A = L(1,\chi_f)\cdot\prod_p 2\,m_p(f)\,\Bigl(1-\frac{\chi_f(p)}{p}\Bigr),$$
for the integral symmetric Gram matrix $A$ of $f$; $m_p$ = `pMassDensity`, $\chi_f(p)$ = `chiP` of
$f\otimes\mathcal O_{\mathbb Q}$ (the Legendre symbol of $-\det f$ at $p \nmid 2\det f$, $0$ otherwise), $L(1,\chi_f)$ = `RegProd.LOne`,
the product over the primes $\mathfrak p = (p)$ of $\mathcal O_{\mathbb Q}$ is Mathlib's `tprod`. For positive definite $f$ it is the
limit of $\prod_{p \le X}2m_p(f)$ in the natural order (`mass_formula_two_dimTwo`). -/
@[kb "conwaysloane1988" "§4, (2), p. 263 (n = 2)"]
def regTwoPMass (A : Matrix (Fin 2) (Fin 2) ℤ) : ℝ :=
  regProd (fun v => chiP v (up (ofMatrixZ A))) 1 fun v => 2 * pMassDensity (pv v) A

/-- $2\pi^{-3/2}\Gamma(\tfrac12)\Gamma(1) = 2/\pi$, the constant of (2) for $n = 2$. -/
theorem const_two :
    2 * π ^ (-((2 : ℝ) * (2 + 1) / 4)) * (∏ j ∈ Finset.Icc 1 (2 : ℕ), Gamma ((j : ℝ) / 2)) = 2 / π := by
  have hI : Finset.Icc 1 (2 : ℕ) = {1, 2} := by decide
  rw [hI, Finset.prod_pair (by norm_num)]
  push_cast
  rw [show (2 : ℝ) / 2 = 1 by norm_num, Real.Gamma_one, Real.Gamma_one_half_eq,
    show -((2 : ℝ) * (2 + 1) / 4) = -(1 + 1 / 2) by norm_num, Real.rpow_neg pi_pos.le,
    Real.rpow_add pi_pos, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hs : sqrt π ≠ 0 := (sqrt_pos.mpr pi_pos).ne'
  field_simp

/-- $\mathrm{vol}(SO_2(\mathbb R)) = \frac\pi4\,d^{-3/2}$ (`archVolSO` at $n = 2$). -/
theorem archVolSO_two (d : ℝ) : archVolSO 2 d = π / 4 * d ^ (-((3 : ℝ) / 2)) := by
  unfold archVolSO
  rw [Finset.prod_range_succ, Finset.prod_range_one]
  push_cast
  rw [show ((0 : ℝ) + 1) / 2 = 1 / 2 by norm_num, show ((1 : ℝ) + 1) / 2 = 1 by norm_num, Real.rpow_one,
    Real.Gamma_one, Real.Gamma_one_half_eq, ← Real.sqrt_eq_rpow,
    show -((2 : ℝ) + 1) / 2 = -((3 : ℝ) / 2) by norm_num]
  have hs : sqrt π ≠ 0 := (sqrt_pos.mpr pi_pos).ne'
  norm_num
  field_simp

section Main

variable {A : Matrix (Fin 2) (Fin 2) ℤ}

/-- The form with a positive definite Gram matrix is nondegenerate over $\mathcal O_{\mathbb Q}$. -/
theorem nondegenerate_up_ofMatrixZ (hQ : IntQF.PosDef (ofMatrixZ A)) : (up (ofMatrixZ A)).Nondegenerate := by
  have h := Siegel.det_hessian_pos hQ
  unfold QuadForm.Nondegenerate
  rw [QuadForm.hessian_map', ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero_iff _ (algebraMap ℤ (𝓞 ℚ)).injective_int).mpr h.ne'

/-- **Kitaoka's density in terms of Conway–Sloane's** (binary case): $|2|_p\,\alpha'_p(f) = \tfrac12\alpha_p(f)$, with
$\alpha'_p$ = `NF.siegelDensity` at the place $p$ and $\alpha_p$ = `alphaP`; from `localBeta_ofMatrixZ` ($\beta_p = \tfrac12\alpha_p$)
and `Hanke2005.hankeBeta_gramV` ($\beta_p = |2|_p^{n(n-1)/2}\alpha'_p$, $n = 2$). -/
theorem norm_two_mul_siegelDensity (v : HeightOneSpectrum (𝓞 ℚ)) (hA : A.IsSymm) (hdet : A.det ≠ 0)
    (hnd : (up (ofMatrixZ A)).Nondegenerate) :
    ‖(2 : v.adicCompletion ℚ)‖ * NF.siegelDensity v (up (ofMatrixZ A)) (up (ofMatrixZ A)) =
      (1 / 2 : ℝ) * alphaP (pv v) A := by
  rw [← localBeta_ofMatrixZ v hA hdet]
  have h := Hanke2005.hankeBeta_gramV v (up (ofMatrixZ A)) hnd
  rw [show 2 * (2 - 1) / 2 = 1 from rfl, pow_one] at h
  exact h.symm

/-- **The regularized Tamagawa measure of $K_{SO}$ for $f$** over $\mathbb Q$: `tamagawaKReg` $= \frac\pi4(\det f)^{-3/2}\cdot
L(1,\chi_f)^{-1}\prod_p\alpha'_p(f)(1-\chi_f(p)/p)^{-1}$, $\alpha'_p$ = `NF.siegelDensity` ($|d_{\mathbb Q}| = 1$, one real place,
$\det(H/2) = \det A$). -/
theorem tamagawaKReg_up_ofMatrixZ (hA : A.IsSymm) (hdpos : 0 < A.det) :
    tamagawaKReg (up (ofMatrixZ A)) = π / 4 * (A.det : ℝ) ^ (-((3 : ℝ) / 2)) *
      regProd (fun v => chiP v (up (ofMatrixZ A))) (-1)
        (fun v => NF.siegelDensity v (up (ofMatrixZ A)) (up (ofMatrixZ A))) := by
  have hσ : ∀ σ : ℚ →ₐ[ℚ] ℂ, detGram (up (ofMatrixZ A)) σ = A.det := by
    intro σ
    unfold detGram
    rw [BinaryTauRat.hessian_det_up, hessian_det_ofMatrixZ hA]
    have hd : (0 : ℝ) < A.det := by exact_mod_cast hdpos
    simp [map_div₀, abs_of_pos hd, map_ofNat]
    ring
  have hsub : Subsingleton (ℚ →ₐ[ℚ] ℂ) := ⟨fun a b => AlgHom.ext fun x => by
    rw [show a x = a.toRingHom x from rfl, show b x = b.toRingHom x from rfl, Subsingleton.elim a.toRingHom b.toRingHom]⟩
  unfold tamagawaKReg
  rw [NumberField.discr_rat, Fintype.prod_subsingleton _ (Algebra.ofId ℚ ℂ), hσ, archVolSO_two]
  simp

/-- **Formula (2) for $n = 2$, regularized product, and the natural order** (Conway–Sloane, §4, (2), p. 263, $n = 2$):
for a symmetric positive definite integral Gram matrix $A$ ($2\times2$; the form $f$ = `ofMatrixZ A`),
$$m(f) = 2\,\pi^{-3/2}\,\Gamma(\tfrac12)\,\Gamma(1)\cdot\textstyle\prod^{\mathrm{reg}}_p 2\,m_p(f),$$
where $m(f)$ = `Siegel.mass` (weights $1/|\mathrm{Aut}|$, improper automorphs included) and $\prod^{\mathrm{reg}}_p 2m_p(f)$ =
`regTwoPMass A` $= L(1,\chi_f)\prod_p 2m_p(f)(1-\chi_f(p)/p)$. Moreover `regTwoPMass A` $> 0$, and it is the limit of the
partial products $\prod_{p \le X}2m_p(f)$ over the primes $p \le X$ (`Siegel.primesUpTo X`) as $X \to \infty$: the product
"over all primes $2, 3, \dots$" of the paper converges in this order. Unconditional. -/
@[kb "conwaysloane1988" "§4, (2), p. 263 (n = 2)"]
theorem mass_formula_two_dimTwo (hA : A.IsSymm) (hQ : IntQF.PosDef (ofMatrixZ A)) :
    Siegel.mass (ofMatrixZ A) =
        2 * π ^ (-((2 : ℝ) * (2 + 1) / 4)) * (∏ j ∈ Finset.Icc 1 (2 : ℕ), Gamma ((j : ℝ) / 2)) * regTwoPMass A ∧
      0 < regTwoPMass A ∧
      Tendsto (fun X : ℕ => ∏ p ∈ Siegel.primesUpTo X, 2 * pMassDensity (p : ℕ) A) atTop (𝓝 (regTwoPMass A)) := by
  classical
  set Q := ofMatrixZ A with hQdef
  have hdpos : 0 < A.det := det_pos_of_posDef hA hQ
  have hdne : A.det ≠ 0 := hdpos.ne'
  have hdR : (0 : ℝ) < A.det := by exact_mod_cast hdpos
  have hpd : IsTotallyPosDef (formF (up Q)) := (isTotallyPosDef_up_iff Q).mpr hQ
  have hnd : (up Q).Nondegenerate := nondegenerate_up_ofMatrixZ hQ
  set χ : HeightOneSpectrum (𝓞 ℚ) → ℝ := fun v => chiP v (up Q) with hχ
  have hχle : ∀ v, |χ v| ≤ 1 := fun v => abs_chiP_le (up Q) v
  have hlam : ∀ v, 0 < 1 - χ v / (normP v : ℝ) := fun v => one_sub_div_pos (hχle v) v
  -- the regularized binary mass formula: `tamagawaKReg · Mass = 1`
  have hmK : tamagawaKReg (up Q) * Siegel.mass Q = 1 := by
    have hτ := BinaryTauRat.binaryTamagawaTwoReg_rat.tau_eq_two (up Q) hpd
    have h2 := tauSOReg_eq (up Q) hnd hpd
    rw [mass_rat Q hQ]
    linarith
  have hmpos : 0 < Siegel.mass Q := by
    rw [mass_rat Q hQ]; exact mass_pos hpd _ (HilbertModular.isIntegral_stdLat _)
  -- the corrected Kitaoka densities have finite support
  set g : HeightOneSpectrum (𝓞 ℚ) → ℝ :=
    fun v => NF.siegelDensity v (up Q) (up Q) * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ) with hg
  have hgfin : Function.HasFiniteMulSupport g :=
    hasFiniteMulSupport_siegelDensity_binary_reg hnd ∅ (fun _ _ => rfl)
  have hginv : HasProd (fun v => (g v)⁻¹) (∏ᶠ v, g v)⁻¹ := by
    have hfin' : Function.HasFiniteMulSupport fun v => (g v)⁻¹ := by
      refine Set.Finite.subset hgfin fun v hv => ?_
      simp only [Function.mem_mulSupport] at hv ⊢
      intro h
      exact hv (by rw [h, inv_one])
    have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hfin').hasProd
    rwa [tprod_eq_finprod hfin', finprod_inv_distrib] at this
  -- the product formula for 2
  have hnorm : HasProd (fun v : HeightOneSpectrum (𝓞 ℚ) => ‖(2 : v.adicCompletion ℚ)‖⁻¹) 2 := by
    have hm := multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _)
      (Hanke2005.hasFiniteMulSupport_norm_two (F := ℚ))
    have h := hm.hasProd
    rw [Hanke2005.tprod_norm_two, Module.finrank_self, pow_one] at h
    simpa using h.inv₀ (by norm_num)
  -- the determinant factors
  have hdet := (Equiv.hasProd_iff (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ))).mpr
    (hasProd_pow_det hdpos ((((2 : ℕ) : ℝ) + 1) / 2))
  -- the corrected `2 m_p`
  have hcorr : HasProd (fun v => 2 * pMassDensity (pv v) A * (1 - χ v / (normP v : ℝ)))
      ((A.det : ℝ) ^ ((((2 : ℕ) : ℝ) + 1) / 2) * 2 * (∏ᶠ v, g v)⁻¹) := by
    refine ((hdet.mul hnorm).mul hginv).congr_fun fun v => ?_
    have hk := norm_two_mul_siegelDensity v hA hdne hnd
    rw [← hQdef] at hk
    have hn2 : ‖(2 : v.adicCompletion ℚ)‖ ≠ 0 := by
      rw [norm_ne_zero_iff]; exact two_ne_zero
    have hα : alphaP (pv v) A ≠ 0 := (alphaP_pos (Rat.HeightOneSpectrum.primesEquiv v).2 hA hdne).ne'
    have hσ : NF.siegelDensity v (up Q) (up Q) = (1 / 2 : ℝ) * alphaP (pv v) A / ‖(2 : v.adicCompletion ℚ)‖ := by
      rw [← hk]; field_simp
    have hl := (hlam v).ne'
    simp only [Function.comp, hg, hσ, _root_.zpow_neg_one, pMassDensity]
    have e : ((pv v : ℕ) : ℝ) ^ (((padicValInt (pv v) A.det : ℝ) * (((2 : ℕ) : ℝ) + 1)) / 2) =
        ((pv v : ℕ) : ℝ) ^ ((padicValInt (pv v) A.det : ℝ) * ((((2 : ℕ) : ℝ) + 1) / 2)) := by
      congr 1; ring
    rw [e]
    field_simp
  -- the two regularized products
  have hreg1 : regTwoPMass A = LOne χ * ((A.det : ℝ) ^ ((((2 : ℕ) : ℝ) + 1) / 2) * 2 * (∏ᶠ v, g v)⁻¹) := by
    unfold regTwoPMass regProd
    simp only [zpow_one]
    rw [hcorr.tprod_eq]
  have hreg2 : regProd χ (-1) (fun v => NF.siegelDensity v (up Q) (up Q)) = (LOne χ)⁻¹ * ∏ᶠ v, g v := by
    unfold regProd
    rw [tprod_eq_finprod hgfin, _root_.zpow_neg_one]
  have hK := tamagawaKReg_up_ofMatrixZ hA hdpos
  rw [← hQdef, hreg2] at hK
  have hmass : Siegel.mass Q = 2 / π * regTwoPMass A := by
    have hm := eq_inv_of_mul_eq_one_right hmK
    rw [hm, hK, hreg1, Real.rpow_neg hdR.le]
    have h3 : (((2 : ℕ) : ℝ) + 1) / 2 = (3 : ℝ) / 2 := by norm_num
    rw [h3]
    have hπ : π ≠ 0 := pi_pos.ne'
    simp only [mul_inv, inv_inv]
    ring
  -- the natural order
  have hnat : Tendsto (fun X : ℕ => ∏ p ∈ Siegel.primesUpTo X, 2 * pMassDensity (p : ℕ) A) atTop
      (𝓝 (regTwoPMass A)) := by
    have hf' : BinQF.PosDef' Q := (BinQF.posDef_iff_posDef' _).mp ((Binary.intQF_posDef_iff _).mp hQ)
    obtain ⟨D₀, hD₀, -, k, hk, hD⟩ := BinaryAllRat.exists_fundamental_decomp_of_posDef hf'
    have := hD₀
    obtain ⟨S, hS⟩ := BinaryAllRat.chiP_up_eq_kronChi hf' hD (by exact_mod_cast hk)
    have hN := (RatHeadline3.naturalOrderEulerOne_of_almost_kron (D := D₀) hχle S hS).1
    have h1 := hasProd_normOrder_regProd hN hχle hcorr
    have h2 := hasProd_normOrder_iff.mp h1
    unfold IsEulerProductValueNF at h2
    have h3 := RatHeadline3.eulerPartialProdNF_rat (fun p : ℕ => 2 * pMassDensity p A)
    show Tendsto _ atTop (𝓝 (regProd χ 1 fun v => 2 * pMassDensity (pv v) A))
    convert h2 using 2 with X
    exact (congrFun h3 X).symm
  refine ⟨?_, ?_, hnat⟩
  · rw [const_two]; exact hmass
  · have := hmpos
    rw [hmass] at this
    exact pos_of_mul_pos_right this (by positivity)

/-- **Formula (2) for $n = 2$, exactly as printed, in the natural order of the primes** (Conway–Sloane, §4, (2), p. 263,
"$p$ runs through all primes $2, 3, \dots$"): for a symmetric positive definite integral $2\times2$ Gram matrix $A$,
$$2\,\pi^{-3/2}\,\Gamma(\tfrac12)\,\Gamma(1)\prod_{p\le X}2\,m_p(f) \longrightarrow m(f)\qquad(X\to\infty),$$
$m(f)$ = `Siegel.mass (ofMatrixZ A)`, $m_p$ = `pMassDensity`, the product over the primes $p \le X$ (`Siegel.primesUpTo X`).
No regularization enters the statement. Unconditional (`mass_formula_two_dimTwo`). -/
@[kb "conwaysloane1988" "§4, (2), p. 263 (n = 2)"]
theorem mass_formula_two_dimTwo_natural (hA : A.IsSymm) (hQ : IntQF.PosDef (ofMatrixZ A)) :
    Tendsto (fun X : ℕ => 2 * π ^ (-((2 : ℝ) * (2 + 1) / 4)) * (∏ j ∈ Finset.Icc 1 (2 : ℕ), Gamma ((j : ℝ) / 2)) *
        ∏ p ∈ Siegel.primesUpTo X, 2 * pMassDensity (p : ℕ) A) atTop (𝓝 (Siegel.mass (ofMatrixZ A))) := by
  obtain ⟨hm, -, hnat⟩ := mass_formula_two_dimTwo hA hQ
  rw [hm]
  exact hnat.const_mul _

end Main

end QuadFormsKB.ConwaySloane.Mass
