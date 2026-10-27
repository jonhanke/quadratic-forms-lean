import QuadFormsKB.Siegel.RegProd
import QuadFormsKB.Siegel.NFGlobalLowerBound
import QuadFormsKB.Tamagawa.MassInduction

/-!
# Siegel's formula in rank 3: the regularized statement

**Layer:** forms over $\mathcal O_F$, $F$ a number field (totally real in the intended use), a ternary form $Q_0$ with
Hessian $H$ and $d_Q = \det(H/2)$, the standard lattice $L = \mathcal O_F^3$, and $m \in \mathcal O_F$.

**Why a new statement.** `siegelProduct` takes $\prod_\mathfrak p\beta_\mathfrak p(L,m)$ as Mathlib's unconditional
`tprod`. In rank $3$ the good factors are $\beta_\mathfrak p = 1 + \chi_m(\mathfrak p)/N\mathfrak p$, which are not unconditionally
multipliable, so `tprod` returns its junk value $1$ whenever no $\beta_\mathfrak p$ vanishes (`siegelProduct_of_not_multipliable`),
and `SiegelFormulaAt Q₀ m` is then a false statement. Following the
regularization convention, the rank-3 product is **defined** as the regularized product
$$\prod_\mathfrak p\beta_\mathfrak p(L,m) := L_F(1,\chi_m)\prod_\mathfrak p\beta_\mathfrak p(L,m)\bigl(1-\chi_m(\mathfrak p)N\mathfrak p^{-1}\bigr)$$
(`RegProd.regProd`), whose right-hand product converges absolutely (`multipliable_localDensity_mul_chiTern`).
We use a separate `siegelProduct3` / `SiegelFormulaAt3`; the rank $\ge 4$ objects are unchanged.

**Definitions.**
* `chiTern Q₀ m` $= \chi_m$: $\chi_m(\mathfrak p) = \left(\frac{-2\det H\cdot m}{\mathfrak p}\right)$ for $\mathfrak p \nmid 2\det H$,
  else $0$ (it is `Siegel.psiNF Q₀ m`, Hanke's $\psi_{T'}$; $0$ also at $\mathfrak p \mid m$). Since
  $-2\det H\,m = 16\cdot(-m\,d_Q)$, $\chi_m(\mathfrak p) = \left(\frac{-m\,d_Q}{\mathfrak p}\right)$: the normalizing constant
  is $c = 1$. **Matched against `chiP`:** $\chi_m(\mathfrak p)$ is the character of the quaternary form
  $\langle -m\rangle \perp Q_0$ at every prime (`chiTern_eq_chiP`).
* `siegelProductWith Q₀ m P` $= |d_F|^{-(N-1)/2}\prod_\sigma\beta_\sigma(m)\cdot P$ (`siegelProduct` is the case
  $P = $ `tprod`, `siegelProduct_eq_with`), and `siegelProduct3 Q₀ m` its rank-3 case with $P$ the regularized product.
* `SiegelFormulaAt3 Q₀ m` (**input**): $\mathrm{repMass}(L,m) = \mathrm{Mass}(L)\cdot$ `siegelProduct3 Q₀ m`.

**Results (proved).** `localDensity_mul_one_sub_chiTern` (the good factors: $\beta_\mathfrak p(1-\chi_m(\mathfrak p)/N\mathfrak p) =
1 - N\mathfrak p^{-2}$ at $\mathfrak p \nmid 2\det H$, $m \notin \mathfrak p^2$), `multipliable_localDensity_mul_chiTern` (the corrected
product converges absolutely for $Q_0$ nondegenerate and $m \ne 0$), `abs_chiTern_le`, `chiTern_eq_chiP`,
`siegelProduct_of_not_multipliable` (the junk value of the product).
-/

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open Lattices NFEuler RegProd LocalDensity

variable {F : Type} [Field F] [NumberField F]

local notation "QFof" Q₀ => QuadForm.map (algebraMap (𝓞 F) F) Q₀

/-! ### The character $\chi_m$ -/

/-- **The ternary character $\chi_m$** of $Q_0$ and $m$ (the quadratic character of $E_m = F(\sqrt{-m\,d_Q})$ at the good
primes): $\chi_m(\mathfrak p) = \left(\frac{-2\det H\cdot m}{\mathfrak p}\right) = \left(\frac{-m\,d_Q}{\mathfrak p}\right)$ for
$\mathfrak p \nmid 2\det H$ (the residue symbol is $0$ at $\mathfrak p \mid m$), and $0$ at $\mathfrak p \mid 2\det H$. It is
`Siegel.psiNF Q₀ m` (Hanke 2004, $\psi_{T'}$ of Thm 5.7(a)) and `chiP` of $\langle -m\rangle\perp Q_0$ (`chiTern_eq_chiP`). The
value $0$ at finitely many primes where the true character of $E_m/F$ is $\pm1$ does not affect `regProd` (see there). -/
@[kb "hanke2004" "Thm 5.7(a), p. 372 (ψ_{T'}, n = 3)"]
def chiTern (Q₀ : QuadForm (𝓞 F) 3) (m : 𝓞 F) : HeightOneSpectrum (𝓞 F) → ℝ :=
  Siegel.psiNF Q₀ m

section Char

variable (v : HeightOneSpectrum (𝓞 F))

local notation "𝔽" => IsLocalRing.ResidueField (v.adicCompletionIntegers F)
local notation "res" => IsLocalRing.residue (v.adicCompletionIntegers F)

theorem abs_charNF_le (x : 𝓞 F) : |(Siegel.charNF v x : ℝ)| ≤ 1 := by
  unfold Siegel.charNF
  by_cases h : res (NF.ι v x) = 0
  · rw [h, quadraticChar_zero]; simp
  · rcases quadraticChar_dichotomy h with h' | h' <;> rw [h'] <;> simp

theorem abs_chiTern_le (Q₀ : QuadForm (𝓞 F) 3) (m : 𝓞 F) : |chiTern Q₀ m v| ≤ 1 := by
  unfold chiTern Siegel.psiNF
  split_ifs
  · exact abs_charNF_le v _
  · simp

theorem charNF_eq_zero_of_mem {x : 𝓞 F} (hx : x ∈ v.asIdeal) : Siegel.charNF v x = 0 := by
  rw [Siegel.charNF, quadraticChar_eq_zero_iff, DVR.residue_eq_zero_iff_dvd (NF.irreducible_π v),
    NF.π_dvd_ι_iff]
  exact hx

theorem res_two_ne_zero (h2 : (2 : 𝓞 F) ∉ v.asIdeal) : (2 : 𝔽) ≠ 0 := by
  intro h
  have h' : res (2 : v.adicCompletionIntegers F) = 0 := by rw [map_ofNat]; exact h
  exact Siegel.not_π_dvd_two h2 ((DVR.residue_eq_zero_iff_dvd (NF.irreducible_π v) _).1 h')

/-- $\chi(a\,y^{-2}) = \chi(a)$ for the quadratic character of a finite field and $y \ne 0$. -/
theorem quadraticChar_mul_inv_sq {K : Type*} [Field K] [Fintype K] [DecidableEq K] {y : K} (hy : y ≠ 0)
    (a : K) : quadraticChar K (a * (y ^ 2)⁻¹) = quadraticChar K a := by
  rw [← inv_pow, map_mul, quadraticChar_sq_one' (inv_ne_zero hy), mul_one]

/-- **The normalizing constant $c$ is $1$** (the character of DVR.`chiDiscT` at a good prime): Hanke's
$\chi((-1)^{(n-1)/2}D_QT)$ for $n = 3$ at $\mathfrak p \nmid 2$ is the residue symbol of $-2\det H\cdot T$. -/
theorem chiDiscT_Qp_eq_charNF (Q₀ : QuadForm (𝓞 F) 3) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (T : 𝓞 F) :
    DVR.chiDiscT (NF.Qp v Q₀) (NF.ι v T) = Siegel.charNF v ((-1) ^ ((3 - 1) / 2) * (2 * Q₀.hessian.det) * T) := by
  have h2' := res_two_ne_zero v h2
  rw [DVR.chiDiscT, DVR.resGramDet, NF.det_hessian_Qp, Siegel.charNF]
  have e : (-1) ^ ((3 - 1) / 2) * (res (NF.ι v Q₀.hessian.det) / 2 ^ 3) * res (NF.ι v T) =
      res (NF.ι v ((-1) ^ ((3 - 1) / 2) * (2 * Q₀.hessian.det) * T)) * (((2 : 𝔽) ^ 2) ^ 2)⁻¹ := by
    simp only [map_mul, map_pow, map_neg, map_one, map_ofNat]
    field_simp
  rw [e, quadraticChar_mul_inv_sq (pow_ne_zero 2 h2')]

/-- **$\chi_m$ is the character of $\langle -m\rangle \perp Q_0$** at every prime: `chiP` of the quaternary split form
$\langle -m\rangle\perp Q_0$ (discriminant $(-1)^2\det(H_4/2) = -m\,d_Q$) equals $\chi_m(\mathfrak p)$, including the primes
where both vanish ($\mathfrak p \mid 2\,m\det H$). -/
theorem chiTern_eq_chiP (Q₀ : QuadForm (𝓞 F) 3) (m : 𝓞 F) :
    chiTern Q₀ m v = chiP v (splitForm (-m) Q₀) := by
  classical
  have hdet4 : (splitForm (-m) Q₀).hessian.det = 2 * (-m) * Q₀.hessian.det := det_hessian_splitForm _ _
  unfold chiTern Siegel.psiNF chiP
  by_cases hG : Siegel.IsGoodPrimeNF Q₀ v
  · rw [if_pos hG]
    by_cases hm : m ∈ v.asIdeal
    · have h4 : (splitForm (-m) Q₀).hessian.det ∈ v.asIdeal := by
        rw [hdet4]; exact v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_left _ (v.asIdeal.neg_mem_iff.2 hm))
      rw [if_pos (Or.inr h4), charNF_eq_zero_of_mem v (v.asIdeal.mul_mem_left _ hm)]
      simp
    · have h4 : (splitForm (-m) Q₀).hessian.det ∉ v.asIdeal := by
        rw [hdet4]
        intro h
        rcases v.isPrime.mem_or_mem h with h | h
        · rcases v.isPrime.mem_or_mem h with h | h
          · exact hG.1 h
          · exact hm (v.asIdeal.neg_mem_iff.1 h)
        · exact hG.2 h
      rw [if_neg (not_or.2 ⟨hG.1, h4⟩)]
      have h2' := res_two_ne_zero v hG.1
      congr 2
      rw [DVR.chiDisc, DVR.resGramDet, NF.det_hessian_Qp, hdet4, Siegel.charNF]
      have e : (-1) ^ ((3 + 1) / 2) * (res (NF.ι v (2 * -m * Q₀.hessian.det)) / 2 ^ (3 + 1)) =
          res (NF.ι v ((-1) ^ ((3 - 1) / 2) * (2 * Q₀.hessian.det) * m)) * (((2 : 𝔽) ^ 2) ^ 2)⁻¹ := by
        simp only [map_mul, map_pow, map_neg, map_one, map_ofNat]
        field_simp
        ring
      rw [e, quadraticChar_mul_inv_sq (pow_ne_zero 2 h2')]
  · rw [if_neg hG]
    have h : (2 : 𝓞 F) ∈ v.asIdeal ∨ (splitForm (-m) Q₀).hessian.det ∈ v.asIdeal := by
      by_cases h2 : (2 : 𝓞 F) ∈ v.asIdeal
      · exact Or.inl h2
      · have hd : Q₀.hessian.det ∈ v.asIdeal := by
          by_contra hd; exact hG ⟨h2, hd⟩
        exact Or.inr (by rw [hdet4]; exact v.asIdeal.mul_mem_left _ hd)
    rw [if_pos h]

end Char

/-! ### The good factors -/

/-- **The corrected good factor** (rank $3$): at $\mathfrak p \nmid 2\det H$ with $m \notin \mathfrak p^2$,
$$\beta_\mathfrak p(L,m)\,\bigl(1-\chi_m(\mathfrak p)N\mathfrak p^{-1}\bigr) = 1 - N\mathfrak p^{-2}.$$
($\mathfrak p \nmid m$: $\beta_\mathfrak p = 1 + \chi_m(\mathfrak p)/N\mathfrak p$ with $\chi_m(\mathfrak p) = \pm1$; $\mathfrak p \parallel m$:
$\beta_\mathfrak p = 1 - N\mathfrak p^{-2}$ and $\chi_m(\mathfrak p) = 0$.) No shape hypothesis is needed (the DVR reduction
`DVR.localDensity_odd_unit_of_unimodular`). -/
@[kb "siegel1935" "local densities at good primes, n = 3 [unverified]"]
theorem localDensity_mul_one_sub_chiTern (Q₀ : QuadForm (𝓞 F) 3) (m : 𝓞 F) (v : HeightOneSpectrum (𝓞 F))
    (hG : Siegel.IsGoodPrimeNF Q₀ v) (hm2 : m ∉ v.asIdeal ^ 2) :
    NF.localDensity v Q₀ m * (1 - chiTern Q₀ m v / (normP v : ℝ)) = 1 - 1 / (normP v : ℝ) ^ 2 := by
  have h2 := Siegel.not_π_dvd_two hG.1
  have hdet : ¬ NF.π v ∣ (NF.Qp v Q₀).hessian.det := by
    rw [NF.det_hessian_Qp, NF.π_dvd_ι_iff]; exact hG.2
  have hN : (2 : ℝ) ≤ (normP v : ℝ) := by exact_mod_cast two_le_normP v
  have hN0 : (normP v : ℝ) ≠ 0 := by linarith
  rw [NF.localDensity_eq_completion]
  by_cases hm : m ∈ v.asIdeal
  · have hπm : NF.π v ∣ NF.ι v m := (NF.π_dvd_ι_iff v m).2 hm
    have hπm2 : ¬ NF.π v ^ 2 ∣ NF.ι v m := by rw [NF.π_pow_dvd_ι_iff]; exact hm2
    rw [DVR.localDensity_odd_ord_one_of_unimodular _ _ (NF.irreducible_π v) h2 hdet (by decide) _ hπm hπm2,
      NF.q_completion]
    have h0 : chiTern Q₀ m v = 0 := by
      unfold chiTern Siegel.psiNF
      rw [if_pos hG, charNF_eq_zero_of_mem v (v.asIdeal.mul_mem_left _ hm)]
      simp
    rw [h0]
    simp
  · have hπm : ¬ NF.π v ∣ NF.ι v m := by rw [NF.π_dvd_ι_iff]; exact hm
    rw [DVR.localDensity_odd_unit_of_unimodular _ _ (NF.irreducible_π v) h2 hdet (by decide) _ hπm,
      NF.q_completion, chiDiscT_Qp_eq_charNF v Q₀ hG.1 m]
    have hnot : (-1) ^ ((3 - 1) / 2) * (2 * Q₀.hessian.det) * m ∉ v.asIdeal := by
      intro h
      rcases v.isPrime.mem_or_mem h with h | h
      · rcases v.isPrime.mem_or_mem h with h | h
        · exact v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (isUnit_neg_one.pow _))
        · rcases v.isPrime.mem_or_mem h with h | h
          · exact hG.1 h
          · exact hG.2 h
      · exact hm h
    have hχ := Siegel.quadraticChar_res_eq v
      (z := NF.ι v ((-1) ^ ((3 - 1) / 2) * (2 * Q₀.hessian.det) * m)) (by rw [NF.π_dvd_ι_iff]; exact hnot)
    have hc : chiTern Q₀ m v = (Siegel.charNF v ((-1) ^ ((3 - 1) / 2) * (2 * Q₀.hessian.det) * m) : ℝ) := by
      unfold chiTern Siegel.psiNF; rw [if_pos hG]
    rw [hc]
    simp only [Siegel.charNF] at *
    rcases hχ with h | h <;> rw [h] <;> push_cast <;> field_simp <;> ring

theorem two_mul_det_mul_ne_zero' {Q₀ : QuadForm (𝓞 F) 3} (hQ : Q₀.Nondegenerate) {m : 𝓞 F} (hm : m ≠ 0) :
    2 * Q₀.hessian.det * m ≠ 0 :=
  mul_ne_zero (mul_ne_zero two_ne_zero hQ) hm

/-- **The corrected product converges absolutely** ($Q_0$ nondegenerate, $m \ne 0$):
$\prod_\mathfrak p\beta_\mathfrak p(L,m)(1-\chi_m(\mathfrak p)/N\mathfrak p)$ is unconditionally multipliable, since its factors are
$1 - N\mathfrak p^{-2}$ outside the finitely many $\mathfrak p \mid 2m\det H$. So `siegelProduct3` is the regularized product of an
absolutely convergent product, as intended. -/
theorem multipliable_localDensity_mul_chiTern {Q₀ : QuadForm (𝓞 F) 3} (hQ : Q₀.Nondegenerate) {m : 𝓞 F}
    (hm : m ≠ 0) :
    Multipliable fun v => NF.localDensity v Q₀ m * (1 - chiTern Q₀ m v / (normP v : ℝ)) ^ (1 : ℤ) := by
  refine multipliable_of_abs_sub_one_le _ (C := 1) (σ := 2) (by norm_num) ?_
  filter_upwards [(Siegel.finite_mem_asIdeal (two_mul_det_mul_ne_zero' hQ hm)).eventually_cofinite_notMem]
    with v hv
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_right _ h))
  have hd : Q₀.hessian.det ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_left _ h))
  have hmv : m ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_left _ h)
  have hm2 : m ∉ v.asIdeal ^ 2 := fun h => hmv (Ideal.pow_le_self two_ne_zero h)
  rw [zpow_one, localDensity_mul_one_sub_chiTern Q₀ m v ⟨h2, hd⟩ hm2]
  have hN : (2 : ℝ) ≤ (normP v : ℝ) := by exact_mod_cast two_le_normP v
  rw [show (1 : ℝ) - 1 / (normP v : ℝ) ^ 2 - 1 = -(1 / (normP v : ℝ) ^ 2) by ring, abs_neg,
    abs_of_pos (by positivity), one_mul, Real.rpow_neg (by linarith), Real.rpow_two, one_div]

/-! ### The rank-3 Siegel product and Siegel's formula -/

section Siegel

variable {N : ℕ}

/-- **The local side of Siegel's formula with a given value $P$ of $\prod_\mathfrak p\beta_\mathfrak p$:**
$|d_F|^{-(N-1)/2}\prod_{\sigma : F\to\mathbb C}\beta_\sigma(m)\cdot P$ ($\beta_\sigma$ = `archRepDensity`).
`siegelProduct` is the case $P = $ `tprod` (`siegelProduct_eq_with`), `siegelProduct3` the rank-3 regularized case. -/
def siegelProductWith (Q₀ : QuadForm (𝓞 F) N) (m : 𝓞 F) (P : ℝ) : ℝ :=
  |(discr F : ℝ)| ^ (-((N : ℝ) - 1) / 2) *
    (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity N ‖σ (algebraMap (𝓞 F) F m)‖ (detGram Q₀ σ)) * P

theorem siegelProduct_eq_with (Q₀ : QuadForm (𝓞 F) N) (m : 𝓞 F) :
    siegelProduct Q₀ m = siegelProductWith Q₀ m (∏' v, NF.localDensity v Q₀ m) := rfl

/-- **The junk value of `siegelProduct`.** If $v \mapsto \beta_\mathfrak p(L,m)$ is not unconditionally
multipliable (rank $3$ with no vanishing $\beta_\mathfrak p$), Mathlib's `tprod`
is $1$ and `siegelProduct Q₀ m` silently drops every finite factor. -/
theorem siegelProduct_of_not_multipliable (Q₀ : QuadForm (𝓞 F) N) (m : 𝓞 F)
    (h : ¬ Multipliable fun v => NF.localDensity v Q₀ m) : siegelProduct Q₀ m = siegelProductWith Q₀ m 1 := by
  rw [siegelProduct_eq_with, tprod_eq_one_of_not_multipliable h]

end Siegel

/-- **The rank-3 Siegel product** (regularized):
$$S_3(L,m) = |d_F|^{-1}\prod_{\sigma : F\to\mathbb C}\beta_\sigma(m)\cdot L_F(1,\chi_m)\prod_\mathfrak p\beta_\mathfrak p(L,m)\bigl(1-\chi_m(\mathfrak p)N\mathfrak p^{-1}\bigr),$$
$\beta_\sigma$ = `archRepDensity 3 |σ(m)| (detGram Q₀ σ)`, $\beta_\mathfrak p$ = `NF.localDensity`, $\chi_m$ = `chiTern Q₀ m`, the last two
factors being `regProd (chiTern Q₀ m) 1 β`. The product converges absolutely for $Q_0$ nondegenerate, $m \ne 0$
(`multipliable_localDensity_mul_chiTern`). Over $\mathbb Q$ it is Hanke's (5.3) read in the natural order
(see `isEulerProductValue_eulerProductReg3`). -/
@[kb "siegel1935" "Hauptsatz, n = 3 (local side, regularized) [unverified]"]
def siegelProduct3 (Q₀ : QuadForm (𝓞 F) 3) (m : 𝓞 F) : ℝ :=
  siegelProductWith Q₀ m (regProd (chiTern Q₀ m) 1 fun v => NF.localDensity v Q₀ m)

/-- **Input: Siegel's formula for the number $m$ in rank $3$** (Siegel 1935, Hauptsatz [unverified]; over $F$: Siegel 1937
[unverified]), with the regularized product:
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(m)}{|O(M)|} = \mathrm{Mass}(L)\cdot S_3(L,m),\qquad L = \mathcal O_F^3.$$

Field:
- `repMass_eq`: `repMass QF L m = mass QF L * siegelProduct3 Q₀ m`.

*Independence (hypothesis hygiene):* as for `SiegelFormulaAt`, a statement about the genus average
$\mathrm{repMass}/\mathrm{Mass}$ of representation numbers of the number $m$; homogeneous in the weights $1/|O(M)|$, so it
says nothing about $\mathrm{Mass}(L)$ itself. Siegel's constant in rank $3$ is $\varepsilon = 1$. Over $\mathbb Q$ it is
`Siegel.SiegelFormula3` with $P$ the regularized value (`RatBridge3.siegelFormula3_iff_siegelFormulaAt3`). Planned
proof: Weil's step from rank $2$. -/
@[kb "siegel1935" "Hauptsatz, n = 3 [unverified]"]
structure SiegelFormulaAt3 (Q₀ : QuadForm (𝓞 F) 3) (m : 𝓞 F) : Prop where
  repMass_eq : repMass (QFof Q₀) (stdLat F 3) (algebraMap (𝓞 F) F m) =
    mass (QFof Q₀) (stdLat F 3) * siegelProduct3 Q₀ m

end QuadFormsKB.Tamagawa
