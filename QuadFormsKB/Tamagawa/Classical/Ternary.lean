/-
# Classical special cases over $\mathbb Q$: Gauss's three-squares formula and $x_0^2+x_1^2-x_2^2$

**Layer:** $\mathbb Q$.

For a ternary form $Q$ over $\mathbb Z$, unimodular at the odd primes ($\det H_Q = \pm8$), and squarefree $m$, the regularized
local product for the ternary character is explicit:
$$\texttt{regProd}(\chi,1,\beta) = L(1,\chi)\prod_p\beta_p(m)\Bigl(1-\frac{\chi(p)}p\Bigr)
  = \frac{8}{\pi^2}\,\beta_2(m)\Bigl(1-\frac{\chi_D(2)}2\Bigr)L(1,\chi_D)$$
(`regProd_eval`: at every odd $p$, $\beta_p(m)(1-\chi(p)/p) = 1-p^{-2}$, `localDensity_mul_one_sub_chiTern`; at $2$,
$\chi(2) = 0$; $L(1,\chi) = L(1,\chi_D)(1-\chi_D(2)/2)$, `lOne_chiTern_eq`; $\prod_{p>2}(1-p^{-2}) = 8/\pi^2$).

**Proves**
* (1a) **Gauss's three-squares formula** (definite route: `repNum_sumSq_three_rat_uncond`):
  `repNum_sumSq_three_LOne`, `gauss_three_squares`;
* (1b) **Siegel's formula for $x_0^2+x_1^2-x_2^2$ and a non-square $m$** with explicit local densities
  (from `siegelIndefinite_ternary_uncond`): `siegel_qInd_nonsquare`, `siegel_qInd_nonsquare_pos`;
* (3) **squares by $x_0^2+x_1^2-x_2^2$** (from `siegelIndefinite_ternary_isotropic_uncond`): `siegel_qInd_squares`.
-/
import QuadFormsKB.Tamagawa.Classical.TernaryReg
import QuadFormsKB.Tamagawa.Classical.TernaryDensities
import QuadFormsKB.Tamagawa.Classical.Helpers
import QuadFormsKB.Tamagawa.Indefinite.Rank2RatChecks

open NumberField IsDedekindDomain Real

namespace QuadFormsKB.Tamagawa.Classical

open QuadFormsKB.Binary QuadFormsKB.Tamagawa.BinaryTauRat QuadFormsKB.Tamagawa.RatHeadline3 RatBridge RegProd
  QuadFormsKB.NFEuler LocalDensity

local notation "natGen" => Rat.HeightOneSpectrum.natGenerator

/-- $(n : \mathcal O_{\mathbb Q})\in\mathfrak p^2 \iff p^2\mid n$. -/
theorem intCast_mem_sq_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℤ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ^ 2 ↔ (natGen w : ℤ) ^ 2 ∣ n := by
  rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow, Rat.HeightOneSpectrum.span_natGenerator,
    ← Ideal.map_pow, ← Ideal.comap_symm, Ideal.mem_comap, intEquiv_symm_intCast]

/-- **The explicit regularized product.** If `chiTern (up Q) m` is $\chi_D$ at the odd primes, $\beta_p(m)(1-\chi(p)/p) =
1-p^{-2}$ at every odd $p$ and $\beta_2(m) = b$, then
$\texttt{regProd}(\chi,1,\beta) = \frac8{\pi^2}\,b\,(1-\chi_D(2)/2)\,L(1,\chi_D)$. -/
theorem regProd_eval (Q : QuadForm ℤ 3) (m : ℤ) {D : ℤ} [IsQuadDisc D] (b : ℝ)
    (hodd : ∀ v, natGen v ≠ 2 → chiTern (up Q) (m : 𝓞 ℚ) v = kronChi D v)
    (hβodd : ∀ v, natGen v ≠ 2 → NF.localDensity v (up Q) (m : 𝓞 ℚ) *
      (1 - chiTern (up Q) (m : 𝓞 ℚ) v / (normP v : ℝ)) = 1 - 1 / (normP v : ℝ) ^ 2)
    (hβ2 : ∀ v, natGen v = 2 → NF.localDensity v (up Q) (m : 𝓞 ℚ) = b) :
    regProd (chiTern (up Q) (m : 𝓞 ℚ)) 1 (fun v => NF.localDensity v (up Q) (m : 𝓞 ℚ)) =
      8 / π ^ 2 * (b * (1 - kronR D 2 / 2)) * Binary.LOne D := by
  obtain ⟨v₂, hv₂⟩ := exists_natGen_eq_two
  have hN : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((normP v : ℕ) : ℝ) = (natGen v : ℝ) := fun v => by
    rw [normP_rat]
  have hg : HasProd (fun v => NF.localDensity v (up Q) (m : 𝓞 ℚ) *
      (1 - chiTern (up Q) (m : 𝓞 ℚ) v / (normP v : ℝ)) ^ (1 : ℤ)) (8 / π ^ 2 * b) := by
    have h1 := hasProd_one_sub_inv_sq_odd
    have h2 : HasProd (fun v : HeightOneSpectrum (𝓞 ℚ) => if natGen v = 2 then b else 1) b := by
      have := hasProd_single (f := fun v : HeightOneSpectrum (𝓞 ℚ) => if natGen v = 2 then b else 1) v₂
        (fun v hv => by
          have : natGen v ≠ 2 := fun h => hv ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
            (Subtype.ext (show natGen v = natGen v₂ by rw [h, hv₂])))
          simp [this])
      simpa [hv₂] using this
    refine (h1.mul h2).congr_fun fun v => ?_
    simp only [zpow_one]
    by_cases hv : natGen v = 2
    · have : v = v₂ := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
        (Subtype.ext (show natGen v = natGen v₂ by rw [hv, hv₂]))
      subst this
      simp [hv, hβ2 _ hv, chiTern_up_two Q m _ hv]
    · have hne : v ≠ v₂ := fun h => hv (h ▸ hv₂)
      simp only [hv, ↓reduceIte, mul_one]
      rw [hβodd v hv, hN]
  rw [regProd, zpow_one, lOne_chiTern_eq Q m (fun v hv => hodd v hv), hg.tprod_eq]
  ring

/-- **The good odd primes of a ternary form with $\det H = \pm 8$ and squarefree $m$**: $\beta_p(m)(1-\chi(p)/p) = 1-p^{-2}$. -/
theorem localDensity_mul_one_sub_chiTern_odd (Q : QuadForm ℤ 3) (hdet : Q.hessian.det = 8 ∨ Q.hessian.det = -8)
    {m : ℤ} (hsf : Squarefree m) (v : HeightOneSpectrum (𝓞 ℚ)) (hp2 : natGen v ≠ 2) :
    NF.localDensity v (up Q) (m : 𝓞 ℚ) * (1 - chiTern (up Q) (m : 𝓞 ℚ) v / (normP v : ℝ)) =
      1 - 1 / (normP v : ℝ) ^ 2 := by
  have hp : (natGen v).Prime := Rat.HeightOneSpectrum.prime_natGenerator v
  have hnot2 : ¬ (natGen v : ℤ) ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (by exact_mod_cast h))
  have h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal := fun h => hnot2 ((intCast_mem_iff v 2).mp (by exact_mod_cast h))
  have hd : (up Q).hessian.det ∉ v.asIdeal := by
    rw [hessian_det_up3]
    intro h
    have h' := (intCast_mem_iff v _).mp h
    have h8 : (natGen v : ℤ) ∣ 2 ^ 3 := by
      rcases hdet with e | e <;> rw [e] at h'
      · simpa using h'
      · simpa using h'
    exact hnot2 (Int.Prime.dvd_pow' (by exact_mod_cast hp) h8)
  have hm2 : (m : 𝓞 ℚ) ∉ v.asIdeal ^ 2 := by
    rw [intCast_mem_sq_iff]
    intro h
    have := hsf (natGen v : ℤ) (by rw [← sq]; exact h)
    exact (Nat.Prime.one_lt hp).ne' (by simpa using Int.isUnit_iff_natAbs_eq.mp this)
  exact localDensity_mul_one_sub_chiTern (up Q) (m : 𝓞 ℚ) v ⟨h2, hd⟩ hm2

/-! ### (1a) Gauss's three-squares formula -/

theorem nfLocalDensity_eq (Q : QuadForm ℤ 3) (m : ℤ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    NF.localDensity v (up Q) (m : 𝓞 ℚ) = LocalDensity.localDensity Q (natGen v) m :=
  NF.localDensity_rat v Q m

/-- **The regularized product for $x_0^2+x_1^2+x_2^2$**, $m$ squarefree, $D$ = `gaussDisc m`:
$P_{\mathrm{reg}}(m) = \frac8{\pi^2}\,c(m)\,L(1,\chi_D)$, $c(m) = 0$ for $m\equiv7\pmod 8$ and $3/2$ otherwise
($c(m) = \beta_2(m)(1-\chi_D(2)/2)$). -/
theorem eulerProductReg3_sumSq {m : ℤ} (hsf : Squarefree m) {D : ℤ} [IsQuadDisc D] (hD : D = gaussDisc m) :
    Siegel.eulerProductReg3 (Siegel.sumSq 3) m = 8 / π ^ 2 * (if m % 8 = 7 then 0 else 3 / 2) * Binary.LOne D := by
  have h4 := not_four_dvd_of_squarefree hsf
  have hreg := regProd_eval (Siegel.sumSq 3) m (D := D) (LocalDensity.localDensity (Siegel.sumSq 3) 2 m)
    (fun v hv => chiTern_sumSq_odd m hD v hv)
    (fun v hv => localDensity_mul_one_sub_chiTern_odd _ (Or.inl hessian_det_sumSq_three) hsf v hv)
    (fun v hv => by rw [nfLocalDensity_eq, hv])
  have hD' : (m % 4 = 3 ∧ D = -m) ∨ (m % 4 ≠ 3 ∧ D = -4 * m) := by
    rw [hD]; unfold gaussDisc; split_ifs with h <;> simp [h]
  rw [Siegel.eulerProductReg3, hreg, localDensity_sumSq_three_two h4, kronR, Nat.cast_ofNat, kronZ_two]
  split_ifs <;> first | omega | (push_cast; ring)

/-- **Gauss's $r_3$ through $L(1,\chi_D)$** (squarefree $m\ge1$, $D$ = `gaussDisc m`):
$r_3(m) = \frac{24}{\pi}\sqrt m\,L(1,\chi_D)$ for $m\not\equiv7\pmod 8$, and $r_3(m) = 0$ for $m\equiv 7\pmod 8$. From the
unconditional `repNum_sumSq_three_rat_uncond` ($r_3(m) = \beta_\infty(m)P_{\mathrm{reg}}(m)$, one class in the genus),
$\beta_\infty(m) = 2\pi\sqrt m$ and `eulerProductReg3_sumSq`. -/
@[kb "gauss1801" "Disquisitiones Arithmeticae, art. 291–292 (three squares) [unverified locator]"]
theorem repNum_sumSq_three_LOne {m : ℤ} (hm : 1 ≤ m) (hsf : Squarefree m) {D : ℤ} [IsQuadDisc D]
    (hD : D = gaussDisc m) :
    (Siegel.repNum (Siegel.sumSq 3) m : ℝ) =
      if m % 8 = 7 then 0 else 24 / π * Real.sqrt m * Binary.LOne D := by
  obtain ⟨P, hP, hr⟩ := repNum_sumSq_three_rat_uncond hm
  have hP' := isEulerProductValue_eulerProductReg3 (Siegel.sumSq 3) Siegel.posDef_sumSq hm
  have hPe : P = Siegel.eulerProductReg3 (Siegel.sumSq 3) m := tendsto_nhds_unique hP hP'
  rw [hr, hPe, eulerProductReg3_sumSq hsf hD, betaInf_sumSq_three (by exact_mod_cast (by omega : (0 : ℤ) ≤ m))]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  split_ifs
  · ring
  · field_simp
    ring

/-- **Gauss's three-squares formula** (Gauss, *Disquisitiones Arithmeticae*, art. 291–292; Grosswald, *Representations
of Integers as Sums of Squares*, Ch. 4 [unverified locator]): for squarefree $m\ge1$, with $D$ = `gaussDisc m` the
discriminant of $\mathbb Q(\sqrt{-m})$, $h(D)$ its class number and $w(D)$ its number of roots of unity,
$r_3(m) = \#\{x\in\mathbb Z^3 : x_0^2+x_1^2+x_2^2 = m\}$ is $24\,h(-4m)/w(-4m)$ for $m\equiv1,2\pmod 4$,
$48\,h(-m)/w(-m)$ for $m\equiv3\pmod 8$, and $0$ for $m\equiv7\pmod 8$.
(E.g. $m = 1$: $24\cdot1/4 = 6$; $m = 3$: $48\cdot1/6 = 8$.) Proof: `repNum_sumSq_three_LOne` and Dirichlet's class number
formula `classNumberFormula_neg`. Unconditional. -/
@[kb "gauss1801" "Disquisitiones Arithmeticae, art. 291–292; grosswald1985 Ch. 4 [unverified locator]"]
theorem gauss_three_squares {m : ℤ} (hm : 1 ≤ m) (hsf : Squarefree m) {D : ℤ} [IsQuadDisc D]
    (hD : D = gaussDisc m) :
    (Siegel.repNum (Siegel.sumSq 3) m : ℝ) =
      (if m % 4 = 1 ∨ m % 4 = 2 then 24 else if m % 8 = 3 then 48 else 0) *
        (classNumber (QField D) : ℝ) / (Units.torsionOrder (QField D) : ℝ) := by
  have hDneg : D < 0 := by rw [hD]; unfold gaussDisc; split_ifs <;> omega
  have hL : Binary.LOne D = 2 * π * classNumber (QField D) /
      (Units.torsionOrder (QField D) * Real.sqrt |(D : ℝ)|) := by
    rw [Binary.LOne, classNumberFormula_neg hDneg, Complex.ofReal_re]
  rw [repNum_sumSq_three_LOne hm hsf hD, hL]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : (0 : ℤ) < m)
  have hsq : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  have hw : (0 : ℝ) < Units.torsionOrder (QField D) := by exact_mod_cast Units.torsionOrder_pos _
  have hπ : 0 < π := Real.pi_pos
  have h4m : Real.sqrt |((-4 * m : ℤ) : ℝ)| = 2 * Real.sqrt m := by
    push_cast
    rw [show |(-4 : ℝ) * m| = 2 ^ 2 * m by rw [abs_mul, abs_of_pos hm0]; norm_num,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have h4 := not_four_dvd_of_squarefree hsf
  rcases (by omega : m % 8 = 7 ∨ m % 8 = 3 ∨ m % 4 = 1 ∨ m % 4 = 2) with h | h | h | h
  · rw [if_pos h, if_neg (by omega), if_neg (by omega)]; ring
  · have hD' : D = -m := by rw [hD]; unfold gaussDisc; rw [if_pos (by omega)]
    have habs : Real.sqrt |(D : ℝ)| = Real.sqrt m := by rw [hD']; push_cast; rw [abs_neg, abs_of_pos hm0]
    rw [if_neg (by omega), if_neg (by omega), if_pos h, habs]
    field_simp
    ring
  · have hD' : D = -4 * m := by rw [hD]; unfold gaussDisc; rw [if_neg (by omega)]
    have habs : Real.sqrt |(D : ℝ)| = 2 * Real.sqrt m := by rw [hD']; exact h4m
    rw [if_neg (by omega), if_pos (Or.inl h), habs]
    field_simp
  · have hD' : D = -4 * m := by rw [hD]; unfold gaussDisc; rw [if_neg (by omega)]
    have habs : Real.sqrt |(D : ℝ)| = 2 * Real.sqrt m := by rw [hD']; exact h4m
    rw [if_neg (by omega), if_pos (Or.inr h), habs]
    field_simp

/-! ### (1b) $x_0^2+x_1^2-x_2^2$, $m$ not a square (`siegelIndefinite_ternary_uncond`) -/

theorem nondegenerate_up_qInd : (up qInd).Nondegenerate := by
  rw [QuadForm.Nondegenerate, hessian_det_up3, hessian_det_qInd]; norm_num

theorem intCast_ne_zero_of_squarefree {m : ℤ} (hsf : Squarefree m) : (((m : 𝓞 ℚ)) : ℚ) ≠ 0 := by
  have : m ≠ 0 := by rintro rfl; exact not_squarefree_zero hsf
  simpa using this

/-- For squarefree $m\ne1$, $-2m\det H = 16m$ is not a square in $\mathbb Q$: the orthogonal complement of a vector of
value $m$ is anisotropic. -/
theorem not_isSquare_qInd {m : ℤ} (hsf : Squarefree m) (hm1 : m ≠ 1) :
    ¬ IsSquare (-(2 * (((m : 𝓞 ℚ)) : ℚ) * algebraMap (𝓞 ℚ) ℚ (up qInd).hessian.det)) := by
  rw [hessian_det_up3, hessian_det_qInd]
  rintro ⟨q, hq⟩
  have h16 : ((m : ℤ) : ℚ) = (q / 4) * (q / 4) := by
    have h8 : (algebraMap (𝓞 ℚ) ℚ) 8 = 8 := map_ofNat _ 8
    have : -(2 * (((m : 𝓞 ℚ)) : ℚ) * algebraMap (𝓞 ℚ) ℚ ((-8 : ℤ) : 𝓞 ℚ)) = 16 * (m : ℚ) := by
      simp [h8]; ring
    rw [this] at hq
    linarith [hq]
  have hsq : IsSquare (m : ℚ) := ⟨q / 4, h16⟩
  rw [Rat.isSquare_intCast_iff] at hsq
  obtain ⟨r, rfl⟩ := hsq
  have hu := hsf r (dvd_refl _)
  rcases Int.isUnit_iff.mp hu with h | h <;> subst h <;> simp at hm1

/-- **The ternary indefinite constant** $c'(m) = \beta_2(m)(1-\chi_D(2)/2)$ for $x_0^2+x_1^2-x_2^2$, $m$ squarefree:
$1$ ($m\equiv1\pmod 8$), $3/2$ ($m\equiv5\pmod 8$), $1/2$ (otherwise). Parameter: `m`. -/
noncomputable def indC (m : ℤ) : ℝ := if m % 8 = 1 then 1 else if m % 8 = 5 then 3 / 2 else 1 / 2

/-- **The regularized local side for $x_0^2+x_1^2-x_2^2$**, $m$ squarefree, $D$ = `realDisc m`:
`ternaryDensityProductReg` $= \frac8{\pi^2}\,c'(m)\,L(1,\chi_D)$. -/
theorem ternaryDensityProductReg_qInd {m : ℤ} (hsf : Squarefree m) {D : ℤ} [IsQuadDisc D] (hD : D = realDisc m) :
    Indefinite.ternaryDensityProductReg (up qInd) (m : 𝓞 ℚ) = 8 / π ^ 2 * indC m * Binary.LOne D := by
  have h4 := not_four_dvd_of_squarefree hsf
  have hreg := regProd_eval qInd m (D := D) (LocalDensity.localDensity qInd 2 m)
    (fun v hv => chiTern_qInd_odd m hD v hv)
    (fun v hv => localDensity_mul_one_sub_chiTern_odd _ (Or.inr hessian_det_qInd) hsf v hv)
    (fun v hv => by rw [nfLocalDensity_eq, hv])
  have hD' : (m % 4 = 1 ∧ D = m) ∨ (m % 4 ≠ 1 ∧ D = 4 * m) := by
    rw [hD]; unfold realDisc; split_ifs with h <;> simp [h]
  rw [Indefinite.ternaryDensityProductReg, Indefinite.chiForms_unary_eq_chiTern, Rat.numberField_discr]
  simp only [Int.cast_one, abs_one, Real.one_rpow, one_mul]
  rw [hreg, localDensity_qInd_two h4, kronR, Nat.cast_ofNat, kronZ_two, indC]
  split_ifs <;> first | omega | (push_cast; ring)

/-- **Siegel's formula for $x_0^2+x_1^2-x_2^2$ and a non-square $m$, with explicit local densities** (Siegel 1936,
*Über die analytische Theorie der quadratischen Formen II*, Hauptsatz for indefinite forms [unverified locator]; see
`siegelIndefinite_ternary_uncond` over $\mathbb Q$): for squarefree $m\ne1$ (of either sign), $D$ = `realDisc m` the
discriminant of $\mathbb Q(\sqrt m)$ and a rational point $\xi$ of $x_0^2+x_1^2-x_2^2 = m$,
$$c_\infty(m)\sum_i\rho(M_i,m) = \frac8{\pi^2}\,c'(m)\,L(1,\chi_D)\sum_iv(M_i),$$
$c'(m)$ = `indC m` $\in\{1, 3/2, 1/2\}$ (by $m\bmod 8$), $\rho$ the measures of representations of the rank-2 frame
fibration
(`frameArchFibrationRank2`), $v(M_i)$ = `unitVolume`. The local factors are $\beta_p(m)(1-\chi_D(p)/p) = 1-p^{-2}$ at every
odd $p$ and $\beta_2(m)\in\{2, 1, 1/2\}$. Unconditional. -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz; x² + y² − z², m not a square, explicit densities [unverified]"]
theorem siegel_qInd_nonsquare {m : ℤ} (hsf : Squarefree m) (hm1 : m ≠ 1) {D : ℤ} [IsQuadDisc D]
    (hD : D = realDisc m) (ξ : Measure.Weil.RatSphere (up qInd) (((m : 𝓞 ℚ)) : ℚ)) :
    Indefinite.cInfNF (k := 2) (((m : 𝓞 ℚ)) : ℚ) *
        ∑' i, Indefinite.repMeasureT (up qInd) (DVR.unary (m : 𝓞 ℚ)) nondegenerate_up_qInd
          (Indefinite.frameArchFibrationRank2 (r := 1) (up qInd) nondegenerate_up_qInd (DVR.unary (m : 𝓞 ℚ))
            (Indefinite.unary_nondegenerate (intCast_ne_zero_of_squarefree hsf))
            (Indefinite.not_isSquare_deltaForms_unary (N := 3) (not_isSquare_qInd hsf hm1))
            ((Indefinite.ratFrameEquivRatSphere (n' := 2) (up qInd) (m : 𝓞 ℚ)).symm ξ)) i =
      ENNReal.ofReal (8 / π ^ 2 * indC m * Binary.LOne D) *
        ∑' i, Indefinite.unitVolume (up qInd) nondegenerate_up_qInd i := by
  rw [← ternaryDensityProductReg_qInd hsf hD]
  exact Indefinite.siegelIndefinite_ternary_uncond (up qInd) nondegenerate_up_qInd
    (intCast_ne_zero_of_squarefree hsf) (not_isSquare_qInd hsf hm1) ξ

/-- **The same, $m\ge2$, with Dirichlet's class number formula** $L(1,\chi_D) = 2h(D)R(D)/\sqrt D$ ($h$ the class number,
$R$ the regulator of $\mathbb Q(\sqrt m)$). -/
theorem siegel_qInd_nonsquare_pos {m : ℤ} (hm : 2 ≤ m) (hsf : Squarefree m) {D : ℤ} [IsQuadDisc D]
    (hD : D = realDisc m) (ξ : Measure.Weil.RatSphere (up qInd) (((m : 𝓞 ℚ)) : ℚ)) :
    Indefinite.cInfNF (k := 2) (((m : 𝓞 ℚ)) : ℚ) *
        ∑' i, Indefinite.repMeasureT (up qInd) (DVR.unary (m : 𝓞 ℚ)) nondegenerate_up_qInd
          (Indefinite.frameArchFibrationRank2 (r := 1) (up qInd) nondegenerate_up_qInd (DVR.unary (m : 𝓞 ℚ))
            (Indefinite.unary_nondegenerate (intCast_ne_zero_of_squarefree hsf))
            (Indefinite.not_isSquare_deltaForms_unary (N := 3) (not_isSquare_qInd hsf (by omega)))
            ((Indefinite.ratFrameEquivRatSphere (n' := 2) (up qInd) (m : 𝓞 ℚ)).symm ξ)) i =
      ENNReal.ofReal (8 / π ^ 2 * indC m *
          (2 * classNumber (QField D) * Units.regulator (QField D) / Real.sqrt D)) *
        ∑' i, Indefinite.unitVolume (up qInd) nondegenerate_up_qInd i := by
  have hDpos : 0 < D := by rw [hD]; unfold realDisc; split_ifs <;> omega
  have hL : Binary.LOne D = 2 * classNumber (QField D) * Units.regulator (QField D) / Real.sqrt D := by
    rw [Binary.LOne, classNumberFormula_pos hDpos, Complex.ofReal_re]
  rw [← hL]
  exact siegel_qInd_nonsquare hsf (by omega) hD ξ

/-! ### (3) Squares by $x_0^2+x_1^2-x_2^2$ (`siegelIndefinite_ternary_isotropic_uncond`) -/

theorem intCast_sq_ne_zero {k : ℤ} (hk : k ≠ 0) : ((((k ^ 2 : ℤ) : 𝓞 ℚ)) : ℚ) ≠ 0 := by
  have : k ^ 2 ≠ 0 := pow_ne_zero 2 hk
  simpa using this

/-- For $m = k^2$, $-2m\det H = 16k^2 = (4k)^2$ is a square: the complement of a representation is isotropic. -/
theorem isSquare_qInd_sq (k : ℤ) :
    IsSquare (-(2 * ((((k ^ 2 : ℤ) : 𝓞 ℚ)) : ℚ) * algebraMap (𝓞 ℚ) ℚ (up qInd).hessian.det)) :=
  ⟨4 * k, by
    have h8 : (algebraMap (𝓞 ℚ) ℚ) 8 = 8 := map_ofNat _ 8
    rw [hessian_det_up3, hessian_det_qInd]; simp [h8]; ring⟩

/-- **The regularized local side for the squares** $k^2$ ($k\ne0$) by $x_0^2+x_1^2-x_2^2$: $\beta_p(k^2) = \beta_p(1)$ at every
$p$ ($1+1/p$ for odd $p$, $2$ for $p = 2$), $\rho_\mathbb Q = 1$, $|d_\mathbb Q| = 1$, so
`ternaryIsoDensityProductReg` $= 2\cdot\frac12\prod_{p>2}(1+p^{-1})(1-p^{-1}) = 8/\pi^2$, independent of $k$. -/
theorem ternaryIsoDensityProductReg_qInd_sq {k : ℤ} (hk : k ≠ 0) :
    Indefinite.ternaryIsoDensityProductReg (up qInd) ((k ^ 2 : ℤ) : 𝓞 ℚ) = 8 / π ^ 2 := by
  rw [Indefinite.ternaryIsoDensityProductReg, Rat.numberField_discr, dedekindZeta_residue_rat]
  simp only [Int.cast_one, abs_one, Real.one_rpow, one_mul]
  rw [← hasProd_one_sub_inv_sq_odd.tprod_eq]
  refine tprod_congr fun v => ?_
  have : Fact (natGen v).Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have hN : (Ideal.absNorm v.asIdeal : ℝ) = natGen v := by exact_mod_cast normP_rat v
  rw [nfLocalDensity_eq, localDensity_qInd_sq _ hk, Measure.Weil.lamV, hN]
  have hp2 : (2 : ℝ) ≤ natGen v := by exact_mod_cast (Rat.HeightOneSpectrum.prime_natGenerator v).two_le
  split_ifs with h
  · rw [h]; norm_num
  · field_simp
    ring

/-- **Siegel's formula for the squares represented by $x_0^2+x_1^2-x_2^2$** (Siegel's excluded case, regularized; see
`siegelIndefinite_ternary_isotropic_uncond` over $\mathbb Q$): for every integer $k\ne0$ and a rational point $\xi$ of
$x_0^2+x_1^2-x_2^2 = k^2$,
$$2\,c_\infty(k^2)\sum_i\rho^1(M_i,k^2) = \frac8{\pi^2}\sum_iv(M_i).$$
The complement of a representation is a hyperbolic plane: the stabilizer of $X = ke_0$ in $SO(V)(\mathbb R)$ is
$1\oplus\begin{psmallmatrix}a&b\\b&a\end{psmallmatrix}$, $a^2-b^2 = 1$ (`stab_e0_qInd_real`), a split torus with eigenvalue
$a+b$ on the isotropic line $\mathbb R(0,1,1)$ (`stab_e0_qInd_eigen`); its norm-one part $|a+b| = 1$ is
$\{1,\mathrm{diag}(1,-1,-1)\}$ (`stab_e0_qInd_normOne`), which is also the integral stabilizer in $SO(\mathbb Z^3)$
(`stab_e0_qInd_int`). $\rho^1$ = `repMeasureIso` measures each representation by the volume of its arithmetic
stabilizer in this norm-one part. Unconditional. -/
@[kb "siegel1944indef" "On the theory of indefinite quadratic forms; squares by x² + y² − z² (excluded case), regularized [unverified]"]
theorem siegel_qInd_squares {k : ℤ} (hk : k ≠ 0) (ξ : Measure.Weil.RatSphere (up qInd) ((((k ^ 2 : ℤ) : 𝓞 ℚ)) : ℚ)) :
    2 * (Indefinite.cInfNF (k := 2) ((((k ^ 2 : ℤ) : 𝓞 ℚ)) : ℚ) *
        ∑' i, Indefinite.repMeasureIso (r := 1) (up qInd) nondegenerate_up_qInd (DVR.unary ((k ^ 2 : ℤ) : 𝓞 ℚ))
          (Indefinite.unary_nondegenerate (intCast_sq_ne_zero hk)) (Indefinite.isSquare_deltaForms_unary (N := 3) (isSquare_qInd_sq k))
          ((Indefinite.ratFrameEquivRatSphere (n' := 2) (up qInd) ((k ^ 2 : ℤ) : 𝓞 ℚ)).symm ξ) i) =
      ENNReal.ofReal (8 / π ^ 2) * ∑' i, Indefinite.unitVolume (up qInd) nondegenerate_up_qInd i := by
  rw [← ternaryIsoDensityProductReg_qInd_sq hk]
  exact Indefinite.siegelIndefinite_ternary_isotropic_uncond (up qInd) nondegenerate_up_qInd
    (intCast_sq_ne_zero hk) (isSquare_qInd_sq k) ξ

end QuadFormsKB.Tamagawa.Classical
