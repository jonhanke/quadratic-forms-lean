/-
# Siegel's formula over $F$: the constant is $|d_F|^{-(n-1)/2}$

**Answer to the question on Hanke 2004 (5.3) over $F$.** With the
repository's normalizations, the Fourier coefficients of the genus Eisenstein series $E_Q$ (`eisQ`) are
$$a_{E_Q}(\nu) = |d_F|^{-(n-1)/2}\,\beta_\infty(\nu)\prod_\mathfrak p\beta_\mathfrak p(\nu)\qquad(\nu \in \mathcal O_F,\ \nu \gg 0),$$
**not** $\beta_\infty(\nu)\prod_\mathfrak p\beta_\mathfrak p(\nu)$ (`eisQ_coeff_eq_discr_mul_aENF`). Here $\beta_\infty = \prod_w\beta_w$ with
$\beta_w$ = `Siegel.betaInfAt` (Hanke (5.5): **Lebesgue measure** at each real place) and $\beta_\mathfrak p$ =
`LocalDensity.NF.localDensity` (Hanke (5.1)–(5.2): $\operatorname{Vol}(\mathfrak o_\mathfrak p) = 1$), i.e. the right side without the factor is
`Siegel.aENF` (Hanke 2004, (5.3), p. 368, which is stated over a totally real $F$). The factor is **not absorbed** in the
archimedean factors: the archimedean factors $\beta_w$ come out exactly (`eisArch_eq`), and the factor is the product of
three explicit constants, each proved:
* $|d_F|^{-1/2}$: the covolume of $\sigma(\mathcal O_F) \subset \mathbb R^d$ in the Poisson summation of each row of $E_Q$
  (`latConst_oBasis_eq`);
* $|d_F|^{-n/2}$: the covolume of $\sigma(\mathcal O_F)^n$ in the theta transformation (the theta constant, `thetaK`,
  `embDet_one`);
* $|d_F|^{+1} = \prod_\mathfrak pN(\mathfrak d_\mathfrak p)$: the local factors of the singular series are
  $N(\mathfrak d_\mathfrak p)\beta_\mathfrak p$, because the dual of $\mathcal O_\mathfrak p$ for $e(\operatorname{Tr}\,\cdot)$ is
  $\mathfrak d_\mathfrak p^{-1}$ (`SingularNF.locFactor_eventually_eq`, `SingularNF.singSeries_eq`).

$-\tfrac12 - \tfrac n2 + 1 = -\tfrac{n-1}2$. Over $\mathbb Q$ all three are $1$, consistent with Hanke (5.3) over $\mathbb Q$ (`hasSum_ssTerm`).
With self-dual measures ($\operatorname{vol}(\mathfrak o_\mathfrak p) = N(\mathfrak d_\mathfrak p)^{-1/2}$, Lebesgue at $\infty$) the same constant is
`globalConst_eq`.

**Consequence** (`eisQ_coeff_ne_aENF`): for every totally real $F \ne \mathbb Q$ and every $\nu = Q_0(x_0)$, $x_0 \ne 0$,
$a_{E_Q}(\nu) \ne$ `aENF Q₀ ν` (both sides are positive and $|d_F| > 2$, Minkowski). For example $F = \mathbb Q(\sqrt5)$, $|d_F| = 5$:
$a_{E_Q}(\nu) = 5^{-(n-1)/2}\,\mathrm{aENF}(\nu)$.

Hypotheses (as in `SteinitzGenus.lean`): $Q_0$ totally positive definite over $\mathcal O_F$ in $n = 2k$ variables, $k \ge 3$; $\mathfrak N \ne 0$ a theta
level (`IsThetaLevelF`); the genus of $\mathcal O_F^n$ free (`GenusFree`, true for $h_F = 1$).

Sources: Hanke 2004, (5.1)–(5.5), pp. 368–369; Siegel, Ann. Math. 36 (1935) and 38 (1937) [unverified]; Shimura, Duke
Math. J. 45 (1978), §3 [unverified].
-/
import QuadFormsKB.HilbertModular.EisensteinCoeff
import QuadFormsKB.Siegel.NFGoodPrime
import QuadFormsKB.Siegel.ArchimedeanNF
import QuadFormsKB.Tamagawa.MassInduction

open Complex NumberField Filter Topology
open scoped Real nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.HilbertModular

open QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

/-! ### The archimedean constant -/

lemma siegel_realEmb_eq (v : InfinitePlace F) (h : v.IsReal) :
    QuadFormsKB.Siegel.realEmb ⟨v, h⟩ = realEmb F v := rfl

/-- $D_w$ (Hanke's $\det(H_w/2)$, `gramDetNF`) is the determinant of the Gram matrix at $w$. -/
lemma gramDetNF_eq (Q : QuadForm (𝓞 F) n) (v : InfinitePlace F) (h : v.IsReal) :
    QuadFormsKB.Siegel.gramDetNF Q ⟨v, h⟩ = ((gramF Q).map (realEmb F v)).det := by
  rw [det_gramF_map, QuadFormsKB.Siegel.gramDetNF, QuadFormsKB.Siegel.realForm,
    QuadFormsKB.Siegel.hessian_map_NF]
  rw [show (Q.hessian.map ⇑((QuadFormsKB.Siegel.realEmb ⟨v, h⟩).comp ιO)).det =
      ((QuadFormsKB.Siegel.realEmb ⟨v, h⟩).comp ιO) Q.hessian.det from (RingHom.map_det _ _).symm]
  change realEmb F v (ιO Q.hessian.det) / 2 ^ n = realEmb F v ((1 / 2) ^ n * ιO Q.hessian.det)
  rw [map_mul, map_pow, map_div₀, map_one, map_ofNat]
  norm_num [div_eq_mul_inv, mul_comm]
  exact Or.inl (by rw [one_div, inv_pow])

/-- $\frac{n\,\omega_n}{2} = \frac{\pi^k}{(k-1)!}$ for $n = 2k$, $k \ge 1$. -/
lemma n_mul_unitBallVol_div_two {k : ℕ} (hk : 1 ≤ k) (hn : n = 2 * k) :
    (n : ℝ) * QuadFormsKB.Siegel.unitBallVol n / 2 = Real.pi ^ k / (k - 1).factorial := by
  rw [QuadFormsKB.Siegel.unitBallVol_eq (by omega), hn]
  have hG : Real.Gamma ((2 * k : ℕ) / 2 + 1 : ℝ) = (k.factorial : ℝ) := by
    rw [show ((2 * k : ℕ) : ℝ) / 2 + 1 = ((k : ℕ) : ℝ) + 1 by push_cast; ring, Real.Gamma_nat_eq_factorial]
  rw [hG, pow_mul, Real.sq_sqrt Real.pi_pos.le]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  field_simp

/-- **The real-place density** $\beta_w(\nu) = \frac{\pi^k}{(k-1)!}\,(\det A_w)^{-1/2}\,\sigma_w(\nu)^{k-1}$ ($n = 2k$). -/
lemma betaInfAt_eq (Q : QuadForm (𝓞 F) n) {k : ℕ} (hk : 1 ≤ k) (hn : n = 2 * k) (v : InfinitePlace F)
    (h : v.IsReal) (ν : F) (hdet : 0 < ((gramF Q).map (realEmb F v)).det) :
    QuadFormsKB.Siegel.betaInfAt Q ⟨v, h⟩ ν = Real.pi ^ k / (k - 1).factorial *
      (Real.sqrt ((gramF Q).map (realEmb F v)).det)⁻¹ * realEmb F v ν ^ (k - 1) := by
  rw [QuadFormsKB.Siegel.betaInfAt, gramDetNF_eq, siegel_realEmb_eq]
  have h1 : (((n : ℝ) - 2) / 2) = ((k - 1 : ℕ) : ℝ) := by
    rw [hn]; push_cast [Nat.cast_sub hk]; ring
  rw [h1, Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_neg hdet.le]
  have h2 := n_mul_unitBallVol_div_two (n := n) hk hn
  rw [← h2]
  ring

open Classical in
/-- **The archimedean constant of $E_Q$ is $|d_F|^{-(n+1)/2}\beta_\infty$**: for $n = 2k$, $\nu \gg 0$,
$$C_Q\,c_{\mathcal O}\,\Big(\frac{(-2\pi i)^k}{(k-1)!}\Big)^dN(\nu)^{k-1} = \big(d_F^{-1/2}\big)^{n+1}\prod_w\beta_w(\nu),$$
$C_Q = K_Q(i/2)^{kd}$, $K_Q = (\prod_v\sqrt{\det A_v})^{-1}d_F^{-n/2}$ (theta constant), $c_{\mathcal O} = d_F^{-1/2}$ (`latConst_oBasis_eq`),
$\beta_w$ = `Siegel.betaInfAt` (Lebesgue measure at each real place; $\frac i2\cdot(-2\pi i) = \pi$). -/
theorem eisArch_eq {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ} (hk : 1 ≤ k) (hn : n = 2 * k)
    {ν : F} (hν : ∀ v, 0 < realEmb F v ν) :
    eisCst Q k * (latConst (oBasis F) : ℂ) * lipCoeff k (realVec ν) =
      (((Real.sqrt (discr F : ℝ))⁻¹ ^ (n + 1) * QuadFormsKB.Siegel.betaInfNF Q ν : ℝ) : ℂ) := by
  have hpos : 0 < Real.sqrt (discr F : ℝ) := by
    have := embDet_one_pos (F := F); rwa [embDet_one] at this
  rw [eisCst, thetaK, lipCoeff, if_pos (show ∀ v, 0 < realVec ν v from hν)]
  simp only [realVec]
  rw [show ((latConst (oBasis F) : NNReal) : ℂ) = (((latConst (oBasis F) : ℝ)) : ℂ) from rfl, latConst_oBasis_eq]
  simp only [oneIdeals, embDet_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- the product over the real places
  rw [QuadFormsKB.Siegel.betaInfNF, Fintype.prod_equiv (Equiv.subtypeUnivEquiv fun v => IsTotallyReal.isReal v)
    (fun w : QuadFormsKB.Siegel.RealPlace F => QuadFormsKB.Siegel.betaInfAt Q w ν)
    (fun v => QuadFormsKB.Siegel.betaInfAt Q ⟨v, IsTotallyReal.isReal v⟩ ν) (fun w => rfl)]
  simp_rw [betaInfAt_eq Q hk hn _ _ ν ((hQ _).det_pos)]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  push_cast
  have hI : (Complex.I / 2) ^ (k * Fintype.card (InfinitePlace F)) *
      ((-2 * π * Complex.I) ^ k / (k - 1).factorial) ^ Fintype.card (InfinitePlace F) =
      ((π : ℂ) ^ k / (k - 1).factorial) ^ Fintype.card (InfinitePlace F) := by
    rw [pow_mul, ← mul_pow]
    congr 1
    rw [← mul_div_assoc, ← mul_pow]
    congr 2
    rw [show Complex.I / 2 * (-2 * π * Complex.I) = -(Complex.I * Complex.I) * π by ring, Complex.I_mul_I]
    ring
  rw [Finset.prod_inv_distrib]
  linear_combination (((∏ v, (Real.sqrt ((gramF Q).map (realEmb F v)).det : ℂ))⁻¹ *
    ((Real.sqrt (discr F : ℝ) : ℂ) ^ n)⁻¹ * ((Real.sqrt (discr F : ℝ) : ℂ))⁻¹ *
      ∏ v, ((realEmb F v ν : ℂ) ^ (k - 1)))) * hI

/-! ### The headline: $a_{E_Q}(\nu) = |d_F|^{-(n-1)/2}\,\mathrm{aENF}(\nu)$ -/

lemma discr_pos : (0 : ℝ) < (discr F : ℝ) := by
  have h := embDet_one_pos (F := F)
  rw [embDet_one] at h
  exact Real.sqrt_pos.mp h

lemma exists_oDual_eq {μ : F} (hμ : μ ∈ invDifferent F) : ∃ m, oDual m = μ := by
  have hmem : μ ∈ ((FractionalIdeal.dual ℤ ℚ (((1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)) :
      FractionalIdeal (𝓞 F)⁰ F) : Set F) := by
    rw [Units.val_one]; exact hμ
  refine ⟨(QuadFormsKB.Analysis.dualEquiv (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)).symm ⟨μ, hmem⟩, ?_⟩
  rw [oDual, ← QuadFormsKB.Analysis.dualEquiv_coe, Equiv.apply_symm_apply]

lemma oDual_zero : oDual (0 : Fin (Module.finrank ℚ F) → ℤ) = 0 := by
  simp [oDual, QuadFormsKB.Analysis.dualElt]

section Headline

variable {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ} (hn : n = 2 * k)
  {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑) (h𝔑 : 𝔑 ≠ ⊥) (hfree : GenusFree (formF Q₀) stdLat)

include hQ hn hlev h𝔑 hfree in
/-- **Siegel's formula over $F$: the Fourier coefficients of $E_Q$, with the exact constant** (answer to the question).
For $F$ totally real, $Q_0$ totally positive definite over $\mathcal O_F$ in $n = 2k \ge 6$ variables (theta level $\mathfrak N$,
free genus) and $\nu \in \mathcal O_F$ totally positive,
$$\mathrm{qCoeff}(E_Q, \nu) = |d_F|^{-(n-1)/2}\cdot\beta_\infty(\nu)\prod_\mathfrak p\beta_\mathfrak p(\nu) = |d_F|^{-(n-1)/2}\cdot\texttt{aENF}\,Q_0\,\nu,$$
$\beta_\infty = \prod_w\beta_w$ with Lebesgue measure at each real place (Hanke (5.5), `betaInfAt`), $\beta_\mathfrak p$ with
$\operatorname{Vol}(\mathfrak o_\mathfrak p) = 1$ (Hanke (5.1)–(5.2), every prime, dyadic included), and `qCoeff` the $\nu$-th Fourier coefficient
of $E_Q$ (the integral over $\mathbb R^d/\sigma(\mathcal O_F)$). The factor is **not** absorbed in the archimedean factors:
$|d_F|^{-(n-1)/2} = |d_F|^{-1/2}$ (Poisson for the rows, `latConst_oBasis_eq`) $\cdot\,|d_F|^{-n/2}$ (theta constant)
$\cdot\,|d_F|$ (singular series, $\prod_\mathfrak pN(\mathfrak d_\mathfrak p)$, `SingularNF.singSeries_eq`).

*Erratum (Hanke 2004, (5.3), p. 368, over $F \ne \mathbb Q$):* with the normalizations of (5.1) and (5.5), (5.3) needs the factor
$|d_F|^{-(n-1)/2}$ (an erratum of the source). Over $\mathbb Q$ the factor is $1$. -/
@[kb "hanke2004" "(5.3), p. 368, over F: a_E(ν) = |d_F|^{-(n-1)/2} ∏_v β_v(ν) (corrected constant); Siegel 1935/1937 [unverified]"]
theorem eisQ_coeff_eq_discr_mul_aENF (hk : 3 ≤ k) {ν : 𝓞 F} (hν : ∀ v, 0 < realEmb F v (ιO ν)) :
    qCoeff (eisQ Q₀ k) (oBasis F) (realVec (ιO ν)) =
      (((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (n - 1) * QuadFormsKB.Siegel.aENF Q₀ ν : ℝ) : ℂ) := by
  have hQ' := isTotPosGram_Q₀ hQ
  have hQnd : Q₀.Nondegenerate := det_hessian_ne_zero hQ'
  have hν0 : ν ≠ 0 := by
    rintro rfl
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
    simpa using hν v
  obtain ⟨m, hm⟩ := exists_oDual_eq (algebraMap_mem_invDifferent ν)
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [oDual_zero] at hm
    exact hν0 (by simpa using hm.symm)
  have hz := eisQ_qexp hQ hn hlev h𝔑 hfree hk (fun _ => UpperHalfPlane.I)
  have hss := SiegelWeil.SingularNF.singSeries_eq Q₀ hQnd (by omega) hν0 (hz.2.1 (ιO ν))
    (QuadFormsKB.Siegel.multipliable_eulerFactorNF hQnd (by omega) (QuadFormsKB.Siegel.hshape_NF Q₀) hν0)
  rw [show realVec (ιO ν) = dualVec (oBasis F) m by rw [dualVec_oBasis, hm],
    qCoeff_eisQ hQ hn hlev h𝔑 hfree hk hm0, hm, eisQCoeff, eisArch_eq hQ' (by omega) hn hν, hss]
  have hd := discr_pos (F := F)
  have hs : Real.sqrt (discr F : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  have hN : (((discr F).natAbs : ℕ) : ℝ) = Real.sqrt (discr F : ℝ) ^ 2 := by
    rw [Nat.cast_natAbs, Int.cast_abs, Real.sq_sqrt hd.le, abs_of_pos hd]
  rw [abs_of_pos hd, QuadFormsKB.Siegel.aENF, QuadFormsKB.Siegel.aEWithNF, QuadFormsKB.Siegel.eulerProductNF, hN]
  push_cast
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hs' : (Real.sqrt (discr F : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  simp only [QuadFormsKB.Siegel.eulerFactorNF]
  have key : (Real.sqrt (discr F : ℝ) : ℂ) ^ 2 * ((Real.sqrt (discr F : ℝ) : ℂ)⁻¹) ^ (j + 1 + 1) =
      ((Real.sqrt (discr F : ℝ) : ℂ)⁻¹) ^ j := by
    have h1 : (Real.sqrt (discr F : ℝ) : ℂ) ^ 2 * ((Real.sqrt (discr F : ℝ) : ℂ)⁻¹) ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hs', one_pow]
    calc (Real.sqrt (discr F : ℝ) : ℂ) ^ 2 * ((Real.sqrt (discr F : ℝ) : ℂ)⁻¹) ^ (j + 1 + 1)
        = ((Real.sqrt (discr F : ℝ) : ℂ) ^ 2 * ((Real.sqrt (discr F : ℝ) : ℂ)⁻¹) ^ 2) *
            ((Real.sqrt (discr F : ℝ) : ℂ)⁻¹) ^ j := by ring
      _ = ((Real.sqrt (discr F : ℝ) : ℂ)⁻¹) ^ j := by rw [h1, one_mul]
  linear_combination ((QuadFormsKB.Siegel.betaInfNF Q₀ (ιO ν) : ℂ) *
    ((∏' v, LocalDensity.NF.localDensity v Q₀ ν : ℝ) : ℂ)) * key

/-- **Over $\mathbb Q$ the factor is $1$** ($d_{\mathbb Q} = 1$): `eisQ_coeff_eq_discr_mul_aENF` reduces to Hanke's (5.3) over $\mathbb Q$, the
statement of `Siegel.aE` (whose singular series is `Siegel.hasSum_ssTerm`, with local factors $\beta_p$: $\mathfrak d = (1)$). -/
theorem discrFactor_rat (n : ℕ) : (Real.sqrt |((discr ℚ : ℤ) : ℝ)|)⁻¹ ^ (n - 1) = 1 := by
  rw [Rat.numberField_discr]; simp

/-! ### Consistency with `Tamagawa.siegelProduct` is $|d_F|^{-(N-1)/2}\,\mathrm{aENF}$ -/

/-- $\frac{N\omega_N}{2} = \frac{\pi^{N/2}}{\Gamma(N/2)}$ ($N \ge 1$): Hanke's (5.5) constant is `archRepDensity` constant. -/
lemma n_mul_unitBallVol_div_two' {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) * QuadFormsKB.Siegel.unitBallVol N / 2 = Real.pi ^ ((N : ℝ) / 2) / Real.Gamma ((N : ℝ) / 2) := by
  rw [QuadFormsKB.Siegel.unitBallVol_eq hN, Real.Gamma_add_one (by positivity), Real.sqrt_eq_rpow,
    ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
  have hG : 0 < Real.Gamma ((N : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  field_simp

open Classical in
/-- **The Siegel product is $|d_F|^{-(N-1)/2}$ times `aENF`** (totally real $F$, $Q_0$ totally positive definite, $m \gg 0$):
$$\texttt{Tamagawa.siegelProduct}\ Q_0\ m = |d_F|^{-(N-1)/2}\cdot\texttt{Siegel.aENF}\ Q_0\ m.$$
The product over the embeddings $\sigma : F \to \mathbb C$ is the product over the real places (one embedding each), and
`archRepDensity` at $\sigma$ is `Siegel.betaInfAt` at its place. With `eisQ_coeff_eq_discr_mul_aENF`: the input
`SiegelFormulaAt Q₀ m` says that the genus average $\mathrm{repMass}/\mathrm{Mass}$ is the $m$-th Fourier coefficient of $E_Q$. -/
theorem siegelProduct_eq_discr_mul_aENF {N : ℕ} {Q : QuadForm (𝓞 F) N} (hQ : IsTotPosGram (gramF Q)) (hN : 1 ≤ N)
    {m : 𝓞 F} (hm : ∀ v, 0 < realEmb F v (ιO m)) :
    QuadFormsKB.Tamagawa.siegelProduct Q m =
      (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (N - 1) * QuadFormsKB.Siegel.aENF Q m := by
  have hd := discr_pos (F := F)
  -- the discriminant factor
  have hfac : |(discr F : ℝ)| ^ (-((N : ℝ) - 1) / 2) = (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (N - 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (abs_nonneg _), ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    rw [Nat.cast_sub hN]; push_cast; ring
  -- the archimedean product
  have harch : ∏ σ : F →ₐ[ℚ] ℂ, QuadFormsKB.Tamagawa.archRepDensity N ‖σ (ιO m)‖
      (QuadFormsKB.Tamagawa.detGram Q σ) = QuadFormsKB.Siegel.betaInfNF Q (ιO m) := by
    set G : InfinitePlace F → ℝ := fun w => QuadFormsKB.Tamagawa.archRepDensity N (w (ιO m))
      (w (ιO Q.hessian.det / 2 ^ N))
    have h1 : ∏ σ : F →ₐ[ℚ] ℂ, QuadFormsKB.Tamagawa.archRepDensity N ‖σ (ιO m)‖
        (QuadFormsKB.Tamagawa.detGram Q σ) = ∏ φ : F →+* ℂ, G (InfinitePlace.mk φ) := by
      rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ : F →+* ℂ => G (InfinitePlace.mk φ))
        (fun σ => QuadFormsKB.Tamagawa.archRepDensity N ‖σ (ιO m)‖ (QuadFormsKB.Tamagawa.detGram Q σ))]
      intro φ
      simp only [G, QuadFormsKB.Tamagawa.detGram, InfinitePlace.apply, RingHom.equivRatAlgHom_apply]
      rfl
    have h2 : ∏ φ : F →+* ℂ, G (InfinitePlace.mk φ) = ∏ w : InfinitePlace F, G w ^ w.mult := by
      rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ => G (InfinitePlace.mk φ))]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [Finset.prod_congr rfl fun φ hφ => by rw [(Finset.mem_filter.mp hφ).2], Finset.prod_const,
        InfinitePlace.card_filter_mk_eq]
    rw [h1, h2, QuadFormsKB.Siegel.betaInfNF, Fintype.prod_equiv
      (Equiv.subtypeUnivEquiv fun v => IsTotallyReal.isReal v)
      (fun w : QuadFormsKB.Siegel.RealPlace F => QuadFormsKB.Siegel.betaInfAt Q w (ιO m))
      (fun v => QuadFormsKB.Siegel.betaInfAt Q ⟨v, IsTotallyReal.isReal v⟩ (ιO m)) (fun w => rfl)]
    refine Finset.prod_congr rfl fun w _ => ?_
    have hmult : w.mult = 1 := by simp [InfinitePlace.mult, IsTotallyReal.isReal w]
    rw [hmult, pow_one]
    simp only [G, QuadFormsKB.Tamagawa.archRepDensity, QuadFormsKB.Siegel.betaInfAt, gramDetNF_eq,
      siegel_realEmb_eq]
    have hw1 : w (ιO m) = realEmb F w (ιO m) := by rw [← abs_realEmb, abs_of_pos (hm w)]
    have hhalf : ∀ x : F, (1 / 2 : F) ^ N * x = x / 2 ^ N := fun x => by
      rw [one_div, inv_pow, div_eq_mul_inv, mul_comm]
    have hdet : ((gramF Q).map (realEmb F w)).det = w (ιO Q.hessian.det / 2 ^ N) := by
      have hp := (hQ w).det_pos
      rw [det_gramF_map, hhalf] at hp ⊢
      rw [← abs_realEmb, abs_of_pos hp]
    rw [hw1, ← hdet, ← n_mul_unitBallVol_div_two' hN]
    ring
  rw [QuadFormsKB.Tamagawa.siegelProduct, hfac, harch, QuadFormsKB.Siegel.aENF, QuadFormsKB.Siegel.aEWithNF,
    QuadFormsKB.Siegel.eulerProductNF]
  simp only [QuadFormsKB.Siegel.eulerFactorNF]
  ring

/-! ### Consequence: `aENF` is not the Fourier coefficient over $F \ne \mathbb Q$ -/

/-- A totally positive Gram matrix makes $Q$ totally positive definite in the sense of `Siegel.IsTotallyPosDef`. -/
theorem siegel_isTotallyPosDef {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) :
    QuadFormsKB.Siegel.IsTotallyPosDef Q := by
  rintro ⟨v, h⟩ y hy
  have hg : QuadFormsKB.Siegel.gramMatrixR (QuadFormsKB.Siegel.realForm Q ⟨v, h⟩) = (gramF Q).map (realEmb F v) := by
    rw [QuadFormsKB.Siegel.gramMatrixR, QuadFormsKB.Siegel.realForm, QuadFormsKB.Siegel.hessian_map_NF, gramF]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, RingHom.coe_comp, Function.comp_apply,
      map_mul, map_div₀, map_one, map_ofNat]
    rfl
  change 0 < (QuadFormsKB.Siegel.realForm Q ⟨v, h⟩).eval y
  rw [QuadFormsKB.Siegel.eval_real_eq_gramR, hg]
  simpa using (hQ v).dotProduct_mulVec_pos hy

/-- $\sigma_v(Q(x)) > 0$ for $x \ne 0$. -/
theorem realEmb_eval_pos {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {x : Fin n → 𝓞 F} (hx : x ≠ 0)
    (v : InfinitePlace F) : 0 < realEmb F v (ιO (Q.eval x)) := by
  have hy : (fun i => realEmb F v (ιO (x i))) ≠ 0 := by
    intro h0; apply hx; funext i
    have := congrFun h0 i
    simp only [Pi.zero_apply, map_eq_zero_iff _ (realEmb_injective F v)] at this
    exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mp this
  have h := siegel_isTotallyPosDef hQ ⟨v, IsTotallyReal.isReal v⟩ _ hy
  have he := QuadFormsKB.Siegel.map_eval_eq ((realEmb F v).comp ιO) Q x
  rw [QuadFormsKB.Siegel.realForm] at h
  change 0 < (Q.map ((realEmb F v).comp ιO)).eval fun i => realEmb F v (ιO (x i)) at h
  simp only [RingHom.comp_apply] at he
  rw [he]
  exact h

/-- **`aENF` is positive at the values of $Q$**: $\mathrm{aENF}(Q(x)) > 0$ for $x \ne 0$ ($n \ge 4$; local representability is
witnessed by $x$ itself, and Hanke's lower bound `aENF_ge_uncond`). -/
theorem aENF_eval_pos {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) (hn : 4 ≤ n) {x : Fin n → 𝓞 F}
    (hx : x ≠ 0) : 0 < QuadFormsKB.Siegel.aENF Q (Q.eval x) := by
  classical
  have hQnd : Q.Nondegenerate := det_hessian_ne_zero hQ
  have hpos := realEmb_eval_pos hQ hx
  have hT0 : Q.eval x ≠ 0 := by
    intro h0
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
    have := hpos v; rw [h0, map_zero, map_zero] at this; exact lt_irrefl _ this
  refine lt_of_lt_of_le ?_ (QuadFormsKB.Siegel.aENF_ge_uncond Q (siegel_isTotallyPosDef hQ) hQnd hn hT0
    fun w => (hpos w.1).le)
  refine mul_pos (mul_pos (pow_pos (div_pos (by norm_num) (pow_pos Real.pi_pos 2)) _) ?_) ?_
  · -- the archimedean density is positive
    refine Finset.prod_pos fun w _ => ?_
    obtain ⟨v, h⟩ := w
    rw [QuadFormsKB.Siegel.betaInfAt, gramDetNF_eq, siegel_realEmb_eq]
    have hω : 0 < QuadFormsKB.Siegel.unitBallVol n := by
      rw [QuadFormsKB.Siegel.unitBallVol_eq (by omega)]
      exact div_pos (pow_pos (Real.sqrt_pos.mpr Real.pi_pos) _) (Real.Gamma_pos_of_pos (by positivity))
    have hD := (hQ v).det_pos
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have := hpos v
    positivity
  · -- the local densities at the finitely many bad primes are positive
    refine Finset.prod_pos fun v _ => QuadFormsKB.Siegel.localDensityNF_pos v Q hQnd hT0 ?_
    refine Eventually.of_forall fun k => ?_
    have := SiegelWeil.SingularNF.finite_quot (pow_ne_zero k v.ne_bot)
    rw [LocalDensity.NF.repCount]
    have hne : Nonempty {y : Fin n → 𝓞 F ⧸ v.asIdeal ^ k //
        Q.evalIn (𝓞 F ⧸ v.asIdeal ^ k) y = Ideal.Quotient.mk _ (Q.eval x)} :=
      ⟨⟨fun i => Ideal.Quotient.mk _ (x i), (SiegelWeil.SingularNF.mk_eval Q _ x).symm⟩⟩
    exact Nat.card_pos

include hQ hn hlev h𝔑 hfree in
/-- **Hanke's (5.3), transcribed over $F$ as `aENF`, is not the Fourier coefficient of $E_Q$ when $F \ne \mathbb Q$**: for every
$x_0 \ne 0$, $\mathrm{qCoeff}(E_Q, Q_0(x_0)) \ne \mathrm{aENF}(Q_0(x_0))$; indeed it is $|d_F|^{-(n-1)/2}$ times it, $\mathrm{aENF} > 0$ and
$|d_F| > 2$ (Minkowski). E.g. $F = \mathbb Q(\sqrt5)$: the factor is $5^{-(n-1)/2}$. -/
@[kb "hanke2004" "(5.3), p. 368, over F ≠ ℚ: the printed constant fails (erratum, confirmed by proof)"]
theorem eisQ_coeff_ne_aENF (hk : 3 ≤ k) (hdeg : 1 < Module.finrank ℚ F) {x : Fin n → 𝓞 F} (hx : x ≠ 0) :
    qCoeff (eisQ Q₀ k) (oBasis F) (realVec (ιO (Q₀.eval x))) ≠
      ((QuadFormsKB.Siegel.aENF Q₀ (Q₀.eval x) : ℝ) : ℂ) := by
  have hQ' := isTotPosGram_Q₀ hQ
  rw [eisQ_coeff_eq_discr_mul_aENF hQ hn hlev h𝔑 hfree hk (realEmb_eval_pos hQ' hx), Ne, Complex.ofReal_inj]
  have hA := aENF_eval_pos hQ' (by omega) hx
  have hd : (2 : ℝ) < |(discr F : ℝ)| := by exact_mod_cast NumberField.abs_discr_gt_two hdeg
  have hs : 1 < Real.sqrt |(discr F : ℝ)| := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one (by linarith)
  have hlt : (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (n - 1) < 1 :=
    pow_lt_one₀ (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_lt_one_of_one_lt₀ hs) (by omega)
  intro h
  have : (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (n - 1) = 1 := by
    have := h
    field_simp at this
    nlinarith [this]
  exact absurd this hlt.ne

include hQ hn hlev h𝔑 hfree in
/-- **The Siegel product is the Fourier coefficient of $E_Q$** ($n = 2k \ge 6$, $m \gg 0$):
$S(L, m) = \mathrm{qCoeff}(E_Q, m)$. So the input `SiegelFormulaAt Q₀ m` (genus average $= S(L, m)$) is the statement that the
genus average of $r_M(m)$ is the $m$-th Fourier coefficient of the genus Eisenstein series, with the proven constant. -/
@[kb "siegel1935" "Hauptsatz over F: the local side equals the Eisenstein coefficient (constant proved) [unverified]"]
theorem siegelProduct_eq_qCoeff_eisQ (hk : 3 ≤ k) {m : 𝓞 F} (hm : ∀ v, 0 < realEmb F v (ιO m)) :
    ((QuadFormsKB.Tamagawa.siegelProduct Q₀ m : ℝ) : ℂ) = qCoeff (eisQ Q₀ k) (oBasis F) (realVec (ιO m)) := by
  rw [eisQ_coeff_eq_discr_mul_aENF hQ hn hlev h𝔑 hfree hk hm,
    siegelProduct_eq_discr_mul_aENF (isTotPosGram_Q₀ hQ) (by omega) hm]

end Headline

/-- **Class number one: the constant with no freeness hypothesis** ($\mathcal O_F$ a PID, e.g. $F = \mathbb Q(\sqrt5)$):
$\mathrm{qCoeff}(E_Q, \nu) = |d_F|^{-(n-1)/2}\,\mathrm{aENF}(\nu)$ for $\nu \gg 0$ (`eisQ_coeff_eq_discr_mul_aENF`, the genus being free by
`genusFree_of_isPrincipalIdealRing`). -/
@[kb "hanke2004" "(5.3), p. 368, over F with h_F = 1: corrected constant, unconditional"]
theorem eisQ_coeff_eq_discr_mul_aENF_of_pid [IsPrincipalIdealRing (𝓞 F)] {Q₀ : QuadForm (𝓞 F) n}
    (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ} (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑)
    (h𝔑 : 𝔑 ≠ ⊥) (hk : 3 ≤ k) {ν : 𝓞 F} (hν : ∀ v, 0 < realEmb F v (ιO ν)) :
    qCoeff (eisQ Q₀ k) (oBasis F) (realVec (ιO ν)) =
      (((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (n - 1) * QuadFormsKB.Siegel.aENF Q₀ ν : ℝ) : ℂ) :=
  eisQ_coeff_eq_discr_mul_aENF hQ hn hlev h𝔑 (genusFree_of_isPrincipalIdealRing _ _) hk hν

/-- **Class number one, $F \ne \mathbb Q$: `aENF` is not the Fourier coefficient** (no freeness hypothesis; e.g. $\mathbb Q(\sqrt5)$). -/
@[kb "hanke2004" "(5.3), p. 368, over F ≠ ℚ with h_F = 1: the printed constant fails, unconditional"]
theorem eisQ_coeff_ne_aENF_of_pid [IsPrincipalIdealRing (𝓞 F)] {Q₀ : QuadForm (𝓞 F) n}
    (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ} (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑)
    (h𝔑 : 𝔑 ≠ ⊥) (hk : 3 ≤ k) (hdeg : 1 < Module.finrank ℚ F) {x : Fin n → 𝓞 F} (hx : x ≠ 0) :
    qCoeff (eisQ Q₀ k) (oBasis F) (realVec (ιO (Q₀.eval x))) ≠
      ((QuadFormsKB.Siegel.aENF Q₀ (Q₀.eval x) : ℝ) : ℂ) :=
  eisQ_coeff_ne_aENF hQ hn hlev h𝔑 (genusFree_of_isPrincipalIdealRing _ _) hk hdeg hx

end QuadFormsKB.HilbertModular
