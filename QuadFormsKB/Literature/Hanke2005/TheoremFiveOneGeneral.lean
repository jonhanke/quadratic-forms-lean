/-
# Hanke's Theorem 5.1 without Shimura's hypothesis

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005), Theorem 5.1
(locators: 1999 thesis, pp. 16–19); W. T. Gan, J. Hanke, J.-K. Yu, *On an exact mass formula of Shimura*, Duke Math. J. 107
(2001), §6, Table 4 and §7.

Theorem 5.1 as printed omits Shimura's hypothesis ("for odd $n$, $\det\varphi$ is locally a unit times a square",
`ShimuraDetHyp`), and is false without it. Gan–Hanke–Yu compute the local
factor in the excluded case too. Here we prove the formula **for every** $Q_0$ ($n\ge3$, $\mathcal O_F^n$ maximal, any number
field, any signature), with Hanke's $\lambda_v$ replaced at the excluded places by
$$\lambda'_v = \tfrac12\,(1 + q^{-m})\ (t_v = 1),\qquad \lambda'_v = \tfrac12\,(1 - q^{-m})\ (t_v = 3),\qquad m = \lfloor n/2\rfloor$$
(`lambdaOddNonUnit`, `lambdaGen`; at every other place $\lambda'_v = \lambda_v$), so that
$$\mathrm{Mass} = \text{`theorem51RHSGen`}\qquad(\texttt{theorem51\_general}),$$
**unconditionally** (no named input, no hypothesis on $\det$). Under Shimura's hypothesis `theorem51RHSGen = theorem51RHS`
(`theorem51RHSGen_eq`), which re-derives the hypothesized Theorem 5.1 (`theorem51_of_general`); the totally definite case is
`theorem51_definite_general`.

*Proof.* The local factor at every finite place is $\alpha_\mathfrak p = [\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p]\,\xi'_\mathfrak p$, with
$\xi' = \xi$ (Shimura's (3.3), per place: `siegelDensity_eq_at`) or $\xi' = $ `xiOddNonUnit` at the excluded places
(`siegelDensity_oddNonUnit`). In both cases $\lambda'_v\,\xi'_v$ is the generic Euler factor (`xiGen_local_gen`):
for odd $n$, $\tfrac12(1\pm q^{-m})\cdot2(1\mp q^{-m})\prod_{i<m}(1-q^{-2i}) = \prod_{i\le m}(1-q^{-2i})$. The rest is the proof
of `theorem51` (Theorem 2.1 with $\tau = 2$, the Euler products, the archimedean factors), with $\lambda'$ for $\lambda$.

**Relation to GHY.** GHY's $\lambda_v$ (2.12) is a ratio of volumes of the hyperspecial model and the stabilizer of the
maximal lattice; on the excluded rows (Table 4, $\delta\notin A^\times$) the quasi-split space with the same discriminant has the
maximal lattice $\mathbb H^{m}\perp\langle\pi u\rangle$ ($t = 1$) whose $\xi'$ is $2(1-q^{-m})\prod_{i<m}$, so GHY's ratio for
$w = -1$ is $\xi'(t{=}1)/\xi'(t{=}3) = (1-q^{-m})/(1+q^{-m})$, and $\lambda'_v = \tfrac12(1+q^{-m})\cdot$(that ratio) for
$t = 3$. Indices are 0-based.
-/
import QuadFormsKB.Literature.Hanke2005.ShimuraDensityAt
import QuadFormsKB.Literature.Hanke2005.MassDefinite

open NumberField IsDedekindDomain Real
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.LocalDensity QuadFormsKB.Tamagawa.LatChange

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### The local factors -/

/-- **$\lambda'_v$ at the places excluded by Shimura's hypothesis** ($n$ odd, $\det\varphi$ not a unit times a square),
$m = \lfloor n/2\rfloor$: $\tfrac12(1+q^{-m})$ for $t_v = 1$ and $\tfrac12(1-q^{-m})$ for $t_v = 3$. -/
@[kb "ganhankeyu2001" "Table 4 (odd rank, δ ∉ A×), in Hanke's normalization of λ_v"]
def lambdaOddNonUnit (q : ℝ) (n t : ℕ) : ℝ :=
  if t = 1 then (1 + q ^ (-((n / 2 : ℕ) : ℝ))) / 2 else (1 - q ^ (-((n / 2 : ℕ) : ℝ))) / 2

section LocalFactors

variable (v : HeightOneSpectrum (𝓞 F))

open Classical in
/-- **The local factor $\lambda'_v$ of Theorem 5.1 without Shimura's hypothesis:** `lambdaOddNonUnit` at a place where $n$ is
odd and $\det\varphi$ is not a unit times a square (`DetUnitSqAt` fails), Hanke's `lambdaAt` elsewhere. -/
@[kb "hanke2005crelle" "Theorem 5.1, p. 17 (λ_v), extended to the places excluded by Shimura's hypothesis (GHY 2001, Table 4)"]
def lambdaGen (Q₀ : QuadForm (𝓞 F) n) : ℝ :=
  if Odd n ∧ ¬ DetUnitSqAt v Q₀ then lambdaOddNonUnit (normQ v) n (anisoDim v Q₀) else lambdaAt v Q₀

open Classical in
/-- **The local factor $\xi'_\mathfrak p$:** `xiOddNonUnit` at the excluded places, Hanke's `xiAt` elsewhere. -/
def xiAtGen (Q₀ : QuadForm (𝓞 F) n) : ℝ :=
  if Odd n ∧ ¬ DetUnitSqAt v Q₀ then xiOddNonUnit (normQ v) n (anisoDim v Q₀) else xiAt v Q₀

theorem algebraMap_det_eq (Q₀ : QuadForm (𝓞 F) n) :
    algebraMap F (v.adicCompletion F) ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det) =
      ((((NF.Qp v Q₀).hessian.det : v.adicCompletionIntegers F)) : v.adicCompletion F) := by
  rw [hessian_det_cast v Q₀]
  have : (Q₀.map (algebraMap (𝓞 F) F)).hessian = Q₀.hessian.map (algebraMap (𝓞 F) F) := by
    ext i j; simp [QuadForm.hessian, QuadForm.map]
  rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rfl

/-- **At a self-dual place Shimura's condition holds** ($n$ odd): non-dyadic, $\det H$ and $2$ are units; dyadic, a unit
$\det H$ forces $n$ even (`exists_pairSum_of_isLocalLevel_zero`). -/
theorem detUnitSqAt_of_dualIndexAt_eq_one (hodd : Odd n) (Q₀ : QuadForm (𝓞 F) n) (h1 : dualIndexAt v Q₀ = 1) :
    DetUnitSqAt v Q₀ := by
  have hπ := NF.irreducible_π v
  have hdet := isUnit_det_of_dualIndexAt_eq_one v Q₀ h1
  by_cases h2 : IsUnit (2 : v.adicCompletionIntegers F)
  · refine ⟨1, one_ne_zero, ?_⟩
    have h2n : ‖(2 : v.adicCompletion F)‖ = 1 := by
      have := norm_coe_unit v h2
      rwa [show (((2 : v.adicCompletionIntegers F)) : v.adicCompletion F) = 2 from
        map_ofNat (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) 2] at this
    rw [one_pow, mul_one, map_div₀, map_pow, map_ofNat, algebraMap_det_eq, norm_div, norm_pow, h2n, one_pow,
      div_one, norm_coe_unit v hdet]
  · exfalso
    have hπ2 : NF.π v ∣ 2 := by
      by_contra hd
      exact h2 (DVR.dvr_isUnit_of_not_dvd hπ hd)
    obtain ⟨r, A, hr, -, -⟩ := DVR.exists_pairSum_of_isLocalLevel_zero (NF.Qp v Q₀) hπ hπ2 (NF.two_ne_zero' v)
      (isLocalLevel_zero_of_isUnit_det _ _ hdet)
    obtain ⟨j, hj⟩ := hodd
    omega

/-- **The local factor at every finite place, without Shimura's hypothesis:** $\alpha_\mathfrak p = [\widetilde\Lambda_\mathfrak p:
\Lambda_\mathfrak p]\,\xi'_\mathfrak p$. -/
@[kb "hanke2005crelle" "(3.3), p. 8, with GHY 2001 Table 4 at the places excluded by Shimura's hypothesis"]
theorem siegelDensity_eq_gen (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) :
    NF.siegelDensity v Q₀ Q₀ = dualIndexAt v Q₀ * xiAtGen v Q₀ := by
  unfold xiAtGen
  split_ifs with h
  · exact (siegelDensity_oddNonUnit v hn h.1 Q₀ hQ hmax h.2).2
  · exact siegelDensity_eq_at hn Q₀ hQ hmax v fun hodd => by
      by_contra hc; exact h ⟨hodd, hc⟩

theorem xiAtGen_pos (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) :
    0 < xiAtGen v Q₀ := by
  have h1 := siegelDensity_eq_gen v hn Q₀ hQ hmax
  have h2 := Tamagawa.siegelDensity_pos v Q₀ hQ
  have h3 := dualIndexAt_pos v Q₀ hQ
  rw [h1] at h2
  exact pos_of_mul_pos_right h2 h3.le

open Classical in
/-- **$\lambda'_v\xi'_v$ is the generic Euler factor** at every finite place (`xiGen`). -/
theorem xiGen_local_gen (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) :
    xiGen (normQ v) n (chiK v Q₀) = lambdaGen v Q₀ * xiAtGen v Q₀ := by
  unfold lambdaGen xiAtGen
  split_ifs with h
  · obtain ⟨ht, -⟩ := siegelDensity_oddNonUnit v hn h.1 Q₀ hQ hmax h.2
    have hq0 : 0 < normQ v := lt_trans zero_lt_one (one_lt_normQ v)
    have hm1 : 1 ≤ n / 2 := by omega
    have hp := ppow_succ_eq hq0.le (n / 2) hm1
    simp only [xiGen, h.1, ite_true]
    rw [hp]
    unfold lambdaOddNonUnit xiOddNonUnit
    rcases ht with ht | ht
    · rw [ht, if_pos rfl, if_pos rfl]; ring
    · rw [ht, if_neg (by decide), if_neg (by decide)]; ring
  · have hw := two_mul_wittIndex_le v Q₀ hQ
    have hpar : anisoDim v Q₀ % 2 = n % 2 := by unfold anisoDim; omega
    have hpos : 0 < xiAt v Q₀ := by
      have := xiAtGen_pos v hn Q₀ hQ hmax
      unfold xiAtGen at this
      rwa [if_neg h] at this
    have := xiGen_eq (normQ v) n (anisoDim v Q₀) (IsRamifiedAt v Q₀) (dualIndexAt v Q₀ = 1)
      (IsSquare (algebraMap F (v.adicCompletion F) (discK Q₀)))
      (by have := NFEuler.two_le_normP v; unfold normQ; exact_mod_cast this) hn hpar
      (shimuraMaximalTypes.selfDual hn Q₀ hQ hmax v)
      (fun he => shimuraMaximalTypes.even_two_iff hn he Q₀ hQ v) hpos
    unfold chiK lambdaAt xiAt
    convert this

theorem lambdaGen_pos (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) :
    0 < lambdaGen v Q₀ := by
  have h := xiGen_local_gen v hn Q₀ hQ hmax
  have h1 := xiGen_pos (one_lt_normQ v) hn (abs_chiK_le v Q₀)
  have h2 := xiAtGen_pos v hn Q₀ hQ hmax
  rw [h] at h1
  exact pos_of_mul_pos_left h1 h2.le

theorem lambdaGen_eq_one_of (Q₀ : QuadForm (𝓞 F) n) (h : dualIndexAt v Q₀ = 1) : lambdaGen v Q₀ = 1 := by
  unfold lambdaGen
  rw [if_neg (fun hc => hc.2 (detUnitSqAt_of_dualIndexAt_eq_one v hc.1 Q₀ h)), lambdaAt_eq_one_of Q₀ v h]

/-- **Under Shimura's hypothesis $\lambda'_v = \lambda_v$.** -/
theorem lambdaGen_eq_of_hyp (Q₀ : QuadForm (𝓞 F) n) (hdet : ShimuraDetHyp Q₀) : lambdaGen v Q₀ = lambdaAt v Q₀ := by
  unfold lambdaGen
  rw [if_neg (fun hc => hc.2 (hdet hc.1 v))]

end LocalFactors

/-! ### The global identity -/

theorem hasFiniteMulSupport_lambdaGen (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => lambdaGen v Q₀ := by
  refine (hasFiniteMulSupport_dualIndexAt Q₀ hQ).subset fun v hv => ?_
  simp only [Function.mem_mulSupport] at hv ⊢
  exact fun h => hv (lambdaGen_eq_one_of v Q₀ h)

theorem tprod_inv_lambdaGen (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) :
    ∏' v : HeightOneSpectrum (𝓞 F), (lambdaGen v Q₀)⁻¹ = (∏' v : HeightOneSpectrum (𝓞 F), lambdaGen v Q₀)⁻¹ := by
  have h1 := hasFiniteMulSupport_lambdaGen Q₀ hQ
  have h2 : ∏' v : HeightOneSpectrum (𝓞 F), (lambdaGen v Q₀)⁻¹ = ∏ᶠ v : HeightOneSpectrum (𝓞 F), (lambdaGen v Q₀)⁻¹ :=
    tprod_eq_finprod (L := SummationFilter.unconditional _) (f := fun v => (lambdaGen v Q₀)⁻¹) h1.inv
  rw [tprod_eq_finprod (L := SummationFilter.unconditional _) h1, h2, finprod_inv_distrib]

theorem tprod_lambdaGen_pos (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) :
    0 < ∏' v : HeightOneSpectrum (𝓞 F), lambdaGen v Q₀ := by
  have h1 := hasFiniteMulSupport_lambdaGen Q₀ hQ
  rw [tprod_eq_finprod (L := SummationFilter.unconditional _) h1, finprod_eq_prod_of_mulSupport_subset _
    (Set.Finite.coe_toFinset h1).symm.subset]
  exact Finset.prod_pos fun v _ => lambdaGen_pos v hn Q₀ hQ hmax

theorem tprod_siegelDensity_eq_gen (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hmax : StdIsMaximal Q₀) :
    ∏' v : HeightOneSpectrum (𝓞 F), NF.siegelDensity v Q₀ Q₀ =
      (∏' v, dualIndexAt v Q₀) * (xiGenVal F n (fun v => chiK v Q₀) * (∏' v, lambdaGen v Q₀)⁻¹) := by
  have hI : HasProd (fun v : HeightOneSpectrum (𝓞 F) => dualIndexAt v Q₀) (∏' v, dualIndexAt v Q₀) :=
    (multipliable_of_hasFiniteMulSupport (hasFiniteMulSupport_dualIndexAt Q₀ hQ)).hasProd
  have hΛ : HasProd (fun v : HeightOneSpectrum (𝓞 F) => (lambdaGen v Q₀)⁻¹) (∏' v, (lambdaGen v Q₀)⁻¹) :=
    (multipliable_of_hasFiniteMulSupport (hasFiniteMulSupport_lambdaGen Q₀ hQ).inv).hasProd
  have hG : HasProd (fun v : HeightOneSpectrum (𝓞 F) => xiGen (normQ v) n (chiK v Q₀))
      (xiGenVal F n (fun v => chiK v Q₀)) := by
    unfold xiGenVal; exact hasProd_xiGen hn Q₀
  have hξ := hG.mul hΛ
  have h := hI.mul hξ
  have e : (fun v : HeightOneSpectrum (𝓞 F) =>
      dualIndexAt v Q₀ * (xiGen (normQ v) n (chiK v Q₀) * (lambdaGen v Q₀)⁻¹)) =
      fun v => NF.siegelDensity v Q₀ Q₀ := by
    funext v
    rw [siegelDensity_eq_gen v hn Q₀ hQ hmax, xiGen_local_gen v hn Q₀ hQ hmax, mul_comm (lambdaGen v Q₀), mul_assoc,
      mul_inv_cancel₀ (lambdaGen_pos v hn Q₀ hQ hmax).ne', mul_one]
  rw [← e, h.tprod_eq, tprod_inv_lambdaGen Q₀ hQ]

open Classical in
/-- **The right side of Theorem 5.1 without Shimura's hypothesis** (Hanke thesis, pp. 16–17, with $\lambda'_v$ = `lambdaGen`
for $\lambda_v$; GHY 2001, Table 4): `theorem51RHS` with $\prod_v\lambda_v$ replaced by $\prod_v\lambda'_v$. -/
@[kb "hanke2005crelle" "Theorem 5.1, pp. 16–17 (right side), with GHY 2001 Table 4's local factors at the places excluded by Shimura's hypothesis"]
def theorem51RHSGen (Q₀ : QuadForm (𝓞 F) n) : ℝ :=
  let d := Module.finrank ℚ F
  let D := |(discr F : ℝ)|
  2 * D ^ ((n - 1) ^ 2 / 4) *
    (∏ j ∈ Finset.range ((n - 1) / 2), (D ^ (1 / 2 : ℝ) *
      ((Nat.factorial (2 * (j + 1) - 1) : ℝ) / (2 * π) ^ (2 * (j + 1))) ^ d *
        NFEuler.dedekindZetaR F (2 * ((j : ℝ) + 1)))) *
    (∏' v, dualIndexAt v Q₀) ^ (((n : ℝ) - 1) / 2) * (∏' v, lambdaGen v Q₀) *
    (∏ w : {w : InfinitePlace F // w.IsReal}, bPhi n (rAt Q₀ w)) *
    ((2 : ℝ) ^ (-(((n : ℝ) - 1) * (n - 2)) / 2) * π ^ ((n : ℝ) * (n + 1) / 4) *
      ∏ l ∈ Finset.range n, (Gamma (((l : ℝ) + 1) / 2))⁻¹) ^ InfinitePlace.nrComplexPlaces F *
    (if Odd n then (2 : ℝ) ^ (-(((n : ℝ) - 1) / 2) * d)
      else D ^ (1 / 2 : ℝ) * ((Nat.factorial (n / 2 - 1) : ℝ) * (2 * π) ^ (-((n : ℝ) / 2))) ^ d *
        NFEuler.LFunctionNF (fun v => chiK v Q₀) ((n : ℝ) / 2))

open Classical in
theorem rhs_identity_gen (hn : 3 ≤ n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) :
    theorem51RHSGen Q₀ =
      2 * (|(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4) *
        (((2 : ℝ) ^ (Module.finrank ℚ F * (n * (n - 1) / 2)))⁻¹ * ∏' v, NF.siegelDensity v Q₀ Q₀)⁻¹) /
        ∏ w, volCAt Q₀ w := by
  rw [tprod_siegelDensity_eq_gen hn Q₀ hQ hmax, div_eq_mul_inv, prod_volCAt_inv Q₀ hQ, prod_B,
    ← tprod_dualIndexAt Q₀ hQ]
  have hI := tprod_dualIndexAt_pos Q₀ hQ
  have hΛ := tprod_lambdaGen_pos hn Q₀ hQ hmax
  have hG : xiGenVal F n (fun v => chiK v Q₀) = if Odd n then ∏ i ∈ Finset.range (n / 2), (NFEuler.dedekindZetaR F (2 * ((i : ℝ) + 1)))⁻¹
  else (NFEuler.LFunctionNF (fun v => chiK v Q₀) ((n / 2 : ℕ) : ℝ))⁻¹ *
         ∏ i ∈ Finset.range (n / 2 - 1), (NFEuler.dedekindZetaR F (2 * ((i : ℝ) + 1)))⁻¹ := rfl
  unfold theorem51RHSGen
  dsimp only
  rw [hG]
  generalize ∏' v, dualIndexAt v Q₀ = I at *
  generalize ∏' v, lambdaGen v Q₀ = Λ at *
  generalize (∏ w : {w : InfinitePlace F // w.IsReal}, bPhi n (rAt Q₀ w)) = B
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hk1 : 1 ≤ k := by omega
    have hodd : ¬ Odd (2 * (k + 1)) := by
      rw [Nat.not_odd_iff_even]; exact ⟨k + 1, by ring⟩
    simp only [hodd, ite_false]
    have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    have e2 : (2 * k + 1) ^ 2 / 4 = k ^ 2 + k := by
      rw [show (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 by ring]; omega
    have e3 : (2 * k + 1) / 2 = k := by omega
    have e4 : (2 * (k + 1)) / 2 = k + 1 := by omega
    have e5 : k + 1 - 1 = k := by omega
    have hL : (((2 * (k + 1) : ℕ) : ℝ)) / 2 = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
    simp only [e1, e2, e3, e4, e5, hL]
    rw [inv_tauR_even (m := k + 1) (by omega), e5]
    have hD : 0 < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero F)
    have hZ : ∀ i : ℕ, 0 < NFEuler.dedekindZetaR F (2 * ((i : ℝ) + 1)) := fun i =>
      lt_of_lt_of_le one_pos (NFEuler.one_le_dedekindZetaR (by have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith))
    have hLpos : 0 < NFEuler.LFunctionNF (fun v => chiK v Q₀) ((k + 1 : ℕ) : ℝ) :=
      NFEuler.LFunctionNF_pos (fun v => abs_chiK_le v Q₀) (by
        have : (2 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ k + 1)
        linarith)
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      Finset.prod_pow]
    simp only [Finset.prod_inv_distrib]
    have hX : 0 < (((2 : ℝ) ^ Module.finrank ℚ F) ^ (2 * (k + 1))) ^ ((((2 * (k + 1) : ℕ) : ℝ) + 1) / 2) := by
      positivity
    have fI : (I / ((2 : ℝ) ^ Module.finrank ℚ F) ^ (2 * (k + 1))) ^ ((((2 * (k + 1) : ℕ) : ℝ) + 1) / 2) =
        I ^ ((((2 * (k + 1) : ℕ) : ℝ) - 1) / 2) * I /
          (((2 : ℝ) ^ Module.finrank ℚ F) ^ (2 * (k + 1))) ^ ((((2 * (k + 1) : ℕ) : ℝ) + 1) / 2) := by
      rw [Real.div_rpow hI.le (by positivity)]
      congr 1
      rw [show (((2 * (k + 1) : ℕ) : ℝ) + 1) / 2 = (((2 * (k + 1) : ℕ) : ℝ) - 1) / 2 + 1 by ring,
        Real.rpow_add hI, Real.rpow_one]
    have fD : |(discr F : ℝ)| ^ (((2 * (k + 1) : ℕ) : ℝ) * (((2 * (k + 1) : ℕ) : ℝ) - 1) / 4) =
        |(discr F : ℝ)| ^ (k ^ 2 + k) * (|(discr F : ℝ)| ^ (1 / 2 : ℝ)) ^ k * |(discr F : ℝ)| ^ (1 / 2 : ℝ) := by
      rw [show (((2 * (k + 1) : ℕ) : ℝ) * (((2 * (k + 1) : ℕ) : ℝ) - 1) / 4) =
          ((k ^ 2 + k : ℕ) : ℝ) + (1 / 2) * (k : ℝ) + 1 / 2 by push_cast; ring,
        Real.rpow_add hD, Real.rpow_add hD, Real.rpow_natCast, Real.rpow_mul hD.le, Real.rpow_natCast]
    have h2 := two_part (Module.finrank ℚ F) (2 * (k + 1))
    simp only [e1] at h2
    have ha : (2 : ℝ) ^ (Module.finrank ℚ F * (2 * (k + 1) * (2 * k + 1) / 2)) =
        ((2 : ℝ) ^ (Module.finrank ℚ F * (2 * (k + 1))))⁻¹ *
          (((2 : ℝ) ^ Module.finrank ℚ F) ^ (2 * (k + 1))) ^ ((((2 * (k + 1) : ℕ) : ℝ) + 1) / 2) := by
      rw [div_eq_iff hX.ne'] at h2
      exact h2
    have hsq : ((2 : ℝ) ^ (2 * (k + 1))) ^ Module.finrank ℚ F =
        (2 : ℝ) ^ (Module.finrank ℚ F * (2 * (k + 1))) := by
      rw [← pow_mul, mul_comm]
    rw [fD, fI, ha, ← hsq]
    have hZp : 0 < ∏ x ∈ Finset.range k, NFEuler.dedekindZetaR F (2 * ((x : ℝ) + 1)) :=
      Finset.prod_pos fun i _ => hZ i
    generalize (∏ x ∈ Finset.range k, NFEuler.dedekindZetaR F (2 * ((x : ℝ) + 1))) = Zp at *
    generalize (∏ j ∈ Finset.range k, ((Nat.factorial (2 * (j + 1) - 1) : ℝ) / (2 * π) ^ (2 * (j + 1)))) = Fp
    generalize ((((2 : ℝ) ^ Module.finrank ℚ F) ^ (2 * (k + 1))) ^ ((((2 * (k + 1) : ℕ) : ℝ) + 1) / 2)) = X at *
    generalize NFEuler.LFunctionNF (fun v => chiK v Q₀) ((k + 1 : ℕ) : ℝ) = L at *
    have h2p : (0 : ℝ) < 2 ^ (2 * (k + 1)) := by positivity
    generalize ((2 : ℝ) ^ (2 * (k + 1))) = T at *
    have hTd : 0 < T ^ Module.finrank ℚ F := by positivity
    field_simp
    ring
  · have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
    have hm1 : 1 ≤ m := by omega
    simp only [hodd, ite_true]
    have e1 : 2 * m + 1 - 1 = 2 * m := by omega
    have e2 : (2 * m) ^ 2 / 4 = m ^ 2 := by
      rw [show (2 * m) ^ 2 = 4 * m ^ 2 by ring]; omega
    have e3 : (2 * m) / 2 = m := by omega
    have e4 : (2 * m + 1) / 2 = m := by omega
    simp only [e1, e2, e3, e4]
    rw [inv_tauR_odd]
    have hD : 0 < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero F)
    have hZ : ∀ i : ℕ, 0 < NFEuler.dedekindZetaR F (2 * ((i : ℝ) + 1)) := fun i =>
      lt_of_lt_of_le one_pos (NFEuler.one_le_dedekindZetaR (by have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith))
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      Finset.prod_pow]
    simp only [Finset.prod_inv_distrib]
    have hX : 0 < (((2 : ℝ) ^ Module.finrank ℚ F) ^ (2 * m + 1)) ^ ((((2 * m + 1 : ℕ) : ℝ) + 1) / 2) := by positivity
    have fI : (I / ((2 : ℝ) ^ Module.finrank ℚ F) ^ (2 * m + 1)) ^ ((((2 * m + 1 : ℕ) : ℝ) + 1) / 2) =
        I ^ (m + 1) / (((2 : ℝ) ^ Module.finrank ℚ F) ^ (2 * m + 1)) ^ ((((2 * m + 1 : ℕ) : ℝ) + 1) / 2) := by
      rw [Real.div_rpow hI.le (by positivity)]
      congr 1
      rw [show (((2 * m + 1 : ℕ) : ℝ) + 1) / 2 = ((m + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    have fIexp : I ^ ((((2 * m + 1 : ℕ) : ℝ) - 1) / 2) = I ^ m := by
      rw [show (((2 * m + 1 : ℕ) : ℝ) - 1) / 2 = (m : ℝ) by push_cast; ring, Real.rpow_natCast]
    have fD : |(discr F : ℝ)| ^ (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) - 1) / 4) =
        |(discr F : ℝ)| ^ (m ^ 2) * (|(discr F : ℝ)| ^ (1 / 2 : ℝ)) ^ m := by
      rw [show (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) - 1) / 4) = ((m ^ 2 : ℕ) : ℝ) + (1 / 2) * (m : ℝ) by
        push_cast; ring, Real.rpow_add hD, Real.rpow_natCast, Real.rpow_mul hD.le, Real.rpow_natCast]
    have f2 : (2 : ℝ) ^ (-((((2 * m + 1 : ℕ) : ℝ) - 1) / 2) * (Module.finrank ℚ F : ℝ)) =
        ((2 : ℝ) ^ (m * Module.finrank ℚ F))⁻¹ := by
      rw [show -((((2 * m + 1 : ℕ) : ℝ) - 1) / 2) * (Module.finrank ℚ F : ℝ) = -((m * Module.finrank ℚ F : ℕ) : ℝ) by
        push_cast; ring, Real.rpow_neg (by norm_num), Real.rpow_natCast]
    have h2 := two_part (Module.finrank ℚ F) (2 * m + 1)
    simp only [e1] at h2
    have ha : (2 : ℝ) ^ (Module.finrank ℚ F * ((2 * m + 1) * (2 * m) / 2)) =
        ((2 : ℝ) ^ (Module.finrank ℚ F * (2 * m + 1)))⁻¹ *
          (((2 : ℝ) ^ Module.finrank ℚ F) ^ (2 * m + 1)) ^ ((((2 * m + 1 : ℕ) : ℝ) + 1) / 2) := by
      rw [div_eq_iff hX.ne'] at h2
      exact h2
    have hsq : ((2 : ℝ) ^ (m + 1)) ^ Module.finrank ℚ F * (2 : ℝ) ^ (m * Module.finrank ℚ F) =
        (2 : ℝ) ^ (Module.finrank ℚ F * (2 * m + 1)) := by
      rw [← pow_mul, ← pow_add]; congr 1; ring
    rw [fD, fI, fIexp, f2, ha, ← hsq]
    have hZp : 0 < ∏ x ∈ Finset.range m, NFEuler.dedekindZetaR F (2 * ((x : ℝ) + 1)) :=
      Finset.prod_pos fun i _ => hZ i
    generalize (∏ x ∈ Finset.range m, NFEuler.dedekindZetaR F (2 * ((x : ℝ) + 1))) = Zp at *
    generalize (∏ j ∈ Finset.range m, ((Nat.factorial (2 * (j + 1) - 1) : ℝ) / (2 * π) ^ (2 * (j + 1)))) = Fp
    generalize ((((2 : ℝ) ^ Module.finrank ℚ F) ^ (2 * m + 1)) ^ ((((2 * m + 1 : ℕ) : ℝ) + 1) / 2)) = X at *
    have h2p : (0 : ℝ) < 2 ^ (m + 1) := by positivity
    have h2q : (0 : ℝ) < 2 ^ (m * Module.finrank ℚ F) := by positivity
    generalize ((2 : ℝ) ^ (m + 1)) = s at *
    generalize ((2 : ℝ) ^ (m * Module.finrank ℚ F)) = q at *
    field_simp
    ring

/-- **Under Shimura's hypothesis the two right sides agree.** -/
theorem theorem51RHSGen_eq (Q₀ : QuadForm (𝓞 F) n) (hdet : ShimuraDetHyp Q₀) : theorem51RHSGen Q₀ = theorem51RHS Q₀ := by
  have e : (fun v : HeightOneSpectrum (𝓞 F) => lambdaGen v Q₀) = fun v => lambdaAt v Q₀ :=
    funext fun v => lambdaGen_eq_of_hyp v Q₀ hdet
  unfold theorem51RHSGen theorem51RHS
  rw [e]

/-- **Theorem 5.1 without Shimura's hypothesis** (Hanke thesis, Theorem 5.1, pp. 16–19, with the local factors of GHY 2001,
Table 4, at the places excluded by Shimura's hypothesis): for $n\ge3$ and $Q_0$ nondegenerate over $\mathcal O_F$ (any number
field, any signature) with $\Lambda = \mathcal O_F^n$ maximal, Hanke's mass is `theorem51RHSGen`. **Unconditional:** no named
input and no hypothesis on $\det\varphi$. -/
@[kb "hanke2005crelle" "Theorem 5.1, pp. 16–19, without Shimura's hypothesis (local factors from GHY 2001, Table 4)"]
theorem theorem51_general (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) :
    hankeMass Q₀ hQ = ENNReal.ofReal (theorem51RHSGen Q₀) := by
  have hP := tprod_siegelDensity_pos hn Q₀ hQ
  have hT : 0 < ∏ w, volCAt Q₀ w := Finset.prod_pos fun w _ => volCAt_pos Q₀ hQ w
  unfold hankeMass
  rw [theorem21_tau_two Q₀ hQ hn, tprod_hankeBeta Q₀ hQ (by omega) (by omega), rhs_identity_gen hn Q₀ hQ hmax]
  have hX : 0 ≤ |(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4) *
        (((2 : ℝ) ^ (Module.finrank ℚ F * (n * (n - 1) / 2)))⁻¹ * ∏' v, NF.siegelDensity v Q₀ Q₀)⁻¹ := by
    positivity
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_div_of_pos hT]

/-- **Theorem 5.1 (with Shimura's hypothesis) from the general version**, unconditional: `theorem51`'s conclusion with no
named input. -/
@[kb "hanke2005crelle" "Theorem 5.1, pp. 16–19 (with Shimura's hypothesis; derived from the general version)"]
theorem theorem51_of_general (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀)
    (hdet : ShimuraDetHyp Q₀) : hankeMass Q₀ hQ = ENNReal.ofReal (theorem51RHS Q₀) := by
  rw [theorem51_general hn Q₀ hQ hmax, theorem51RHSGen_eq Q₀ hdet]

/-- **Theorem 5.1 without Shimura's hypothesis, totally definite case** (Hanke thesis, Theorem 5.1, Part 1, pp. 17–18; GHY
2001, Table 4): $F$ totally real, $Q_0$ totally positive definite, $\mathcal O_F^n$ maximal, $n\ge3$:
$\sum_a[\Gamma_a:1]^{-1} = $ `theorem51RHSGen`. Unconditional. -/
@[kb "hanke2005crelle" "Theorem 5.1, Part 1, pp. 17–18 (totally definite), without Shimura's hypothesis"]
theorem theorem51_definite_general [IsTotallyReal F] (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) (hmax : StdIsMaximal Q₀) :
    ∑' i : DC Q₀, ((Nat.card (unitGroup Q₀ i) : ℝ≥0∞))⁻¹ = ENNReal.ofReal (theorem51RHSGen Q₀) := by
  rw [← hankeMass_definite (by omega) Q₀ hQ hpd]
  exact theorem51_general hn Q₀ hQ hmax

end QuadFormsKB.Hanke2005
