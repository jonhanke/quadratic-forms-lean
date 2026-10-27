/-
# Siegel's formula with an isotropic rank-2 complement, regularized, every number field

**Layer:** number fields. $F$ **any** number field, $Q_0$ a nondegenerate quadratic form over $\mathcal O_F$ in $N = r + 2$
variables of any signature, $L = \mathcal O_F^N$, $T_0$ nondegenerate of rank $r\ge1$ with a rational frame $\Xi$
($Q_0\circ\Xi = T_0$), and the complement $W = \Xi^\perp$ **isotropic**:
$$\delta = -\det H_{Q_0}\det H_{T_0}\ (\texttt{deltaForms Q₀ T₀})\ \text{is a square in }F$$
(`complAnisotropic_iff`: this is the isotropy of $W$, for every rational frame). Then $SO(W)\cong\mathbb G_m$, every
classical stabilizer volume $\operatorname{vol}(\Gamma_{i,X}\backslash H_X)$ is infinite (Siegel excludes this case), and the
formula holds for the **norm-one** stabilizers.

**Headline** (`siegelIndefiniteForms_rank2_isotropic_uncond`, unconditional):
$$2\,c_\infty(T_0)\sum_i\rho^1(M_i, T_0) = |d_F|^{-(N(N-1)-2)/4}\,\rho_F\prod_\mathfrak p\beta_\mathfrak p(L,T_0)\Bigl(1-\frac1{N\mathfrak p}\Bigr)
  \cdot\sum_iv(M_i),$$
* $\rho^1$ = `repMeasureIso`: $\sum_{X\in\Gamma_i\backslash R(M_i,T_0)}\operatorname{vol}(\Gamma_{i,X}\backslash H^1_X)$, the stabilizer
  measure at $\Xi$ being the ($\prod_{w\mid\infty}|\det g|_w^3/c_F(2)$ times Weil's archimedean measure of $SO(Q'')$,
  transported)
  restricted to the shell $\{0\le\log|\chi|_\infty<1\}$ (`isoStabMeasure`);
* $\rho_F = \operatorname{Res}_{s=1}\zeta_F(s)$ (`dedekindZeta_residue`), the factors $1 - N\mathfrak p^{-1} = \zeta_{F,\mathfrak p}(1)^{-1}$
  (`lamV`): the local side is `isoDensityProductReg`, the product converging absolutely
  (`multipliable_localDensityForm_iso`);
* $c_\infty(T_0)$ = `cInfTNF` (as in the rank-2 case), $v(M_i)$ = `unitVolume`;
* the factor $2 = \tau(SO(V))/\tau^1(SO(W))$ ($\tau(SO(V)) = 2$, `tauTwoAll_release_uncond`; $\tau^1(\mathbb G_m) = 1$,
  `tauOne_binary_isotropic_uncond`).

**Proof.** The dictionary (`tsum_repMeasureIso`), the torus lemma for each orbit stabilizer (`tauIso_eq_tsum_DCq`), the orbit
sum with $\lambda_v = 1 - Nv^{-1}$ (`IsoAlg.frameOrbitSum_lam`), $\mu_f(K)\sum_iv(M_i) = \tau(SO(V)) = 2$, and the product
formula (`IsoAlg.frameDensity_identity_lam`).
-/
import QuadFormsKB.Tamagawa.Indefinite.IsoDictionary
import QuadFormsKB.Tamagawa.Indefinite.IsoHyps
import QuadFormsKB.Tamagawa.Indefinite.IsoIdentityAlg

open MeasureTheory Set Matrix MulAction Filter
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames LocalDensity

variable {F : Type} [Field F] [NumberField F] {r : ℕ}

/-! ### The regularized local side -/

/-- **The local side with an isotropic rank-2 complement, regularized**:
$|d_F|^{-(N(N-1)-2)/4}\,\rho_F\prod_\mathfrak p\beta_\mathfrak p(L,T_0)\,(1 - N\mathfrak p^{-1})$ ($N = r + 2$,
$\rho_F = \operatorname{Res}_{s=1}\zeta_F(s)$ = `dedekindZeta_residue F`, $1 - N\mathfrak p^{-1}$ = `lamV`,
$\beta_\mathfrak p$ = `NF.localDensityForm v Q₀ T₀`). This is `regProd χ 1 β` for the trivial character, with the
divergent $L(1,\mathbf 1)$ replaced by its residue. -/
@[kb "siegel1944indef" "local side, complement of rank 2 with square determinant, regularized by Res ζ_F and the factors ζ_{F,p}(1)⁻¹ [unverified]"]
def isoDensityProductReg (Q₀ : QuadForm (𝓞 F) (r + 2)) (T₀ : QuadForm (𝓞 F) r) : ℝ :=
  |(discr F : ℝ)| ^ (-(((r + 2 : ℕ) : ℝ) * ((r + 2 : ℕ) - 1) - 2) / 4) * dedekindZeta_residue F *
    ∏' v, NF.localDensityForm v Q₀ T₀ * lamV v

variable (Q₀ : QuadForm (𝓞 F) (r + 2)) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r)
  (hT : T₀.Nondegenerate) (hiso : IsSquare (algebraMap (𝓞 F) F (deltaForms Q₀ T₀))) (Ξ : RatFrame Q₀ T₀)

local notation "𝔇" => isoTower Q₀ hQ T₀ hT Ξ
local notation "𝔢" => isIsoVec_isoVec Q₀ hQ T₀ hT hiso Ξ

/-! ### Countability -/

instance countable_repsT (i : DC Q₀) : Countable (repsT Q₀ T₀ i) :=
  ((Set.countable_range (ratAT Q₀ T₀)).mono (Set.image_subset_range _ _)).to_subtype

instance countable_RepIdx : Countable (RepIdx Q₀ T₀) := by
  haveI : ∀ i : DC Q₀, Countable (orbitRel.Quotient (unitGroup Q₀ i) (repsT Q₀ T₀ i)) := fun i =>
    Quotient.countable
  infer_instance

include hiso in
theorem countable_DCq_isoU (O : FinOrbit Q₀ T₀ Ξ) : Countable (DCq (𝔇).Q'' (isoU Q₀ hQ T₀ hT Ξ O)) :=
  (isoPsi_surjective Q₀ hQ T₀ hT hiso Ξ O).countable

/-! ### The torus lemma for the orbit stabilizers -/

/-- **The norm-one covolumes of an orbit stabilizer**: $\sum_c\texttt{isoCov}(U_O) = \rho_F/\mu^\lambda_f(U_O)$
(the torus lemma with $\tau^1 = 1$). -/
theorem tsum_isoCov (O : FinOrbit Q₀ T₀ Ξ) :
    ∑' _c : DCq (𝔇).Q'' (isoU Q₀ hQ T₀ hT Ξ O), isoCov Q₀ hQ T₀ hT hiso Ξ (isoU Q₀ hQ T₀ hT Ξ O) =
      ENNReal.ofReal (dedekindZeta_residue F) / muFin (𝔇).Q'' lamV (isoU Q₀ hQ T₀ hT Ξ O) := by
  haveI := countable_DCq_isoU Q₀ hQ T₀ hT hiso Ξ O
  set U := isoU Q₀ hQ T₀ hT Ξ O with hU
  have hτ := tauIso_eq_tsum_DCq (𝔇).Q'' (𝔇).hQ'' 𝔢 U (measurableSet_orbitStab_iso Q₀ hQ T₀ hT Ξ O)
    (fun u hu => isoNormFin_orbitStab Q₀ hQ T₀ hT hiso Ξ _ u hu)
    (fun b => discreteTopology_levelGroup_orbitStab Q₀ hQ T₀ hT Ξ _ b)
  rw [tauIso_of_comparison (isoComparison_of_isotropic (𝔇).hQ'' 𝔢)] at hτ
  have hlev : ∀ c : DCq (𝔇).Q'' U, covolume (levelGroup (GammaSOAdele (𝔇).Q'') U (dcqRep (𝔇).Q'' U c))
      (GInfSO (𝔇).Q'') ((muArchTamSO (𝔇).Q'' (𝔇).hQ'').restrict (isoShellInf (𝔇).Q'' (𝔇).hQ'' 𝔢)) =
      isoCov Q₀ hQ T₀ hT hiso Ξ U := fun c => by
    rw [isoCov, levelGroup_eq_one (𝔇).Q'' (𝔇).hQ'' 𝔢 U]
  simp_rw [hlev] at hτ
  set S := ∑' _c : DCq (𝔇).Q'' U, isoCov Q₀ hQ T₀ hT hiso Ξ U
  set m := muFin (𝔇).Q'' lamV U
  have hm0 : m ≠ 0 := muFin_orbitStab_iso_ne_zero Q₀ hQ T₀ hT Ξ O
  have hmt : m ≠ ⊤ := muFin_orbitStab_iso_ne_top Q₀ hQ T₀ hT Ξ O
  have hρ := dedekindZeta_residue_pos F
  have ha0 : ENNReal.ofReal (dedekindZeta_residue F)⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hρ)).ne'
  have hinv : (ENNReal.ofReal (dedekindZeta_residue F)⁻¹)⁻¹ = ENNReal.ofReal (dedekindZeta_residue F) := by
    rw [← ENNReal.ofReal_inv_of_pos (inv_pos.2 hρ), inv_inv]
  have hS : S = (ENNReal.ofReal (dedekindZeta_residue F)⁻¹ * m)⁻¹ :=
    ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hτ.symm)
  rw [hS, ENNReal.mul_inv (Or.inl ha0) (Or.inl ENNReal.ofReal_ne_top), hinv, div_eq_mul_inv]

/-! ### Weil's form and the headline -/

include hiso in
/-- **Weil's form**: $2\sum_i\rho^1(M_i,T_0) = \lambda\,\rho_F\prod_\mathfrak p(\text{orbit factors})\,\lambda_\mathfrak p\cdot\sum_iv(M_i)$
($\tau(SO(V)) = 2$, $\tau^1(SO(W)) = 1$). -/
theorem two_mul_tsum_repMeasureIso (hr : 1 ≤ r) :
    2 * ∑' i, repMeasureIso Q₀ hQ T₀ hT hiso Ξ i =
      isoFrameLam Q₀ hQ T₀ hT Ξ * ENNReal.ofReal (dedekindZeta_residue F) *
        (ENNReal.ofReal (∏' v, IsoAlg.frameLocFactor Q₀ hQ T₀ Ξ (𝔇) hT v * lamV v) * ∑' i, unitVolume Q₀ hQ i) := by
  have hN : 3 ≤ r + 2 := by omega
  have hdict := tsum_repMeasureIso Q₀ hQ T₀ hT hiso Ξ
    (fun b u hu => isoNormFin_orbitStab Q₀ hQ T₀ hT hiso Ξ b u hu)
    (fun b c => discreteTopology_levelGroup_orbitStab Q₀ hQ T₀ hT Ξ b c)
  simp_rw [tsum_isoCov Q₀ hQ T₀ hT hiso Ξ, div_eq_mul_inv, ENNReal.tsum_mul_left] at hdict
  have hFOS := IsoAlg.frameOrbitSum_lam Q₀ hQ T₀ Ξ (𝔇) hT lamV lamV_pos
    (multipliable_muLocSO_lamV_iso Q₀ hQ T₀ hT hiso Ξ) (finFactor_lamV_iso_pos Q₀ hQ T₀ hT hiso Ξ) (by norm_num) hN
  rw [IsoAlg.frameOrbitSumLam] at hFOS
  simp_rw [div_eq_mul_inv, ENNReal.tsum_mul_left] at hFOS
  have hτ : covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) = 2 :=
    tauTwoAll_release_uncond (r + 2) hN Q₀ hQ
  rw [covolume_eq_muFin_mul_tsum_unitVolume Q₀ hQ] at hτ
  set A := ∑' O : FinOrbit Q₀ T₀ Ξ, (muFin (𝔇).Q'' lamV (isoU Q₀ hQ T₀ hT Ξ O))⁻¹ with hA
  have hA' : ∑' O : FinOrbit Q₀ T₀ Ξ, (muFin (𝔇).Q'' lamV
      (orbitStab (𝔇).ιFin (KSO Q₀) (finOrbitRep Q₀ T₀ Ξ O)))⁻¹ = A := rfl
  rw [hA'] at hFOS
  rw [hdict, ← hFOS, ← hτ]
  ring

include hiso in
/-- The product of the local factors with the convergence factors converges absolutely. -/
theorem multipliable_frameLocFactor_iso (hr : 1 ≤ r) :
    Multipliable fun v => IsoAlg.frameLocFactor Q₀ hQ T₀ Ξ (𝔇) hT v * lamV v :=
  IsoAlg.multipliable_frameLocFactor_lam Q₀ hQ T₀ Ξ (𝔇) hT lamV lamV_pos
    (multipliable_muLocSO_lamV_iso Q₀ hQ T₀ hT hiso Ξ) (finFactor_lamV_iso_pos Q₀ hQ T₀ hT hiso Ξ) (by norm_num)
    (by omega)

include hQ hT hiso Ξ in
/-- **The regularized product converges absolutely**: $\prod_\mathfrak p\beta_\mathfrak p(L,T_0)(1 - N\mathfrak p^{-1})$. -/
theorem multipliable_localDensityForm_iso (hr : 1 ≤ r) :
    Multipliable fun v => NF.localDensityForm v Q₀ T₀ * lamV v := by
  classical
  have hm := multipliable_frameLocFactor_iso Q₀ hQ T₀ hT hiso Ξ hr
  set g := (IsoAlg.towerAdapted Q₀ hQ T₀ Ξ (𝔇) hT).g.val.det with hgdef
  set h := algebraMap (𝓞 F) F T₀.hessian.det with hhdef
  have hg : g ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)).ne_zero
  have hh : h ≠ 0 := algebraMap_det_ne_zero T₀ hT
  have ha : ∀ v : HeightOneSpectrum (𝓞 F), ‖σV v g‖ ≠ 0 := fun v => norm_ne_zero_iff.2 ((map_ne_zero _).2 hg)
  have hb : ∀ v : HeightOneSpectrum (𝓞 F), ‖σV v h‖ ≠ 0 := fun v => norm_ne_zero_iff.2 ((map_ne_zero _).2 hh)
  have hfa := mulSupport_finite_norm (F := F) hg
  have hfb := mulSupport_finite_norm (F := F) hh
  set u : HeightOneSpectrum (𝓞 F) → ℝ := fun v => ‖σV v h‖ ^ 2 * (‖σV v g‖ ^ (2 + 1))⁻¹ with hu
  have hufin : (Function.mulSupport u).Finite := by
    refine (hfa.union hfb).subset fun v hv => ?_
    by_contra hcon
    apply hv
    simp only [Set.mem_union, Function.mem_mulSupport, not_or, not_not] at hcon
    show u v = 1
    simp only [hu, hcon.1, hcon.2, one_pow, inv_one, one_mul]
  have hβ : (fun v => NF.localDensityForm v Q₀ T₀ * lamV v) =
      fun v => (IsoAlg.frameLocFactor Q₀ hQ T₀ Ξ (𝔇) hT v * lamV v) * u v := by
    funext v
    have := ha v
    have := hb v
    simp only [IsoAlg.frameLocFactor, hu]
    rw [← hgdef, ← hhdef]
    field_simp
  rw [hβ]
  exact hm.mul (multipliable_of_hasFiniteMulSupport hufin)

include hiso in
/-- **Siegel's formula for forms by forms with an isotropic rank-2 complement, regularized** (indefinite, any signature,
every number field; Siegel's excluded case): for $Q_0$ nondegenerate in $N = r + 2$ variables, $T_0$ nondegenerate of rank
$r\ge1$ with a rational frame $\Xi$, and $\delta = -\det H_{Q_0}\det H_{T_0}$ a square in $F$ (the complement of $\Xi$ is
isotropic, $SO(W)\cong\mathbb G_m$),
$$2\,c_\infty(T_0)\sum_i\rho^1(M_i,T_0) = |d_F|^{-(N(N-1)-2)/4}\,\rho_F\prod_\mathfrak p\beta_\mathfrak p(L,T_0)
  \Bigl(1-\frac1{N\mathfrak p}\Bigr)\cdot\sum_iv(M_i),$$
with $\rho^1$ the measures of representations for the norm-one stabilizers $H^1_X = \ker|\chi_X|_\infty$ (`repMeasureIso`),
$\rho_F = \operatorname{Res}_{s=1}\zeta_F(s)$, and $2 = \tau(SO(V))/\tau^1(SO(W))$. Unconditional. -/
@[kb "siegel1944indef" "On the theory of indefinite quadratic forms, the case n - m = 2 with square determinant (excluded there), regularized with norm-one stabilizers [unverified]"]
theorem siegelIndefiniteForms_rank2_isotropic_uncond (hr : 1 ≤ r) :
    2 * (cInfTNF Q₀ T₀ * ∑' i, repMeasureIso Q₀ hQ T₀ hT hiso Ξ i) =
      ENNReal.ofReal (isoDensityProductReg Q₀ T₀) * ∑' i, unitVolume Q₀ hQ i := by
  classical
  have hρ := dedekindZeta_residue_pos F
  have hm := multipliable_frameLocFactor_iso Q₀ hQ T₀ hT hiso Ξ hr
  have hid := IsoAlg.frameDensity_identity_lam Q₀ hQ T₀ Ξ (𝔇) hT lamV hm
  have hreg : isoDensityProductReg Q₀ T₀ = dedekindZeta_residue F *
      (|(discr F : ℝ)| ^ (-(((r + 2 : ℕ) : ℝ) * ((r + 2 : ℕ) - 1) - ((2 : ℕ) : ℝ) * ((2 : ℕ) - 1)) / 4) *
        ∏' v, NF.localDensityForm v Q₀ T₀ * lamV v) := by
    rw [isoDensityProductReg]
    norm_num
    ring
  have key : cInfTNF Q₀ T₀ * isoFrameLam Q₀ hQ T₀ hT Ξ * ENNReal.ofReal (dedekindZeta_residue F) *
      ENNReal.ofReal (∏' v, IsoAlg.frameLocFactor Q₀ hQ T₀ Ξ (𝔇) hT v * lamV v) =
      ENNReal.ofReal (isoDensityProductReg Q₀ T₀) := by
    rw [hreg, ← hid]
    unfold cInfTNF isoFrameLam
    have hnn : ∀ w : {w : InfinitePlace F // w.IsReal},
        0 ≤ (|σR w (algebraMap (𝓞 F) F T₀.hessian.det)| ^ 2)⁻¹ := fun w => by positivity
    have hnnC : ∀ w : {w : InfinitePlace F // w.IsComplex},
        0 ≤ (‖σC w (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ (2 * 2))⁻¹ := fun w => by positivity
    have hnn2 : 0 ≤ (∏ w : {w : InfinitePlace F // w.IsReal}, (|σR w (algebraMap (𝓞 F) F T₀.hessian.det)| ^ 2)⁻¹) :=
      Finset.prod_nonneg fun w _ => hnn w
    have hnn2C : 0 ≤ (∏ w : {w : InfinitePlace F // w.IsComplex},
        (‖σC w (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ (2 * 2))⁻¹) := Finset.prod_nonneg fun w _ => hnnC w
    have hnn3 := mul_nonneg (cF_pos' (F := F) (r + 2)).le (mul_nonneg hnn2 hnn2C)
    have hlam : 0 ≤ (∏ w : {w : InfinitePlace F // w.IsReal},
        |σR w (IsoAlg.towerAdapted Q₀ hQ T₀ Ξ (𝔇) hT).g.val.det| ^ (2 + 1)) *
        (∏ w : {w : InfinitePlace F // w.IsComplex},
          ‖σC w (IsoAlg.towerAdapted Q₀ hQ T₀ Ξ (𝔇) hT).g.val.det‖ ^ (2 * (2 + 1))) / cF F 2 :=
      div_nonneg (mul_nonneg (Finset.prod_nonneg fun w _ => by positivity)
        (Finset.prod_nonneg fun w _ => by positivity)) (cF_pos' (F := F) 2).le
    rw [← ENNReal.ofReal_prod_of_nonneg (fun w _ => hnn w), ← ENNReal.ofReal_prod_of_nonneg (fun w _ => hnnC w),
      ← ENNReal.ofReal_mul hnn2, ← ENNReal.ofReal_mul (cF_pos' _).le,
      ← ENNReal.ofReal_mul hnn3, ← ENNReal.ofReal_mul (mul_nonneg hnn3 hlam),
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hnn3 hlam) hρ.le)]
    congr 1
    ring
  rw [mul_left_comm, two_mul_tsum_repMeasureIso Q₀ hQ T₀ hT hiso Ξ hr, ← key]
  ring

end QuadFormsKB.Tamagawa.Indefinite
