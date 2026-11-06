/-
# Hanke 2005, Theorem 2.1: the unit volumes of a genus and the local densities

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Setting.** $F$ a number field of degree $d$, $Q_0$ a nondegenerate quadratic form over $\mathcal O_F$ in $n$ variables of
**any signature**, $(V,\varphi) = (F^n, Q_0)$, $\Lambda = \mathcal O_F^n$ (the lattice spanned by the global basis
$e_0,\dots,e_{n-1}$), $\psi = \tfrac12H_{Q_0}$ the matrix of $\varphi$ in this basis (Hanke's Gram convention),
$G = SO(V)$, $G_a = SO(V)(F\otimes\mathbb R)$ (`GInfSO`). The classes $a\in\mathrm{Cl}$ of $\Lambda$ (Hanke §1: global
$G$-equivalence classes in the genus, parametrized by $G\backslash G_{\mathbb A}/D$) are the double cosets `DC Q₀` of
$SO(V)(F)\backslash SO(V)(\mathbb A_f)/SO(\hat\Lambda)$, and $\Gamma_a = G\cap aDa^{-1}$ is `unitGroup Q₀ a`, viewed in $G_a$.

**Hanke's archimedean measure** $\tau_a = \prod_{v\in a}|\widetilde\omega_G|'_v$ (§2, p. 5) is the gauge-form measure of
$\widetilde\omega_G = \omega_X/F^*\omega_T$ for $F(x) = {}^tx\psi x$, with Hanke's local measures $(d'x)_v$: Lebesgue measure at a
real place and $i\,dz\wedge d\bar z = 2\,dx\,dy$ at a complex place, on $X = M_n$ and on $T$ in the Gram coordinates
$t_{ij}$ ($i\le j$). The repository's Leray measure `muArchNF` uses Lebesgue measure ($dx\,dy$ at complex places) and the
coefficient coordinates $c_{ii} = t_{ii}$, $c_{ij} = 2t_{ij}$. Per real place the coordinate change contributes
$2^{n(n-1)/2}$; per complex place $|2|_{\mathbb C}^{n(n-1)/2} = 4^{n(n-1)/2}$ from the coordinates and
$2^{n^2 - n(n+1)/2} = 2^{n(n-1)/2}$ from $(d'x)_v$ (this is `cxWeil`). Hence
$$\tau_a = 2^{d\,n(n-1)/2}\cdot\texttt{cxWeil}\cdot\texttt{muArchNF} = 2^{d\,n(n-1)/2}\,|d_F|^{n(n-1)/4}\cdot\texttt{muArchTamSO}$$
(`muArchHanke`; $c_F = |d_F|^{-n(n-1)/4}$ = `cF`).

**Theorem 2.1** (`theorem21`): $\sum_{a\in\mathrm{Cl}}\tau_a(\Gamma_a\backslash G_a) = \tau(G)\,|D_k|^{n(n-1)/4}
\prod_{v\in h}\beta_v(\Lambda,\psi)^{-1}$ with $\tau(G)$ the Tamagawa number (Weil's covolume of $G(F)$ in
$G(\mathbb A)$, `muTam`) and Hanke's local densities $\beta_v$ (`hankeBeta`, Gram coordinates). With $\tau(G) = 2$ for
$n\ge3$ (Hanke's (2.1), proved in the repository: `tauTwoAll_release_uncond`), `theorem21_tau_two`. Both are
**unconditional**, for every number field and every signature. *Update (hypothesis):* the product
$\prod_v\beta_v$ converges absolutely only for $n\ne2$; the theorem is stated for $n\ge3$, the case of the paper.

Proof: the repository's decomposition $\tau(G) = \mu_f(SO(\hat\Lambda))\sum_av(M_a)$
(`covolume_eq_muFin_mul_tsum_unitVolume`), $\mu_f(SO(\hat\Lambda)) = \prod_v\alpha_v$ (`muFin_KSO`, `finFactor_one`), the comparison
$\beta_v = |2|_v^{n(n-1)/2}\alpha_v$ (`hankeBeta_gramV`) and the product formula $\prod_v|2|_v = 2^{-d}$ (`tprod_norm_two`).
-/
import QuadFormsKB.Tamagawa.Indefinite.SiegelIndefinite
import QuadFormsKB.Tamagawa.Measure.Weil.ReleaseHeadlines
import QuadFormsKB.Tamagawa.LocalOrbitalGlobal
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarGlobal
import QuadFormsKB.Literature.Hanke2005.LocalDensity

open MeasureTheory Measure NumberField IsDedekindDomain Filter
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.Tamagawa.Indefinite

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)

variable (F n) in
/-- The constant $2^{d\,n(n-1)/2}\,|d_F|^{n(n-1)/4}$ ($d = [F:\mathbb Q]$) relating Hanke's archimedean measure to
`muArchTamSO` (module docstring). -/
def archHankeConst : ℝ :=
  (2 : ℝ) ^ (Module.finrank ℚ F * (n * (n - 1) / 2)) / cF F n

theorem archHankeConst_pos : 0 < archHankeConst F n := by
  unfold archHankeConst cF
  have hd : (0 : ℝ) < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero F)
  positivity

/-- **Hanke's archimedean measure** $\tau_a = \prod_{v\in a}|\widetilde\omega_G|'_v$ on $G_a = SO(V)(F\otimes\mathbb R)$
(Hanke thesis, §2, p. 5), for the matrix $\psi = \tfrac12H_{Q_0}$; see the module docstring for the conversion from
`muArchTamSO`. -/
@[kb "hanke2005crelle" "§2, p. 5 (τ_a = ∏_{v∈a} |ω̃_G|'_v); (2.4), p. 4 ((d'x)_v)"]
def muArchHanke : Measure (GInfSO Q₀) := ENNReal.ofReal (archHankeConst F n) • muArchTamSO Q₀ hQ

instance : (muArchHanke Q₀ hQ).IsMulLeftInvariant := by unfold muArchHanke; infer_instance

/-- $\tau_a(\Gamma_a\backslash G_a) = 2^{d\,n(n-1)/2}|d_F|^{n(n-1)/4}\,v(M_a)$, $v$ = `unitVolume`. -/
theorem covolume_muArchHanke (i : DC Q₀) :
    covolume (unitGroup Q₀ i) (GInfSO Q₀) (muArchHanke Q₀ hQ) =
      ENNReal.ofReal (archHankeConst F n) * unitVolume Q₀ hQ i := by
  have := countable_GammaSOAdele Q₀
  have := countable_levelGroup (Γ := GammaSOAdele Q₀) (KSO Q₀) (dcRep Q₀ i)
  unfold muArchHanke unitVolume
  exact covolume_smul _ _ (by simpa using archHankeConst_pos (F := F) (n := n))

theorem tsum_covolume_muArchHanke :
    ∑' i, covolume (unitGroup Q₀ i) (GInfSO Q₀) (muArchHanke Q₀ hQ) =
      ENNReal.ofReal (archHankeConst F n) * ∑' i, unitVolume Q₀ hQ i := by
  simp only [covolume_muArchHanke Q₀ hQ]
  exact ENNReal.tsum_mul_left

/-- **Theorem 2.1 in the repository's normalization**: $\sum_a\tau_a(\Gamma_a\backslash G_a) =
\tau(G)\cdot2^{d\,n(n-1)/2}|d_F|^{n(n-1)/4}\big(\prod_v\alpha_v(\Lambda,\Lambda)\big)^{-1}$, $\alpha_v$ = `NF.siegelDensity`. -/
theorem theorem21_siegelDensity (hn : 3 ≤ n) :
    ∑' i, covolume (unitGroup Q₀ i) (GInfSO Q₀) (muArchHanke Q₀ hQ) =
      covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) *
        ENNReal.ofReal (archHankeConst F n * (∏' v, LocalDensity.NF.siegelDensity v Q₀ Q₀)⁻¹) := by
  have hpos : 0 < ∏' v, LocalDensity.NF.siegelDensity v Q₀ Q₀ := tprod_siegelDensity_pos hn Q₀ hQ
  rw [tsum_covolume_muArchHanke, covolume_eq_muFin_mul_tsum_unitVolume, muFin_KSO, finFactor_one Q₀ hQ]
  rw [mul_comm (ENNReal.ofReal (∏' v, _)) (∑' i, _), mul_assoc, ← ENNReal.ofReal_mul hpos.le]
  rw [show (∏' v, LocalDensity.NF.siegelDensity v Q₀ Q₀) *
      (archHankeConst F n * (∏' v, LocalDensity.NF.siegelDensity v Q₀ Q₀)⁻¹) = archHankeConst F n by
    field_simp, mul_comm]

/-- **The product formula for $2$**: $\prod_v|2|_v = 2^{-[F:\mathbb Q]}$ over the finite places of $F$. -/
theorem tprod_norm_two :
    ∏' v : HeightOneSpectrum (𝓞 F), ‖(2 : v.adicCompletion F)‖ = ((2 : ℝ) ^ Module.finrank ℚ F)⁻¹ := by
  have h := prod_infinitePlace_mul_tprod_finitePlace (F := F) (x := 2) two_ne_zero
  have h1 : ∏ w : InfinitePlace F, w (algebraMap (𝓞 F) F 2) ^ w.mult = (2 : ℝ) ^ Module.finrank ℚ F := by
    rw [InfinitePlace.prod_eq_abs_norm]
    have : algebraMap (𝓞 F) F 2 = algebraMap ℚ F 2 := by
      rw [map_ofNat, map_ofNat]
    rw [this, Algebra.norm_algebraMap]
    push_cast
    rw [abs_of_pos (by positivity)]
  have h2 : ∀ v : HeightOneSpectrum (𝓞 F),
      ‖FinitePlace.embedding v (algebraMap (𝓞 F) F 2)‖ = ‖(2 : v.adicCompletion F)‖ := by
    intro v; rw [map_ofNat, map_ofNat]
  simp only [h2] at h
  rw [h1] at h
  exact eq_inv_of_mul_eq_one_right h

/-- $|2|_v = 1$ except at the finitely many dyadic places. -/
theorem hasFiniteMulSupport_norm_two :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => ‖(2 : v.adicCompletion F)‖ := by
  have h0 : {v : HeightOneSpectrum (𝓞 F) | (2 : 𝓞 F) ∈ v.asIdeal}.Finite := by
    have h_span_nezero : Ideal.span {(2 : 𝓞 F)} ≠ 0 := by simp
    simp only [← Ideal.dvd_span_singleton]
    exact Ideal.finite_factors h_span_nezero
  refine h0.subset fun v hv => ?_
  by_contra h
  apply hv
  have := (FinitePlace.norm_eq_one_iff_notMem F v (2 : 𝓞 F)).mpr h
  simpa [map_ofNat] using this

include hQ in
/-- **The product of Hanke's local densities**: $\prod_v\beta_v(\Lambda,\psi) = 2^{-d\,n(n-1)/2}\prod_v\alpha_v(\Lambda,\Lambda)$. -/
theorem tprod_hankeBeta (hn0 : n ≠ 0) (hn2 : n ≠ 2) :
    ∏' v, hankeBeta v (std v) (gramOf v (LocalDensity.NF.Qp v Q₀)) =
      ((2 : ℝ) ^ (Module.finrank ℚ F * (n * (n - 1) / 2)))⁻¹ * ∏' v, LocalDensity.NF.siegelDensity v Q₀ Q₀ := by
  simp_rw [hankeBeta_gramV _ Q₀ hQ]
  have hfin := hasFiniteMulSupport_norm_two (F := F)
  have hf : Multipliable fun v : HeightOneSpectrum (𝓞 F) => ‖(2 : v.adicCompletion F)‖ ^ (n * (n - 1) / 2) :=
    multipliable_of_hasFiniteMulSupport (hfin.pow _)
  rw [hf.tprod_mul (multipliable_siegelDensity hn0 hn2 Q₀ hQ)]
  congr 1
  have e1 : ∏' v : HeightOneSpectrum (𝓞 F), ‖(2 : v.adicCompletion F)‖ ^ (n * (n - 1) / 2) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(2 : v.adicCompletion F)‖ ^ (n * (n - 1) / 2) :=
    tprod_eq_finprod (L := SummationFilter.unconditional _) (hfin.pow _)
  have e2 : ∏' v : HeightOneSpectrum (𝓞 F), ‖(2 : v.adicCompletion F)‖ =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(2 : v.adicCompletion F)‖ :=
    tprod_eq_finprod (L := SummationFilter.unconditional _) hfin
  rw [e1, ← finprod_pow hfin, ← e2, tprod_norm_two, inv_pow, ← pow_mul]

/-- **Theorem 2.1** (Hanke thesis, pp. 5–6; Cassels 1978, pp. 380–382, over $\mathbb Q$): for $\Lambda = \mathcal O_F^n$ and
$\psi = \tfrac12H_{Q_0}$ the matrix of $\varphi$ in the global basis $e_0,\dots,e_{n-1}$ ($n\ge3$, any signature, any number
field),
$$\sum_{a\in\mathrm{Cl}}\tau_a(\Gamma_a\backslash G_a) = \tau(G)\,|D_k|^{n(n-1)/4}\prod_{v\in h}\beta_v(\Lambda,\psi)^{-1},$$
$\tau(G)$ the covolume of $G(F)$ in $G(\mathbb A)$ for Weil's Tamagawa measure. -/
@[kb "hanke2005crelle" "Theorem 2.1, pp. 5–6"]
theorem theorem21 (hn : 3 ≤ n) :
    ∑' i, covolume (unitGroup Q₀ i) (GInfSO Q₀) (muArchHanke Q₀ hQ) =
      covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) *
        ENNReal.ofReal (|(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4) *
          (∏' v, hankeBeta v (std v) (gramOf v (LocalDensity.NF.Qp v Q₀)))⁻¹) := by
  rw [theorem21_siegelDensity Q₀ hQ hn, tprod_hankeBeta Q₀ hQ (by omega) (by omega)]
  congr 2
  unfold archHankeConst cF
  rw [Real.rpow_neg (abs_nonneg _), mul_inv, inv_inv]
  field_simp

/-- **Theorem 2.1 with $\tau(G) = 2$** (Hanke's (2.1), p. 4; proved in the repository for every nondegenerate $V$ of
dimension $n\ge3$ over every number field, `tauTwoAll_release_uncond`):
$$\sum_{a\in\mathrm{Cl}}\tau_a(\Gamma_a\backslash G_a) = 2\,|D_k|^{n(n-1)/4}\prod_{v\in h}\beta_v(\Lambda,\psi)^{-1}.$$ -/
@[kb "hanke2005crelle" "Theorem 2.1, pp. 5–6, with (2.1), p. 4"]
theorem theorem21_tau_two (hn : 3 ≤ n) :
    ∑' i, covolume (unitGroup Q₀ i) (GInfSO Q₀) (muArchHanke Q₀ hQ) =
      2 * ENNReal.ofReal (|(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4) *
          (∏' v, hankeBeta v (std v) (gramOf v (LocalDensity.NF.Qp v Q₀)))⁻¹) := by
  rw [theorem21 Q₀ hQ hn]
  have h2 : covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) = 2 :=
    tauTwoAll_release_uncond n hn Q₀ hQ
  rw [h2]

end QuadFormsKB.Hanke2005
