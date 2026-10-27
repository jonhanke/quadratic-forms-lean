/-
# Siegel's formula when the stabilizer of a frame has rank one: corank one and anisotropic binary forms

**Layer:** number fields. $F$ **any** number field, $Q_0$ a nondegenerate quadratic form over $\mathcal O_F$ in $N = r + 1$
variables of any signature, $L = \mathcal O_F^N$, $T_0$ a nondegenerate form over $\mathcal O_F$ of rank $r$ with a rational
frame $\Xi$ ($Q_0\circ\Xi = T_0$). The orthogonal complement $W$ of a frame has rank $n' = N - r = 1$, so its special
orthogonal group $SO(W) = SO_1$ is trivial; this is the case $n = m + 1$ of Siegel (1935, 1936) excluded from
`siegelIndefiniteForms_uncond` ($n'\ge3$). Write $|x|_w$ for the normalized absolute value at an archimedean place $w$
($|\sigma_wx|$ at a real place, $|\sigma_wx|^2$ at a complex place), $v(M_i)$ for the unit volumes (`unitVolume`: the covolume
of the unit group $\Gamma_i = SO(M_i)$ in $SO(V)(F_\infty)$ for Weil's measure `muArchTamSO`; $\Gamma_i$ may be infinite) and
$n(M_i,T_0) = \#(\Gamma_i\backslash R(M_i,T_0))$ for the number of classes of representations of $T_0$ by $M_i$ modulo units
(`repCount`).

**Headlines (unconditional):**
* **`siegelIndefiniteForms_corank1_uncond`** ($N\ge3$):
  $$c^{(1)}_\infty(Q_0)\sum_in(M_i,T_0) = \frac12\,|d_F|^{-N(N-1)/4}\prod_\mathfrak p\beta_\mathfrak p(L,T_0)\cdot\sum_iv(M_i),\qquad
    c^{(1)}_\infty(Q_0) = c_F(N)\prod_{w\mid\infty}|\det H_{Q_0}|_w^{-1};$$
* **`siegelIndefinite_binary_uncond`** ($N = 2$, $r = 1$, $T_0 = \langle m\rangle$, $V$ **anisotropic**, $E$ its discriminant
  field, $\chi_E$ the quadratic character): the same with the regularized product
  $$|d_F|^{-1/2}\,L(1,\chi_E)^{-1}\prod_\mathfrak pL_\mathfrak p(1,\chi_E)\,\beta_\mathfrak p(L,m)\qquad(\texttt{binDensityProduct}),$$
  whose factors are $1$ for almost all $\mathfrak p$. Isotropic binary $V$ (e.g. $xy$) is excluded (hypothesis `AnisotropicF`):
  there $SO(V)\cong\mathbb G_m$ and Weil's measure has a different normalization (`tauOne_binary_isotropic_uncond`).

**The factor $\frac12$ (Siegel's $\varepsilon$).** In Weil's form Siegel's formula carries $\tau(SO(W))/\tau(SO(V))$; here
$\tau(SO(V)) = 2$ (`tauTwoAll_release_uncond` for $N\ge3$, `tauTwoBinaryAll_uncond` for anisotropic binary $V$) while
$SO(W) = SO_1$ is trivial, $\tau(SO_1) = 1$. Classically the same $\frac12$ is Siegel's $\varepsilon = \frac12$ for $n = m + 1$
(1935, Hauptsatz): counting with the full orthogonal groups, the stabilizer $O(W) = \{\pm1\}$ of a representation has order
$2$ while $SO(W)$ is trivial. The local densities $\beta_\mathfrak p(L,T_0)$ (`NF.localDensityForm`) are the full ones.

**Proof.** The global count $\sum_in(M_i,T_0) = \#\{SO(\hat L)\text{-orbits of integral adelic
frames}\}$ (`tsum_repCount_eq`, no Tamagawa number), the local counts (`tsum_one_finOrbit`, `frameLocFactor_mul_aSO`),
$\tau(SO(V)) = 2$ in the form $\mu_f(SO(\hat L))\sum_iv(M_i) = 2$, and the product formula (`densityIdentity_corankOne`).
-/
import QuadFormsKB.Tamagawa.Indefinite.CorankOneCount
import QuadFormsKB.Tamagawa.Indefinite.CorankOneLocal
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryTauTwoUncond

open MeasureTheory Set Matrix MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames LocalDensity
  QuadFormsKB.RegProd

variable {F : Type} [Field F] [NumberField F] {r : ℕ}

/-! ### The archimedean constant -/

open Classical in
/-- **The archimedean constant for corank one**
$c^{(1)}_\infty(Q_0) = c_F(N)\prod_{w\ \mathrm{real}}|\sigma_w\det H_{Q_0}|^{-1}\prod_{w\ \mathrm{complex}}|\sigma_w\det H_{Q_0}|^{-2}$,
i.e. $c_F(N)\prod_{w\mid\infty}|\det H_{Q_0}|_w^{-1}$ with normalized absolute values. It is $c_\infty(T_0)\cdot m$ with
$c_\infty(T_0) = c_F(N)\prod_w|\det H_{T_0}|_w^{-1}$ (`cInfTNF`, $n' = 1$) and $m = \prod_w|\det H_{T_0}|_w/|\det H_{Q_0}|_w$ the
mass of Siegel's measure on the one-point stabilizer $SO_1(F_\infty)$ of a representation (the normalization of
`siegelIndefiniteForms_uncond`: $\prod_w|\det g|_w^{n'+1}$ times the Leray mass $\prod_w|2c''|_w^{-1}$ of $SO(\langle c''\rangle)$,
and $\det(g)^2\det H_{Q_0} = \det H_{T_0}\cdot2c''$). Parameter: `Q₀`. -/
def cInfCorankOne {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) : ℝ≥0∞ :=
  ENNReal.ofReal (cF F N) *
    ((∏ w : {w : InfinitePlace F // w.IsReal}, ENNReal.ofReal (|σR w (algebraMap (𝓞 F) F Q₀.hessian.det)|⁻¹)) *
      ∏ w : {w : InfinitePlace F // w.IsComplex},
        ENNReal.ofReal ((‖σC w (algebraMap (𝓞 F) F Q₀.hessian.det)‖ ^ 2)⁻¹))

open Classical in
theorem cInfCorankOne_eq {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) :
    cInfCorankOne Q₀ = ENNReal.ofReal (cF F N *
      ((∏ w : {w : InfinitePlace F // w.IsReal}, |σR w (algebraMap (𝓞 F) F Q₀.hessian.det)|⁻¹) *
        ∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w (algebraMap (𝓞 F) F Q₀.hessian.det)‖ ^ 2)⁻¹)) := by
  unfold cInfCorankOne
  have h1 : ∀ w : {w : InfinitePlace F // w.IsReal}, 0 ≤ |σR w (algebraMap (𝓞 F) F Q₀.hessian.det)|⁻¹ :=
    fun w => by positivity
  have h2 : ∀ w : {w : InfinitePlace F // w.IsComplex},
      0 ≤ (‖σC w (algebraMap (𝓞 F) F Q₀.hessian.det)‖ ^ 2)⁻¹ := fun w => by positivity
  rw [← ENNReal.ofReal_prod_of_nonneg (fun w _ => h1 w), ← ENNReal.ofReal_prod_of_nonneg (fun w _ => h2 w),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => h1 w), ← ENNReal.ofReal_mul (cF_pos' (F := F) _).le]

/-! ### Covolumes with convergence factors -/

/-- **The β-decomposition of the covolume with convergence factors** $(\lambda_v)$:
$\operatorname{covol}(SO(V)(F)\backslash SO(V)(\mathbb A),\mu^\lambda) = \mu^\lambda_f(SO(\hat L))\sum_iv(M_i)$. -/
theorem covolume_muTam_eq_muFin_mul {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (lam : HeightOneSpectrum (𝓞 F) → ℝ) :
    covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ lam) =
      muFin Q₀ lam (KSO Q₀) * ∑' i, unitVolume Q₀ hQ i := by
  have := countable_GammaSOAdele Q₀
  haveI := fun i => countable_levelGroup (Γ := GammaSOAdele Q₀) (KSO Q₀) (dcRep Q₀ i)
  haveI := fun i => smulInvariantMeasure_subgroup (levelGroup (GammaSOAdele Q₀) (KSO Q₀) (dcRep Q₀ i))
    (muArchTamSO Q₀ hQ)
  haveI := fun i => measurableConstSMul_subgroup (levelGroup (GammaSOAdele Q₀) (KSO Q₀) (dcRep Q₀ i))
  exact covolume_eq_measure_mul_tsum_covolume (GammaSOAdele Q₀) (KSO Q₀) (isOpen_KSO Q₀).measurableSet
    (dcRep Q₀) (dcRep_cov Q₀) (fun i j γ hγ k hk k' hk' h => dcRep_disj Q₀ i j γ hγ k hk k' hk' h)
    (fun i γ hγ h1 => GammaSOAdele_injA Q₀ γ hγ.1 h1)
    (fun i => (exists_fd_levelGroup Q₀ (dcRep Q₀ i)).choose)
    (fun i => (exists_fd_levelGroup Q₀ (dcRep Q₀ i)).choose_spec.1)
    (fun i => (exists_fd_levelGroup Q₀ (dcRep Q₀ i)).choose_spec.2)
    (muArchTamSO Q₀ hQ) (muFin Q₀ lam)

/-- The covolume is linear in the measure. -/
theorem covolume_smul_muTam {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (lam : HeightOneSpectrum (𝓞 F) → ℝ) (c : ℝ≥0∞) :
    covolume (GammaSOAdele Q₀) (SOAdele Q₀) (c • muTam Q₀ hQ lam) =
      c * covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ lam) := by
  have := countable_GammaSOAdele Q₀
  have := discreteTopology_GammaSOAdele Q₀
  obtain ⟨E, hE⟩ := exists_measurableSet_forall_existsUnique_smul_mem (GammaSOAdele Q₀)
  have h1 : IsFundamentalDomain (GammaSOAdele Q₀) E (muTam Q₀ hQ lam) :=
    IsFundamentalDomain.mk' hE.1.nullMeasurableSet hE.2
  have h2 : IsFundamentalDomain (GammaSOAdele Q₀) E (c • muTam Q₀ hQ lam) :=
    IsFundamentalDomain.mk' hE.1.nullMeasurableSet hE.2
  rw [h2.covolume_eq_volume, h1.covolume_eq_volume, Measure.smul_apply, smul_eq_mul]

/-- $a_v = \mu_v(SO(L_v))$ (`aSO`) is Siegel's density $\alpha_v(L,L)$. -/
theorem aSO_eq_siegelDensity {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (v : HeightOneSpectrum (𝓞 F)) :
    aSO Q₀ v = NF.siegelDensity v Q₀ Q₀ := by
  rw [aSO, muLocSO_soStabSO, div_one, ENNReal.toReal_ofReal (siegelDensity_self_pos' Q₀ hQ v).le]

/-- $\mu^\lambda_f(SO(\hat L)) = \prod'_va_v/\lambda_v$, $a_v = \mu_v(SO(L_v))$ (`aSO`). -/
theorem finFactor_eq_tprod_aSO {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    {lam : HeightOneSpectrum (𝓞 F) → ℝ} (hlam : ∀ v, 0 < lam v) : finFactor Q₀ lam = ∏' v, aSO Q₀ v / lam v := by
  rw [finFactor_eq Q₀ hQ hlam]
  exact tprod_congr fun v => by rw [aSO_eq_siegelDensity Q₀ hQ v]

/-! ### The count against the local factors -/

section Count

variable (Q₀ : QuadForm (𝓞 F) (r + 1)) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate)
  (Ξ : RatFrame Q₀ T₀)

local notation "D" => towerCorankOne Q₀ hQ T₀ hT Ξ

include hT in
/-- **The count against the local factors**, for any positive convergence factors $(\lambda_v)$ for which
$\prod_va_v/\lambda_v$ converges to a positive number:
$$\sum_in(M_i,T_0)\cdot\prod_v\frac{a_v}{\lambda_v} = \prod_v\frac{f_v}{\lambda_v}\cdot\prod_va''_v,$$
$f_v$ = `frameLocFactor` $=\beta_v(L,T_0)|\det g|_v^2|\det H_{T_0}|_v^{-1}$, $a''_v = \mu''_v(SO_1(\mathfrak o_v))$; and the
product of the $f_v/\lambda_v$ converges. -/
theorem count_mul_tprod (lam : HeightOneSpectrum (𝓞 F) → ℝ) (hlam : ∀ v, 0 < lam v)
    (ha : Multipliable fun v => aSO Q₀ v / lam v) :
    Multipliable (fun v => frameLocFactor Q₀ hQ T₀ Ξ D hT v / lam v) ∧
      (∑' i, repCount Q₀ T₀ i) * ENNReal.ofReal (∏' v, aSO Q₀ v / lam v) =
        ENNReal.ofReal ((∏' v, frameLocFactor Q₀ hQ T₀ Ξ D hT v / lam v) * ∏' v, aSO (D).Q'' v) := by
  classical
  set n : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (locCount Q₀ hQ T₀ Ξ D hT v : ℝ) with hn
  have hnfin : (Function.mulSupport n).Finite :=
    (towerBad Q₀ hQ T₀ Ξ D hT).finite_toSet.subset (mulSupport_locCount_subset Q₀ hQ T₀ Ξ D hT)
  have hn' : Multipliable n := multipliable_of_hasFiniteMulSupport hnfin
  have ha''fin := mulSupport_aSO_rankOne_finite (D).Q'' (D).hQ''
  have ha'' : Multipliable (aSO (D).Q'') := multipliable_of_hasFiniteMulSupport ha''fin
  have hinvfin : (Function.mulSupport fun v => (aSO (D).Q'' v)⁻¹).Finite := ha''fin.subset fun v hv => by
    intro h1; apply hv; show (aSO (D).Q'' v)⁻¹ = 1; rw [show aSO (D).Q'' v = 1 from h1, inv_one]
  have hinv : Multipliable fun v => (aSO (D).Q'' v)⁻¹ := multipliable_of_hasFiniteMulSupport hinvfin
  have hf : ∀ v, frameLocFactor Q₀ hQ T₀ Ξ D hT v / lam v = n v * (aSO Q₀ v / lam v) * (aSO (D).Q'' v)⁻¹ := by
    intro v
    have h := frameLocFactor_mul_aSO Q₀ hQ T₀ Ξ D hT v
    have hpos := aSO_pos (D).Q'' (D).hQ'' v
    have hf' : frameLocFactor Q₀ hQ T₀ Ξ D hT v = n v * aSO Q₀ v / aSO (D).Q'' v :=
      eq_div_of_mul_eq hpos.ne' h
    rw [hf']
    ring
  have hmf : Multipliable fun v => frameLocFactor Q₀ hQ T₀ Ξ D hT v / lam v := by
    simp_rw [hf]; exact (hn'.mul ha).mul hinv
  refine ⟨hmf, ?_⟩
  rw [tsum_repCount_eq Q₀ hQ T₀ hT Ξ, tsum_one_finOrbit Q₀ hQ T₀ Ξ D hT,
    ← ENNReal.ofReal_mul (tprod_nonneg fun v => Nat.cast_nonneg _)]
  congr 1
  have e1 : ∀ v, n v * (aSO Q₀ v / lam v) = frameLocFactor Q₀ hQ T₀ Ξ D hT v / lam v * aSO (D).Q'' v := by
    intro v
    rw [hf, mul_assoc, inv_mul_cancel₀ (aSO_pos (D).Q'' (D).hQ'' v).ne', mul_one]
  rw [← hn'.tprod_mul ha, ← hmf.tprod_mul ha'']
  exact tprod_congr e1

end Count

/-! ### Headline (1): corank one, $N\ge3$ -/

open Classical in
/-- **Siegel's formula for frames of corank one, every number field — unconditional** (Siegel 1935, 1936, Hauptsatz for
$n = m + 1$, $\varepsilon = \frac12$, measure form; Weil 1965): for $F$ a number field, $Q_0$ nondegenerate over
$\mathcal O_F$ in $N = r + 1\ge3$ variables of any signature, $T_0$ nondegenerate of rank $r$ with a rational frame $\Xi$
($Q_0\circ\Xi = T_0$),
$$c^{(1)}_\infty(Q_0)\sum_in(M_i,T_0) = \frac12\,|d_F|^{-N(N-1)/4}\prod_\mathfrak p\beta_\mathfrak p(L,T_0)\cdot\sum_iv(M_i),$$
the sums over the proper classes $M_i$ in the genus of $L = \mathcal O_F^N$; $n(M_i,T_0)$ = `repCount` (the number of classes
of representations of $T_0$ by $M_i$ modulo the unit group $\Gamma_i = SO(M_i)$, which may be infinite), $v(M_i)$ =
`unitVolume`, $c^{(1)}_\infty(Q_0) = c_F(N)\prod_{w\mid\infty}|\det H_{Q_0}|_w^{-1}$ (`cInfCorankOne`, normalized absolute
values), $\beta_\mathfrak p$ = `NF.localDensityForm` (the right side is `frameDensityProduct`, as in
`siegelIndefiniteForms_uncond`). The factor $\frac12$ is Siegel's $\varepsilon$: $\tau(SO(W))/\tau(SO(V)) = 1/2$ for the trivial
stabilizer $SO(W) = SO_1$. No hypotheses beyond these. -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz, n = m + 1 (ε = 1/2; corank one; every number field) [unverified]"]
theorem siegelIndefiniteForms_corank1_uncond (Q₀ : QuadForm (𝓞 F) (r + 1)) (hQ : Q₀.Nondegenerate)
    (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀) (hr : 2 ≤ r) :
    cInfCorankOne Q₀ * ∑' i, repCount Q₀ T₀ i =
      2⁻¹ * ENNReal.ofReal (frameDensityProduct Q₀ T₀) * ∑' i, unitVolume Q₀ hQ i := by
  set D := towerCorankOne Q₀ hQ T₀ hT Ξ with hD
  have hN : 3 ≤ r + 1 := by omega
  -- the local product of `SO(V)` and `τ(SO(V)) = 2`
  have hApos : 0 < ∏' v, aSO Q₀ v := tprod_aSO_pos hN Q₀ hQ
  set A := ENNReal.ofReal (∏' v, aSO Q₀ v) with hAdef
  have hA0 : A ≠ 0 := (ENNReal.ofReal_pos.2 hApos).ne'
  have hAt : A ≠ ⊤ := ENNReal.ofReal_ne_top
  set V := ∑' i, unitVolume Q₀ hQ i with hV
  have hτ : A * V = 2 := by
    have h := tauTwoAll_release_uncond (r + 1) hN Q₀ hQ
    unfold TamagawaNumberTwoAdelic at h
    rw [covolume_muTam_eq_muFin_mul, muFin_KSO, finFactor_eq_tprod_aSO Q₀ hQ (fun _ => one_pos)] at h
    simp only [div_one] at h
    exact h
  obtain ⟨hmf, hcount⟩ := count_mul_tprod Q₀ hQ T₀ hT Ξ (fun _ => 1) (fun _ => one_pos)
    (by simpa only [div_one] using multipliable_aSO hN Q₀ hQ)
  -- the product formula
  have hid := densityIdentity_corankOne Q₀ hQ T₀ Ξ D hT (fun _ => 1) (fun _ => one_ne_zero) hmf
  simp only [div_one] at hid hcount
  have hfdp : frameDensityProduct Q₀ T₀ = cF F (r + 1) * ∏' v, NF.localDensityForm v Q₀ T₀ := by
    unfold frameDensityProduct cF
    congr 2
    push_cast
    ring
  -- cancel `A`
  have key1 : cInfCorankOne Q₀ * (∑' i, repCount Q₀ T₀ i) * A = ENNReal.ofReal (frameDensityProduct Q₀ T₀) := by
    rw [mul_assoc, hcount, cInfCorankOne_eq, ← ENNReal.ofReal_mul (mul_nonneg (cF_pos' (F := F) _).le (mul_nonneg
      (Finset.prod_nonneg fun w _ => by positivity) (Finset.prod_nonneg fun w _ => by positivity))), hfdp, ← hid]
    congr 1
    ring
  have key2 : 2⁻¹ * ENNReal.ofReal (frameDensityProduct Q₀ T₀) * V * A = ENNReal.ofReal (frameDensityProduct Q₀ T₀) := by
    calc 2⁻¹ * ENNReal.ofReal (frameDensityProduct Q₀ T₀) * V * A
        = 2⁻¹ * (A * V) * ENNReal.ofReal (frameDensityProduct Q₀ T₀) := by ring
      _ = _ := by rw [hτ, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  exact (ENNReal.mul_left_inj hA0 hAt).mp (key1.trans key2.symm)

/-! ### Headline (2): anisotropic binary forms -/

/-- **The regularized product of the local densities of a binary form**:
$$|d_F|^{-1/2}\,L(1,\chi_E)^{-1}\prod_\mathfrak pL_\mathfrak p(1,\chi_E)\,\beta_\mathfrak p(L,T_0),$$
$\chi_E$ the character of the discriminant field $E$ (`chiE`), $L_\mathfrak p(1,\chi_E)^{-1}$ = `lamL (chiE F E) 𝔭`, $L(1,\chi_E)$ =
`LOne (chiE F E)`. The factors $L_\mathfrak p(1,\chi_E)\beta_\mathfrak p(L,T_0)$ are $1$ for almost all $\mathfrak p$ when $V$ is
anisotropic (so the product is finite), while $\prod_\mathfrak p\beta_\mathfrak p$ itself does not converge absolutely. Parameters:
`Q₀`, `T₀`, `E`. -/
@[kb "siegel1935" "local densities of binary forms, regularized by L(1, χ) [unverified]"]
def binDensityProduct (Q₀ : QuadForm (𝓞 F) 2) (T₀ : QuadForm (𝓞 F) 1) (E : Type) [Field E] [NumberField E]
    [Algebra F E] : ℝ :=
  |(discr F : ℝ)| ^ (-(1 / 2 : ℝ)) * (LOne (chiE F E))⁻¹ *
    ∏' v, NF.localDensityForm v Q₀ T₀ / lamL (chiE F E) v

open Classical in
/-- **Siegel's formula for the numbers represented by an anisotropic binary form, every number field —
unconditional** (Siegel 1935, Hauptsatz for $n = 2$, $m = 1$, $\varepsilon = \frac12$; Dirichlet and Gauss's genus theory over
$\mathbb Q$; Weil 1965 with convergence factors): for $F$ a number field, $Q_0$ a nondegenerate binary form over $\mathcal O_F$
of any signature, **anisotropic** over $F$, $E$ its discriminant field (`IsDiscField`: $E = F(\sqrt{-\det H_{Q_0}})$), $T_0 =
\langle m\rangle$ a nondegenerate form in one variable with a rational point $\Xi$ ($Q_0(\Xi) = m$),
$$c^{(1)}_\infty(Q_0)\sum_in(M_i,m) = \frac12\,|d_F|^{-1/2}L(1,\chi_E)^{-1}\prod_\mathfrak pL_\mathfrak p(1,\chi_E)\,\beta_\mathfrak p(L,m)
\cdot\sum_iv(M_i),$$
$n(M_i,m)$ = `repCount` (the number of $x\in M_i$ with $Q(x) = m$ modulo the unit group $SO(M_i)$: finite for definite
$Q_0$, infinite for indefinite $Q_0$ where it is the group of norm-one units of an order of $E$), $v(M_i)$ = `unitVolume`
(for indefinite $Q_0$ over $\mathbb Q$ a multiple of the regulator of that order), $c^{(1)}_\infty(Q_0) = c_F(2)\prod_w|\det
H_{Q_0}|_w^{-1}$. The factor $\frac12$ is $\tau(SO_1)/\tau(SO(V)) = 1/2$; the $L$-value is Weil's global convergence factor
of $\tau(SO(V)) = 2$ (`tauTwoBinaryAll_uncond`, equivalent to Dirichlet's class number formula for $E$). Isotropic binary
$V$ is excluded. -/
@[kb "siegel1935" "Hauptsatz for n = 2, m = 1 (ε = 1/2), binary forms; Dirichlet's class number formula [unverified]"]
theorem siegelIndefinite_binary_uncond (Q₀ : QuadForm (𝓞 F) 2) (hQ : Q₀.Nondegenerate) (hA : AnisotropicF Q₀)
    (E : Type) [Field E] [NumberField E] [Algebra F E] (hE : IsDiscField Q₀ E)
    (T₀ : QuadForm (𝓞 F) 1) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀) :
    cInfCorankOne Q₀ * ∑' i, repCount Q₀ T₀ i =
      2⁻¹ * ENNReal.ofReal (binDensityProduct Q₀ T₀ E) * ∑' i, unitVolume Q₀ hQ i := by
  set lam := lamL (chiE F E) with hlamdef
  have hlam : ∀ v, 0 < lam v := lamL_pos (abs_chiE_le hE.finrank_eq_two)
  obtain ⟨hL, -⟩ := lOne_chiE (F := F) (E := E) hE.finrank_eq_two
  -- the convergence factors make the local product finite
  obtain ⟨S, hS⟩ := eventually_muLocSO_lamL_chiE Q₀ hQ hE
  have haS : ∀ v ∉ S, aSO Q₀ v / lam v = 1 := by
    intro v hv
    have h := hS v hv
    have h0 : 0 ≤ NF.siegelDensity v Q₀ Q₀ / lam v :=
      div_nonneg (siegelDensity_self_pos' Q₀ hQ v).le (hlam v).le
    rw [muLocSO_soStabSO, ← ENNReal.ofReal_one] at h
    rw [aSO_eq_siegelDensity Q₀ hQ v]
    exact (ENNReal.ofReal_eq_ofReal_iff h0 zero_le_one).mp h
  have hafin : (Function.mulSupport fun v => aSO Q₀ v / lam v).Finite :=
    S.finite_toSet.subset fun v hv => by
      by_contra h; exact hv (haS v h)
  have ha : Multipliable fun v => aSO Q₀ v / lam v := multipliable_of_hasFiniteMulSupport hafin
  have hApos : 0 < ∏' v, aSO Q₀ v / lam v := by
    rw [tprod_eq_prod (s := hafin.toFinset) (fun v hv => by
      by_contra hne; exact hv (hafin.mem_toFinset.2 hne))]
    exact Finset.prod_pos fun v _ => div_pos (aSO_pos Q₀ hQ v) (hlam v)
  set A := ENNReal.ofReal (∏' v, aSO Q₀ v / lam v) with hAdef
  have hA0 : A ≠ 0 := (ENNReal.ofReal_pos.2 hApos).ne'
  have hAt : A ≠ ⊤ := ENNReal.ofReal_ne_top
  set V := ∑' i, unitVolume Q₀ hQ i with hV
  -- `τ(SO(V)) = 2` for the binary measure
  have hτ : ENNReal.ofReal (LOne (chiE F E))⁻¹ * (A * V) = 2 := by
    have h := tauTwoBinaryAll_uncond F Q₀ hQ hA E hE
    rw [muTamBin, muTamChi, covolume_smul_muTam, covolume_muTam_eq_muFin_mul, muFin_KSO,
      finFactor_eq_tprod_aSO Q₀ hQ hlam] at h
    exact h
  have hAV : A * V = 2 * ENNReal.ofReal (LOne (chiE F E)) := by
    rw [ENNReal.ofReal_inv_of_pos hL] at hτ
    have hL0 : ENNReal.ofReal (LOne (chiE F E)) ≠ 0 := (ENNReal.ofReal_pos.2 hL).ne'
    calc A * V = (ENNReal.ofReal (LOne (chiE F E)))⁻¹ * (A * V) * ENNReal.ofReal (LOne (chiE F E)) := by
          rw [mul_comm _ (A * V), mul_assoc, ENNReal.inv_mul_cancel hL0 ENNReal.ofReal_ne_top, mul_one]
      _ = 2 * ENNReal.ofReal (LOne (chiE F E)) := by rw [hτ]
  obtain ⟨hmf, hcount⟩ := count_mul_tprod (r := 1) Q₀ hQ T₀ hT Ξ lam hlam ha
  have hid := densityIdentity_corankOne (r := 1) Q₀ hQ T₀ Ξ (towerCorankOne (r := 1) Q₀ hQ T₀ hT Ξ) hT lam
    (fun v => (hlam v).ne') hmf
  have key1 : cInfCorankOne Q₀ * (∑' i, repCount Q₀ T₀ i) * A =
      ENNReal.ofReal (binDensityProduct Q₀ T₀ E * LOne (chiE F E)) := by
    rw [mul_assoc, hcount, cInfCorankOne_eq, ← ENNReal.ofReal_mul (mul_nonneg (cF_pos' (F := F) _).le (mul_nonneg
      (Finset.prod_nonneg fun w _ => by positivity) (Finset.prod_nonneg fun w _ => by positivity)))]
    congr 1
    rw [binDensityProduct, ← hid, cF_two]
    field_simp
  have key2 : 2⁻¹ * ENNReal.ofReal (binDensityProduct Q₀ T₀ E) * V * A =
      ENNReal.ofReal (binDensityProduct Q₀ T₀ E * LOne (chiE F E)) := by
    calc 2⁻¹ * ENNReal.ofReal (binDensityProduct Q₀ T₀ E) * V * A
        = 2⁻¹ * (A * V) * ENNReal.ofReal (binDensityProduct Q₀ T₀ E) := by ring
      _ = 2⁻¹ * 2 * (ENNReal.ofReal (LOne (chiE F E)) * ENNReal.ofReal (binDensityProduct Q₀ T₀ E)) := by
          rw [hAV]; ring
      _ = _ := by
          rw [ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul, ← ENNReal.ofReal_mul hL.le, mul_comm]
  exact (ENNReal.mul_left_inj hA0 hAt).mp (key1.trans key2.symm)

end QuadFormsKB.Tamagawa.Indefinite
