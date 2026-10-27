/-
# Siegel's measure of representations for indefinite forms: the classical translation

**Layer:** number fields.

Let $F$ be a number field, $Q_0$ a nondegenerate quadratic form over $\mathcal O_F$ in $n$ variables of **any
signature**, $V = F^n$, $L = \mathcal O_F^n$, $G = SO(V)$, $\Gamma = G(F)$ diagonally in
$G(\mathbb A) = G_\infty\times G(\mathbb A_f)$ (`SOAdele`), $K = SO(\hat L)$ (`KSO`), with Weil's Tamagawa measure
$\mu = \mu_\infty\times\mu_f$ (`muTam`, $\lambda_v = 1$; $\mu_\infty$ = `muArchTamSO`). Let $b_i$ (`dcRep`) run over
representatives of $\Gamma\backslash G(\mathbb A_f)/K$ (`DC`), i.e. over the proper classes $M_i = b_i\hat L\cap V$ in
the genus of $L$, and fix $m\in F$.

**Defines**
* `unitGroup Q₀ i` $=\Gamma_i = SO(M_i)$, viewed in $G_\infty$ (`levelGroup`), and **`unitVolume`**
  $v(M_i) = \operatorname{vol}(\Gamma_i\backslash G_\infty, \mu_\infty)$ (`covolume`; an exact fundamental domain exists,
  `exists_fd_levelGroup`);
* `reps Q₀ m i` $= R(M_i, m) = \{x\in M_i : Q(x) = m\}$ embedded in $V_\infty$, a $\Gamma_i$-set;
* **`repMeasure`** $\rho(M_i, m) = \sum_{x\in\Gamma_i\backslash R(M_i,m)}\operatorname{vol}(\Gamma_{i,x}\backslash H_x,
  \mu_{H_x})$, Siegel's *Darstellungsmaß*, where $H_x = \operatorname{Stab}_{G_\infty}(x)$ carries the measure
  $\mu_{H_x}$ of an archimedean fibration $\mathfrak F$ of $\mu_\infty$ over the quadric $\{Q = m\}$ (`ArchFibration`;
  constructed for totally real $F$ in `totallyRealArchFibration`).

**Proves** (unconditional given the fibration data, which is constructed, not assumed, for totally real $F$)
* `lintegral_theta_classical` (**the theta integral, classically**): for every fundamental domain $E$ of $\Gamma$ in
  $G(\mathbb A)$ and every measurable $\Phi\ge0$ on $V_\infty$,
  $$\int_E\sum_{\eta\in V(F),\ Q(\eta)=m}\Phi(g_\infty^{-1}\eta)\,1_{\hat L}(g_f^{-1}\eta)\,d\mu(g)
    = \mu_f(K)\cdot c\cdot\sum_i\rho(M_i, m)\cdot\int_T\Phi\circ\tau\,d\sigma;$$
* `lintegral_theta_mul_tsum_unitVolume` (**the mean-value identity**): multiplied by $\sum_iv(M_i)$ the left side
  equals $\operatorname{covol}(\Gamma\backslash G(\mathbb A))\cdot c\cdot\sum_i\rho(M_i, m)\cdot\int_T\Phi\circ\tau\,d\sigma$;
  dividing by $\operatorname{covol} = \tau(G)$ gives Siegel's $\sum_i\rho(M_i, m)/\sum_iv(M_i)$;
* `totallyRealArchFibration`, `lintegral_theta_classical_totallyReal`,
  `lintegral_theta_mul_tsum_unitVolume_totallyReal`: for totally real $F$, $n\ge2$ and $m\ne0$, the fibration is the
  product of the real-place fibrations (`realArchFibration`) and $c = c_F\prod_w|2\sigma_w(m)|^{-(n-1)}$,
  $c_F = |d_F|^{-n(n-1)/4}$ (`cF`), $T = \prod_wS_{\sigma_w(m)}$, $\sigma = \bigotimes_w\sigma_{w}$ (Leray measures).

All identities hold in $[0,\infty]$, with no finiteness hypothesis.
-/
import QuadFormsKB.Tamagawa.Indefinite.ClassicalDiscrete
import QuadFormsKB.Tamagawa.Indefinite.ClassicalLattice
import QuadFormsKB.Tamagawa.Indefinite.ArchUnique

open MeasureTheory Measure MulAction Set NumberField IsDedekindDomain
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-! ### Unit groups, unit-group volumes, representations -/

/-- **The unit group of the class $i$**: $\Gamma_i = SO(M_i)$, $M_i = b_i\hat L\cap V$, viewed in $G_\infty$ (the image of
$\Gamma\cap(G_\infty\times b_iKb_i^{-1})$). -/
abbrev unitGroup (i : DC Q₀) : Subgroup (GInfSO Q₀) := levelGroup (GammaSOAdele Q₀) (KSO Q₀) (dcRep Q₀ i)

/-- **The unit-group volume** $v(M_i) = \operatorname{vol}(\Gamma_i\backslash G_\infty)$ for Weil's archimedean Tamagawa
measure $\mu_\infty$ = `muArchTamSO` (Siegel's $\rho(M)$-denominator; the measure of an exact fundamental domain,
`exists_fd_levelGroup`). -/
@[kb "siegel1936" "Indefinite quadratische Formen; Maß der Einheitengruppe [unverified]"]
def unitVolume (i : DC Q₀) : ℝ≥0∞ := covolume (unitGroup Q₀ i) (GInfSO Q₀) (muArchTamSO Q₀ hQ)

/-- **The representations of $m$ by the class $i$**: $R(M_i, m) = \{x\in M_i : Q(x) = m\}$, embedded in $V_\infty$; a
$\Gamma_i$-set. -/
def reps (m : F) (i : DC Q₀) : SubMulAction (unitGroup Q₀ i) (VInf F n) :=
  repSet (ratA_smul Q₀ (m := m)) (ratF_smul Q₀ (m := m)) (latHat_stable Q₀) (dcRep Q₀ i)

variable {T : Type*} [MeasurableSpace T] {P : Set (VInf F n)} {σ : Measure T} {τ : T → VInf F n} {c : ℝ≥0∞}

/-- **Siegel's measure of representations** (*Darstellungsmaß*) of $m$ by the class $i$:
$$\rho(M_i, m) = \sum_{x\in\Gamma_i\backslash R(M_i, m)}\operatorname{vol}(\Gamma_{i,x}\backslash H_x, \mu_{H_x}),$$
$H_x = \operatorname{Stab}_{G_\infty}(x)$ with the measure $\mu_{H_x}$ of the archimedean fibration `𝔉` (the quotient
measure: $\mu_\infty = c\,\sigma\otimes\mu_{H_x}$ along the orbit of $x$). Parameters: `Q₀`, `hQ`, `m`, `𝔉`, `i`. -/
@[kb "siegel1936" "Indefinite quadratische Formen; Darstellungsmaß [unverified]"]
def repMeasure (m : F) (𝔉 : ArchFibration (muArchTamSO Q₀ hQ) P σ τ c) (i : DC Q₀) : ℝ≥0∞ :=
  repMeasureOf (unitGroup Q₀ i) (reps Q₀ m i) 𝔉.μH

/-! ### The classical theta integral -/

/-- **The theta integral of an indefinite form, classically** (Siegel 1936; Weil 1982, §2.4 and §4.5): for every
archimedean fibration `𝔉` of $\mu_\infty$ over a quadric `P` containing the archimedean images of
$T(m)(F) = \{Q = m\}$, every fundamental domain $E$ of $\Gamma = SO(V)(F)$ in $SO(V)(\mathbb A)$ and every measurable
$\Phi\ge0$ on $V_\infty$,
$$\int_E\theta_{\Phi\otimes1_{\hat L}}\,d\mu = \mu_f(SO(\hat L))\cdot c\cdot\sum_i\rho(M_i, m)\cdot
  \int_T\Phi\circ\tau\,d\sigma,\qquad\theta(g) = \sum_{\eta\in T(m)(F)}\Phi(g_\infty^{-1}\eta)1_{\hat L}(g_f^{-1}\eta).$$ -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form) [unverified]"]
theorem lintegral_theta_classical (m : F) [SFinite σ] (𝔉 : ArchFibration (muArchTamSO Q₀ hQ) P σ τ c)
    (hP : ∀ η : RatSphere Q₀ m, ratA Q₀ m η ∈ P) (Φ : VInf F n → ℝ≥0∞) (hΦ : Measurable Φ)
    (hΦτ : Measurable fun x => Φ (τ x)) {E : Set (SOAdele Q₀)}
    (hE : IsFundamentalDomain (GammaSOAdele Q₀) E (muTam Q₀ hQ fun _ => 1)) :
    ∫⁻ g in E, thetaFn (ratA Q₀ m) (ratF Q₀ m) Φ (latHat F n) g ∂muTam Q₀ hQ (fun _ => 1) =
      muFin Q₀ (fun _ => 1) (KSO Q₀) * c * (∑' i, repMeasure Q₀ hQ m 𝔉 i) * ∫⁻ x, Φ (τ x) ∂σ := by
  have := countable_GammaSOAdele Q₀
  exact lintegral_theta_eq (Γ := GammaSOAdele Q₀) (KSO Q₀) (isOpen_KSO Q₀).measurableSet (dcRep Q₀)
    (dcRep_cov Q₀) (fun i j γ hγ k hk k' hk' h => dcRep_disj Q₀ i j γ hγ k hk k' hk' h)
    (fun i γ hγ h1 => GammaSOAdele_injA Q₀ γ hγ.1 h1)
    (fun i => (exists_fd_levelGroup Q₀ (dcRep Q₀ i)).choose)
    (fun i => (exists_fd_levelGroup Q₀ (dcRep Q₀ i)).choose_spec.1)
    (fun i => (exists_fd_levelGroup Q₀ (dcRep Q₀ i)).choose_spec.2)
    (muArchTamSO Q₀ hQ) (muFin Q₀ fun _ => 1) (ratA_smul Q₀) (ratF_smul Q₀) (ratA_injective Q₀ m)
    (latHat_stable Q₀) 𝔉 hP (fun i y => exists_fd_stabArith Q₀ (dcRep Q₀ i) y) Φ
    (measurable_GInf_inv_smul Q₀ hΦ) hΦτ hE

/-- **The mean-value identity** (classical form of the Siegel–Weil identity before dividing by $\tau(G)$): with
$v(M_i)$ = `unitVolume`,
$$\Big(\int_E\theta_{\Phi\otimes1_{\hat L}}\,d\mu\Big)\cdot\sum_iv(M_i) =
  \operatorname{covol}(\Gamma\backslash SO(V)(\mathbb A), \mu)\cdot c\cdot\sum_i\rho(M_i, m)\cdot\int_T\Phi\circ\tau\,d\sigma.$$
Since $\int_E\theta = \operatorname{covol}\cdot(\text{mean value of }\theta)$, once $\operatorname{covol} = \tau(G)$ is known to
be finite and nonzero this is Siegel's $\text{mean} = c\sum_i\rho(M_i,m)/\sum_iv(M_i)\cdot\int\Phi\,d\sigma$. -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form) [unverified]"]
theorem lintegral_theta_mul_tsum_unitVolume (m : F) [SFinite σ] (𝔉 : ArchFibration (muArchTamSO Q₀ hQ) P σ τ c)
    (hP : ∀ η : RatSphere Q₀ m, ratA Q₀ m η ∈ P) (Φ : VInf F n → ℝ≥0∞) (hΦ : Measurable Φ)
    (hΦτ : Measurable fun x => Φ (τ x)) {E : Set (SOAdele Q₀)}
    (hE : IsFundamentalDomain (GammaSOAdele Q₀) E (muTam Q₀ hQ fun _ => 1)) :
    (∫⁻ g in E, thetaFn (ratA Q₀ m) (ratF Q₀ m) Φ (latHat F n) g ∂muTam Q₀ hQ (fun _ => 1)) *
        ∑' i, unitVolume Q₀ hQ i =
      covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) * c *
        (∑' i, repMeasure Q₀ hQ m 𝔉 i) * ∫⁻ x, Φ (τ x) ∂σ := by
  have := countable_GammaSOAdele Q₀
  exact lintegral_theta_mul_tsum_covolume (Γ := GammaSOAdele Q₀) (KSO Q₀) (isOpen_KSO Q₀).measurableSet
    (dcRep Q₀) (dcRep_cov Q₀) (fun i j γ hγ k hk k' hk' h => dcRep_disj Q₀ i j γ hγ k hk k' hk' h)
    (fun i γ hγ h1 => GammaSOAdele_injA Q₀ γ hγ.1 h1)
    (fun i => (exists_fd_levelGroup Q₀ (dcRep Q₀ i)).choose)
    (fun i => (exists_fd_levelGroup Q₀ (dcRep Q₀ i)).choose_spec.1)
    (fun i => (exists_fd_levelGroup Q₀ (dcRep Q₀ i)).choose_spec.2)
    (muArchTamSO Q₀ hQ) (muFin Q₀ fun _ => 1) (ratA_smul Q₀) (ratF_smul Q₀) (ratA_injective Q₀ m)
    (latHat_stable Q₀) 𝔉 hP (fun i y => exists_fd_stabArith Q₀ (dcRep Q₀ i) y) Φ
    (measurable_GInf_inv_smul Q₀ hΦ) hΦτ hE

/-! ### Totally real fields: the archimedean fibration is constructed -/

section TotallyReal

open QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.SphereLeray
open QuadFormsKB.Tamagawa.Measure.LerayComplex NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Classical

variable {k : ℕ} (Q₀ : QuadForm (𝓞 F) (k + 1)) (hQ : Q₀.Nondegenerate)

/-- $\sigma_w(m)$ at a real place $w$. -/
abbrev mR (m : F) (w : {w : InfinitePlace F // w.IsReal}) : ℝ := embedding_of_isReal w.2 m

theorem mR_ne_zero {m : F} (hm : m ≠ 0) (w : {w : InfinitePlace F // w.IsReal}) : mR m w ≠ 0 :=
  (map_ne_zero _).mpr hm

/-- **The archimedean quadric** $\{Q = m\}\subseteq V_\infty$: $\prod_wS_{\sigma_w(m)}(Q^{\sigma_w})$ at the real places
(and all of $\mathbb C^n$ at the complex places, of which there are none below). -/
def quadricInf (m : F) : Set (VInf F (k + 1)) :=
  (univ.pi fun w => sph (QRe Q₀ w) (mR m w)) ×ˢ (univ.pi fun _ => univ)

/-- The parameter space $T = \prod_wS_{\sigma_w(m)}$ (times a point when there are no complex places). -/
abbrev TInf (m : F) : Type :=
  (∀ w : {w : InfinitePlace F // w.IsReal}, Sph (QRe Q₀ w) (mR m w)) ×
    (∀ _j : {w : InfinitePlace F // w.IsComplex}, Fin (k + 1) → ℂ)

/-- The parametrization $T\to V_\infty$. -/
def τInf (m : F) : TInf Q₀ m → VInf F (k + 1) :=
  Prod.map (fun x w => (x w : Fin (k + 1) → ℝ)) (fun x j => id (x j))

theorem measurable_τInf (m : F) : Measurable (τInf Q₀ m) :=
  (measurable_pi_iff.mpr fun w => measurable_subtype_coe.comp (measurable_pi_apply w)).prodMap
    (measurable_pi_iff.mpr fun j => measurable_pi_apply j)

/-- **The Leray measure of the archimedean quadric**, $\bigotimes_w\sigma_{\sigma_w(m)}$ (`SphereLeray.sig`). -/
def sigInf (m : F) : Measure (TInf Q₀ m) :=
  (Measure.pi fun w => sig (QRe Q₀ w) (mR m w)).prod (Measure.pi fun _ => (0 : Measure (Fin (k + 1) → ℂ)))

theorem sigmaFinite_sigInf {m : F} (hm : m ≠ 0) : SigmaFinite (sigInf Q₀ m) := by
  have := fun w => sigmaFinite_sig (Q := QRe Q₀ w) (mR_ne_zero hm w)
  unfold sigInf
  infer_instance

/-- **The archimedean constant** $c_\infty(m) = c_F\prod_w|2\sigma_w(m)|^{-(n-1)}$ (as it comes out of the product). -/
def cInf (m : F) : ℝ≥0∞ :=
  ENNReal.ofReal (cF F (k + 1)) * ((∏ w, ENNReal.ofReal ((|2 * mR m w| ^ k)⁻¹)) *
    ∏ _j : {w : InfinitePlace F // w.IsComplex}, (1 : ℝ≥0∞))

theorem cInf_eq [IsEmpty {w : InfinitePlace F // w.IsComplex}] (m : F) :
    cInf (k := k) m = ENNReal.ofReal (cF F (k + 1)) * ∏ w, ENNReal.ofReal ((|2 * mR m w| ^ k)⁻¹) := by
  rw [cInf, Finset.prod_const_one, mul_one]

/-- Weil's complex-place factor `cxWeil` is $1$ when $F$ has no complex places. -/
theorem cxWeil_of_isEmpty [IsEmpty {w : InfinitePlace F // w.IsComplex}] (n : ℕ) : cxWeil F n = 1 := by
  have h : nrComplexPlaces F = 0 := Fintype.card_eq_zero
  rw [cxWeil, h, mul_zero, pow_zero]

/-- **The archimedean fibration of a totally real field** (any signature at each real place): the product over the
real places of `realArchFibration`, rescaled by $c_F$ (`muArchTamSO` has no complex-place factor `cxWeil` here).
Constructed, not assumed. -/
@[kb "weil1982" "§2.4 Lemma 2.4.1, Theorem 2.4.3, p. 25 (product over the archimedean places) [unverified page]"]
def totallyRealArchFibration [IsEmpty {w : InfinitePlace F // w.IsComplex}] {m : F} (hm : m ≠ 0) (hk : 1 ≤ k) :
    ArchFibration (muArchTamSO Q₀ hQ) (quadricInf Q₀ m) (sigInf Q₀ m) (τInf Q₀ m) (cInf (k := k) m) :=
  haveI := fun w => sigmaFinite_sig (Q := QRe Q₀ w) (mR_ne_zero hm w)
  ((ArchFibration.prod
    (ArchFibration.pi (fun _ => ENNReal.ofReal_ne_top) fun w =>
      realArchFibration (QRe Q₀ w) (gramDetR_QRe_ne_zero Q₀ hQ w) (mR_ne_zero hm w) hk)
    (ArchFibration.pi (σ := fun _ => (0 : Measure (Fin (k + 1) → ℂ))) (τ := fun _ => id)
      (P := fun _ => univ) (c := fun _ => 1)
      (μA := fun j => lerayMeasureC (QCx Q₀ j) (gramDetC_QCx_ne_zero Q₀ hQ j))
      (fun j => isEmptyElim j) fun j => isEmptyElim j)).smul (ENNReal.ofReal (cF F (k + 1)))).congrMeasure
    (by rw [muArchTamSO, cxWeil_of_isEmpty, mul_one]; rfl)

theorem ratA_mem_quadricInf (m : F) (η : RatSphere Q₀ m) : ratA Q₀ m η ∈ quadricInf Q₀ m := by
  refine ⟨fun w _ => ?_, fun j _ => trivial⟩
  have h : (ratA Q₀ m η).1 w = fun j => embedding_of_isReal w.2 (η.1 j) := by
    funext j
    simp only [ratA, archVec, diagVec_apply, diag_fst, mixedEmbedding_apply_isReal]
  show (QRe Q₀ w).eval ((ratA Q₀ m η).1 w) = mR m w
  rw [h, QRe, eval_map_comp]
  exact congrArg _ η.2

/-- **The theta integral for a totally real field, any signature, unconditional**:
$$\int_E\theta_{\Phi\otimes1_{\hat L}}\,d\mu = \mu_f(SO(\hat L))\cdot c_\infty(m)\cdot\sum_i\rho(M_i, m)\cdot
  \int_{\prod_wS_{\sigma_w(m)}}\Phi\,d\Big(\bigotimes_w\sigma_{\sigma_w(m)}\Big),\qquad
  c_\infty(m) = c_F\prod_w|2\sigma_w(m)|^{-(n-1)},$$
for $n\ge2$ and $m\ne0$, with $\rho(M_i, m)$ defined by the constructed fibration. -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form; totally real) [unverified]"]
theorem lintegral_theta_classical_totallyReal [IsEmpty {w : InfinitePlace F // w.IsComplex}] {m : F} (hm : m ≠ 0)
    (hk : 1 ≤ k) (Φ : VInf F (k + 1) → ℝ≥0∞) (hΦ : Measurable Φ) {E : Set (SOAdele Q₀)}
    (hE : IsFundamentalDomain (GammaSOAdele Q₀) E (muTam Q₀ hQ fun _ => 1)) :
    ∫⁻ g in E, thetaFn (ratA Q₀ m) (ratF Q₀ m) Φ (latHat F (k + 1)) g ∂muTam Q₀ hQ (fun _ => 1) =
      muFin Q₀ (fun _ => 1) (KSO Q₀) * cInf (k := k) m *
        (∑' i, repMeasure Q₀ hQ m (totallyRealArchFibration Q₀ hQ hm hk) i) *
        ∫⁻ x, Φ (τInf Q₀ m x) ∂sigInf Q₀ m := by
  have := sigmaFinite_sigInf Q₀ hm
  exact lintegral_theta_classical Q₀ hQ m (totallyRealArchFibration Q₀ hQ hm hk) (ratA_mem_quadricInf Q₀ m) Φ hΦ
    (hΦ.comp (measurable_τInf Q₀ m)) hE

/-- **The mean-value identity for a totally real field, any signature, unconditional**:
$$\Big(\int_E\theta\,d\mu\Big)\sum_iv(M_i) = \operatorname{covol}(\Gamma\backslash SO(V)(\mathbb A))\cdot c_\infty(m)\cdot
  \sum_i\rho(M_i, m)\cdot\int\Phi\,d\sigma_\infty.$$ -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form; totally real) [unverified]"]
theorem lintegral_theta_mul_tsum_unitVolume_totallyReal [IsEmpty {w : InfinitePlace F // w.IsComplex}] {m : F}
    (hm : m ≠ 0) (hk : 1 ≤ k) (Φ : VInf F (k + 1) → ℝ≥0∞) (hΦ : Measurable Φ) {E : Set (SOAdele Q₀)}
    (hE : IsFundamentalDomain (GammaSOAdele Q₀) E (muTam Q₀ hQ fun _ => 1)) :
    (∫⁻ g in E, thetaFn (ratA Q₀ m) (ratF Q₀ m) Φ (latHat F (k + 1)) g ∂muTam Q₀ hQ (fun _ => 1)) *
        ∑' i, unitVolume Q₀ hQ i =
      covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) * cInf (k := k) m *
        (∑' i, repMeasure Q₀ hQ m (totallyRealArchFibration Q₀ hQ hm hk) i) *
        ∫⁻ x, Φ (τInf Q₀ m x) ∂sigInf Q₀ m := by
  have := sigmaFinite_sigInf Q₀ hm
  exact lintegral_theta_mul_tsum_unitVolume Q₀ hQ m (totallyRealArchFibration Q₀ hQ hm hk)
    (ratA_mem_quadricInf Q₀ m) Φ hΦ (hΦ.comp (measurable_τInf Q₀ m)) hE

theorem cInf_ne_zero {m : F} (hm : m ≠ 0) : cInf (k := k) m ≠ 0 := by
  have hcF : 0 < cF F (k + 1) := Real.rpow_pos_of_pos (abs_pos.mpr (by exact_mod_cast discr_ne_zero F)) _
  refine mul_ne_zero (ENNReal.ofReal_pos.mpr hcF).ne' (mul_ne_zero ?_ ?_)
  · refine Finset.prod_ne_zero_iff.mpr fun w _ => (ENNReal.ofReal_pos.mpr ?_).ne'
    exact inv_pos.mpr (pow_pos (abs_pos.mpr (mul_ne_zero two_ne_zero (mR_ne_zero hm w))) k)
  · exact Finset.prod_ne_zero_iff.mpr fun _ _ => one_ne_zero

theorem cInf_ne_top (m : F) : cInf (k := k) m ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top
    (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top) (ENNReal.prod_ne_top fun _ _ => ENNReal.one_ne_top))

/-- The stabilizer measures of `totallyRealArchFibration` are right invariant (the stabilizers are unimodular). -/
theorem isMulRightInvariant_totallyRealArchFibration [IsEmpty {w : InfinitePlace F // w.IsComplex}] {m : F}
    (hm : m ≠ 0) (hk : 1 ≤ k) (y : VInf F (k + 1)) :
    ((totallyRealArchFibration Q₀ hQ hm hk).μH y).IsMulRightInvariant := by
  haveI := fun w => sigmaFinite_sig (Q := QRe Q₀ w) (mR_ne_zero hm w)
  exact ArchFibration.isMulRightInvariant_prod _ _ y
    (ArchFibration.isMulRightInvariant_pi _ _ y.1 fun w =>
      isMulRightInvariant_realStabMeasure (QRe Q₀ w) (gramDetR_QRe_ne_zero Q₀ hQ w) (mR_ne_zero hm w) (y.1 w))
    (ArchFibration.isMulRightInvariant_pi _ _ y.2 fun j => isEmptyElim j)

/-- **The measure of representations is canonical** (totally real $F$): computed with any archimedean fibration of
$\mu_\infty$ over the same quadric, Leray measure and constant, $\rho(M_i, m)$ is the same as with the constructed
`totallyRealArchFibration` (provided the Leray measure of the quadric is nonzero). So $\rho(M_i, m)$ depends only on
$\mu_\infty$ and $\sigma_\infty$, not on the sections used to build the coordinates. -/
theorem repMeasure_eq_totallyReal [IsEmpty {w : InfinitePlace F // w.IsComplex}] {m : F} (hm : m ≠ 0) (hk : 1 ≤ k)
    (𝔉' : ArchFibration (muArchTamSO Q₀ hQ) (quadricInf Q₀ m) (sigInf Q₀ m) (τInf Q₀ m) (cInf (k := k) m))
    (hσ : sigInf Q₀ m ≠ 0) (i : DC Q₀) :
    repMeasure Q₀ hQ m 𝔉' i = repMeasure Q₀ hQ m (totallyRealArchFibration Q₀ hQ hm hk) i := by
  have := sigmaFinite_sigInf Q₀ hm
  refine (repMeasureOf_eq (totallyRealArchFibration Q₀ hQ hm hk) 𝔉' (cInf_ne_zero hm) (cInf_ne_top m) hσ
    (unitGroup Q₀ i) (reps Q₀ m i) ?_ fun y _ => isMulRightInvariant_totallyRealArchFibration Q₀ hQ hm hk y).symm
  rintro _ ⟨η, -, rfl⟩
  exact ratA_mem_quadricInf Q₀ m η

end TotallyReal

end QuadFormsKB.Tamagawa.Indefinite
