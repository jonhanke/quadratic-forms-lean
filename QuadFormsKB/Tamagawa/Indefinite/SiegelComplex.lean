/-
# Siegel's formula for indefinite forms over every number field

**Layer:** number fields. $F$ **any** number field ($r_1$ real and $r_2$ complex places), $Q_0$ a nondegenerate quadratic
form over $\mathcal O_F$ in $N = k+1\ge4$ variables of any signature, $m\in\mathcal O_F\setminus0$ with a rational point $\xi$ on
$Q_0 = m$. This removes `[IsTotallyReal F]` from `siegelIndefinite_release_totallyReal_uncond`.

Write $|x|_w$ for the normalized absolute value at an archimedean place: $|\sigma_wx|$ at a real place, $|\sigma_wx|^2$ at a
complex place. At a complex place we use **Weil's normalization** (1982, §2.2: $|dz\wedge d\bar z| = 2\,dx\,dy$): the Haar
measure of $SO_N(\mathbb C)$ is $2^{N(N-1)/2}$ times `lerayMeasureC` (this is `cxWeil`, already in `muArchTamSO`), and the Leray
measure $dx/dQ$ of the complex quadric $\{Q = c\}$ is $2^{N-1}$ times `sigC` ($2^N$ for $\omega_{\mathbb C^N}$ over $2$ for $dQ$).

**Defines**
* `TInfNF`, `τInfNF`, `quadricInfNF`: the archimedean quadric $\prod_{w\ \mathrm{real}}\{Q^{\sigma_w} = \sigma_wm\}\times
  \prod_{w\ \mathrm{complex}}\{Q^{\sigma_w} = \sigma_wm\}\subseteq V_\infty$;
* **`sigInfNF`**: its Leray measure $\sigma_\infty = \bigotimes_{w\ \mathrm{real}}\sigma_w\otimes\bigotimes_{w\ \mathrm{complex}}2^{N-1}\sigma_w$
  (Weil's normalization at the complex places);
* **`cInfNF`**: $c_\infty(m) = c_F(N)\prod_{w\mid\infty}|2m|_w^{-(N-1)}$. No Gamma factor occurs in the measure form: the
  archimedean density is absorbed in the fibration;
* **`archFibrationNF`**: the archimedean fibration of $\mu_\infty$ = `muArchTamSO` over the quadric, constant $c_\infty(m)$: the
  product of `realArchFibration` at the real places and of `complexArchFibration` (Weil-normalized) at the complex places.

**Proves**
* `adelicSphereDensitiesNF`: the input `AdelicSphereDensities` for every number field (from the box formula with the complex
  places, `map_projRC_restrict_boxGNF`; its factor $2^{(N-1)r_2}$ is Weil's normalization of $\sigma_\infty$);
* **`siegelIndefinite_uncond`** (headline):
  $$c_\infty(m)\sum_i\rho(M_i, m) = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\cdot\sum_iv(M_i).$$
-/
import QuadFormsKB.Tamagawa.Indefinite.FormsIndefinite
import QuadFormsKB.Tamagawa.Indefinite.ArchConjC
import QuadFormsKB.Tamagawa.Measure.Weil.SphereBoxNF
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereDensitiesProof

open MeasureTheory Measure MulAction Set NumberField IsDedekindDomain
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
open QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.SphereLeray
open QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Tamagawa.Measure.SphereLerayC
open NumberField.InfinitePlace NumberField.mixedEmbedding

/-! ### Generic facts on archimedean fibrations -/

section Generic

variable {A : Type*} [Group A] [MeasurableSpace A] [MeasurableMul A] {μA : Measure A}
  {Y : Type*} [MulAction A Y] {T : Type*} [MeasurableSpace T] {P : Set Y} {σ : Measure T} {τ : T → Y} {c : ℝ≥0∞}

/-- An archimedean fibration with the measure $\sigma$ replaced by an equal measure. -/
def ArchFibration.congrSigma (𝔉 : ArchFibration μA P σ τ c) {σ' : Measure T} (h : σ = σ') :
    ArchFibration μA P σ' τ c := h ▸ 𝔉

theorem ArchFibration.congrSigma_μH (𝔉 : ArchFibration μA P σ τ c) {σ' : Measure T} (h : σ = σ') :
    (𝔉.congrSigma h).μH = 𝔉.μH := by
  subst h; rfl

/-- **The base measure of a fibration is nonzero** when the group measure is nonzero and the quadric is nonempty. -/
theorem ArchFibration.sigma_ne_zero (𝔉 : ArchFibration μA P σ τ c) (hμ : μA ≠ 0) {y : Y} (hy : y ∈ P) : σ ≠ 0 := by
  intro h0
  apply hμ
  have := 𝔉.sigmaFinite y
  rw [← Measure.measure_univ_eq_zero, 𝔉.fib y hy, Measure.smul_apply,
    Measure.map_apply (𝔉.coord y hy).coord.measurable MeasurableSet.univ, Set.preimage_univ, ← Set.univ_prod_univ,
    Measure.prod_prod]
  have h1 : σ univ = 0 := by rw [h0]; rfl
  simp [h1]

end Generic

section NF

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {k : ℕ} (Q₀ : QuadForm (𝓞 F) (k + 1)) (hQ : Q₀.Nondegenerate)

/-! ### The archimedean quadric and its Leray measure -/

/-- $\sigma_w(m)$ at a complex place $w$. -/
abbrev mC (m : F) (w : {w : InfinitePlace F // w.IsComplex}) : ℂ := σC w m

theorem mC_ne_zero {m : F} (hm : m ≠ 0) (w : {w : InfinitePlace F // w.IsComplex}) : mC m w ≠ 0 :=
  (map_ne_zero _).mpr hm

/-- The parameter space $T_\infty = \prod_{w\ \mathrm{real}}S_{\sigma_w(m)}\times\prod_{w\ \mathrm{complex}}S_{\sigma_w(m)}$. -/
abbrev TInfNF (m : F) : Type :=
  (∀ w : {w : InfinitePlace F // w.IsReal}, Sph (QRe Q₀ w) (σR w m)) ×
    (∀ w : {w : InfinitePlace F // w.IsComplex}, SphC (QCx Q₀ w) (mC m w))

/-- The inclusion $T_\infty\to V_\infty$. -/
def τInfNF (m : F) : TInfNF Q₀ m → VInf F (k + 1) :=
  Prod.map (fun x w => ((x w : Sph (QRe Q₀ w) (σR w m)) : Fin (k + 1) → ℝ))
    (fun x w => ((x w : SphC (QCx Q₀ w) (mC m w)) : Fin (k + 1) → ℂ))

theorem measurable_τInfNF (m : F) : Measurable (τInfNF Q₀ m) :=
  (measurable_pi_iff.mpr fun w => measurable_subtype_coe.comp (measurable_pi_apply w)).prodMap
    (measurable_pi_iff.mpr fun w => measurable_subtype_coe.comp (measurable_pi_apply w))

/-- **The archimedean quadric** $\{Q = m\}\subseteq V_\infty$, at the real and the complex places. -/
def quadricInfNF (m : F) : Set (VInf F (k + 1)) :=
  (univ.pi fun w => sph (QRe Q₀ w) (σR w m)) ×ˢ (univ.pi fun w => sphC (QCx Q₀ w) (mC m w))

/-- **The Leray measure of the archimedean quadric in Weil's normalization**:
$\sigma_\infty = \bigotimes_{w\ \mathrm{real}}\sigma_{\sigma_w(m)}\otimes\bigotimes_{w\ \mathrm{complex}}2^{N-1}\sigma_{\sigma_w(m)}$, $N = k+1$,
with $\sigma$ = `sig` (real) and `sigC` (complex, built from $dx\,dy$; the factor $2^{N-1}$ converts it to
$|dz\wedge d\bar z| = 2\,dx\,dy$). -/
@[kb "weil1982" "§2.2 (gauge forms; |dz∧dz̄| at complex places), §2.4 (measure on G/H) [unverified]"]
def sigInfNF (m : F) : Measure (TInfNF Q₀ m) :=
  (Measure.pi fun w => sig (QRe Q₀ w) (σR w m)).prod
    (Measure.pi fun w => ((2 : ℝ≥0∞) ^ k) • sigC (QCx Q₀ w) (mC m w))

theorem sigmaFinite_sigInfNF {m : F} (hm : m ≠ 0) : SigmaFinite (sigInfNF Q₀ m) := by
  have := fun w => sigmaFinite_sig (Q := QRe Q₀ w) (mR_ne_zero hm w)
  have := fun w => sigmaFinite_sigC (Q := QCx Q₀ w) (mC_ne_zero hm w) (Nat.succ_pos k)
  have := fun w => sigmaFinite_smul (sigC (QCx Q₀ w) (mC m w)) (c := (2 : ℝ≥0∞) ^ k)
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  unfold sigInfNF
  infer_instance

open Classical in
/-- **The archimedean constant over every number field**
$c_\infty(m) = c_F(N)\prod_{w\ \mathrm{real}}|2\sigma_w(m)|^{-(N-1)}\prod_{w\ \mathrm{complex}}|2\sigma_w(m)|^{-2(N-1)}$
$= c_F(N)\prod_{w\mid\infty}|2m|_w^{-(N-1)}$, $N = k+1$, $c_F(N) = |d_F|^{-N(N-1)/4}$ (`cF`). -/
@[kb "siegel1936" "Indefinite quadratische Formen; the archimedean factor (every number field) [unverified]"]
def cInfNF (m : F) : ℝ≥0∞ :=
  ENNReal.ofReal (cF F (k + 1)) * ((∏ w, ENNReal.ofReal ((|2 * mR m w| ^ k)⁻¹)) *
    ∏ w, ENNReal.ofReal ((‖2 * mC m w‖ ^ (2 * k))⁻¹))

theorem cInfNF_ne_zero {m : F} (hm : m ≠ 0) : cInfNF (k := k) m ≠ 0 := by
  have hcF : 0 < cF F (k + 1) := Real.rpow_pos_of_pos (abs_pos.mpr (by exact_mod_cast discr_ne_zero F)) _
  refine mul_ne_zero (ENNReal.ofReal_pos.mpr hcF).ne' (mul_ne_zero ?_ ?_)
  · refine Finset.prod_ne_zero_iff.mpr fun w _ => (ENNReal.ofReal_pos.mpr ?_).ne'
    exact inv_pos.mpr (pow_pos (abs_pos.mpr (mul_ne_zero two_ne_zero (mR_ne_zero hm w))) k)
  · refine Finset.prod_ne_zero_iff.mpr fun w _ => (ENNReal.ofReal_pos.mpr ?_).ne'
    exact inv_pos.mpr (pow_pos (norm_pos_iff.mpr (mul_ne_zero two_ne_zero (mC_ne_zero hm w))) _)

theorem cInfNF_ne_top (m : F) : cInfNF (k := k) m ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top
    (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top) (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top))

/-! ### Weil's normalization at the complex places -/

/-- $(k+1)k/2 = k(k-1)/2 + k$ (dimensions of $SO_{k+1}$ and $SO_k$). -/
theorem dim_so_succ (k : ℕ) : (k + 1) * (k + 1 - 1) / 2 = k * (k - 1) / 2 + k := by
  have h : (k + 1) * (k + 1 - 1) = k * (k - 1) + k * 2 := by
    rcases k with _ | j
    · rfl
    · simp only [Nat.add_sub_cancel]; ring
  rw [h, Nat.add_mul_div_right _ _ two_pos]

variable (F) in
/-- $\mathrm{cxWeil}(N) = 2^{(N-1)r_2}\,\mathrm{cxWeil}(N-1)$. -/
theorem cxWeil_succ (k : ℕ) : cxWeil F (k + 1) = (2 : ℝ) ^ (k * nrComplexPlaces F) * cxWeil F k := by
  rw [cxWeil, cxWeil, dim_so_succ, add_mul, pow_add, mul_comm]

variable (F) in
open Classical in
theorem ofReal_cxWeil_succ (k : ℕ) :
    ENNReal.ofReal (cxWeil F (k + 1)) =
      (∏ _w : {w : InfinitePlace F // w.IsComplex}, (2 : ℝ≥0∞) ^ k) * ENNReal.ofReal (cxWeil F k) := by
  rw [cxWeil_succ, ENNReal.ofReal_mul (by positivity), Finset.prod_const, Finset.card_univ, ← pow_mul,
    ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]

variable (F) in
open Classical in
/-- $\mathrm{cxWeil}(N) = \prod_{w\ \mathrm{complex}}2^{N(N-1)/2}$. -/
theorem ofReal_cxWeil_eq_prod (n : ℕ) :
    ENNReal.ofReal (cxWeil F n) = ∏ _w : {w : InfinitePlace F // w.IsComplex}, (2 : ℝ≥0∞) ^ (n * (n - 1) / 2) := by
  rw [cxWeil, Finset.prod_const, Finset.card_univ, ← pow_mul, ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]

/-! ### The archimedean fibration over every number field -/

/-- **The complex-place fibration in Weil's normalization**: for $Q$ nondegenerate over $\mathbb C$ in $N = k+1\ge2$
variables and $c\ne0$,
$$2^{N(N-1)/2}\mu_Q = |2c|^{-2(N-1)}\,\mathrm{coord}_*\big(2^{N-1}\sigma_c\otimes2^{(N-1)(N-2)/2}\mu_{H_y}\big),$$
the rescaling of `complexArchFibration`. -/
def complexArchFibrationW (Q : QuadForm ℂ (k + 1)) (hQ : gramDetC Q ≠ 0) {c : ℂ} (hc : c ≠ 0) (hk : 1 ≤ k) :
    ArchFibration ((2 : ℝ≥0∞) ^ ((k + 1) * (k + 1 - 1) / 2) • lerayMeasureC Q hQ) (sphC Q c)
      (((2 : ℝ≥0∞) ^ k) • sigC Q c) Subtype.val (ENNReal.ofReal ((‖2 * c‖ ^ (2 * k))⁻¹)) :=
  ((complexArchFibration Q hQ hc hk).smul ((2 : ℝ≥0∞) ^ ((k + 1) * (k + 1 - 1) / 2))).rescale
    ((2 : ℝ≥0∞) ^ (k * (k - 1) / 2)) ((2 : ℝ≥0∞) ^ k) (ENNReal.ofReal ((‖2 * c‖ ^ (2 * k))⁻¹))
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) (by
      have hpos : 0 < ‖2 * c‖ ^ (2 * k) := pow_pos (norm_pos_iff.mpr (mul_ne_zero two_ne_zero hc)) _
      rw [dim_so_succ, pow_add, ← ENNReal.ofReal_coe_nnreal]
      push_cast
      rw [ENNReal.ofReal_inv_of_pos hpos]
      ring)

open Classical in
/-- `muArchTamSO` as the product of the real Leray measures and of the Weil-normalized complex ones, times $c_F(N)$. -/
theorem muArchTamSO_eq_prodW :
    muArchTamSO Q₀ hQ = ENNReal.ofReal (cF F (k + 1)) •
      ((Measure.pi fun w => lerayMeasure (QRe Q₀ w) (gramDetR_QRe_ne_zero Q₀ hQ w)).prod
        (Measure.pi fun w => (2 : ℝ≥0∞) ^ ((k + 1) * (k + 1 - 1) / 2) •
          lerayMeasureC (QCx Q₀ w) (gramDetC_QCx_ne_zero Q₀ hQ w))) := by
  have := fun w => isHaarMeasure_lerayMeasureC (Q := QCx Q₀ w) (gramDetC_QCx_ne_zero Q₀ hQ w)
  rw [pi_smul _ _ fun _ => ENNReal.pow_ne_top ENNReal.ofNat_ne_top, Measure.prod_smul_right, smul_smul,
    ← ofReal_cxWeil_eq_prod, ← ENNReal.ofReal_mul (cF_pos' _).le, muArchTamSO]
  rfl

/-- **The archimedean fibration over every number field** (any signature at each real place; Weil 1982, Lemma 2.4.1 /
Thm 2.4.3 at every archimedean place): the product of `realArchFibration` at the real places and of the Weil-normalized
`complexArchFibration` at the complex places, times $c_F(N)$. Over the quadric $\{Q = m\}\subseteq V_\infty$ with the measure
`sigInfNF` and the constant $c_\infty(m)$ = `cInfNF`. Constructed, not assumed. -/
@[kb "weil1982" "§2.4 Lemma 2.4.1, Theorem 2.4.3, p. 25 (product over the archimedean places) [unverified page]"]
def archFibrationNF {m : F} (hm : m ≠ 0) (hk : 1 ≤ k) :
    ArchFibration (muArchTamSO Q₀ hQ) (quadricInfNF Q₀ m) (sigInfNF Q₀ m) (τInfNF Q₀ m) (cInfNF (k := k) m) :=
  haveI := fun w => sigmaFinite_sig (Q := QRe Q₀ w) (mR_ne_zero hm w)
  haveI := fun w => sigmaFinite_sigC (Q := QCx Q₀ w) (mC_ne_zero hm w) (Nat.succ_pos k)
  haveI := fun w => sigmaFinite_smul (sigC (QCx Q₀ w) (mC m w)) (c := (2 : ℝ≥0∞) ^ k)
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  ((ArchFibration.prod
    (ArchFibration.pi (fun _ => ENNReal.ofReal_ne_top) fun w =>
      realArchFibration (QRe Q₀ w) (gramDetR_QRe_ne_zero Q₀ hQ w) (mR_ne_zero hm w) hk)
    (ArchFibration.pi (fun _ => ENNReal.ofReal_ne_top) fun w =>
      complexArchFibrationW (QCx Q₀ w) (gramDetC_QCx_ne_zero Q₀ hQ w) (mC_ne_zero hm w) hk)).smul
    (ENNReal.ofReal (cF F (k + 1)))).congrMeasure (muArchTamSO_eq_prodW Q₀ hQ).symm

theorem ratA_mem_quadricInfNF (m : F) (η : RatSphere Q₀ m) : ratA Q₀ m η ∈ quadricInfNF Q₀ m := by
  refine ⟨fun w _ => (ratA_mem_quadricInf Q₀ m η).1 w (mem_univ w), fun w _ => ?_⟩
  have h : (ratA Q₀ m η).2 w = fun j => σC w (η.1 j) := by
    funext j
    simp only [ratA, archVec, diagVec_apply, diag_snd, mixedEmbedding_apply_isComplex]
    rfl
  show (QCx Q₀ w).eval ((ratA Q₀ m η).2 w) = mC m w
  rw [h, QCx, eval_map_comp]
  exact congrArg _ η.2

/-! ### The densities over every number field -/

namespace DensitiesNF

variable {Q₀} {ρ : F}

theorem τInfNF_projRC (y : adelicSphere Q₀ ρ) : τInfNF Q₀ ρ (AdelicSphereSetup.projRC Q₀ ρ y) = archVec y.1 :=
  rfl

theorem boxGNF_int_eq :
    AdelicSphereSetup.boxGNF Q₀ ρ (fun _ => univ) (fun _ => univ) (fun v => AdelicSphereSetup.intSph Q₀ ρ v) =
      AdelicSphereSetup.boxA Q₀ ρ fun _ => univ := by
  ext y
  simp [AdelicSphereSetup.boxGNF, AdelicSphereSetup.boxA, AdelicSphereSetup.intSph]

theorem testFn_eqNF (Φ : VInf F (k + 1) → ℝ≥0∞) (y : adelicSphere Q₀ ρ) :
    testFn Φ y.1 = (AdelicSphereSetup.boxGNF Q₀ ρ (fun _ => univ) (fun _ => univ)
      (fun v => AdelicSphereSetup.intSph Q₀ ρ v)).indicator
        (fun y => Φ (τInfNF Q₀ ρ (AdelicSphereSetup.projRC Q₀ ρ y))) y := by
  rw [boxGNF_int_eq]
  have hiff : Indefinite.finVec y.1 ∈ latHat F (k + 1) ↔ y ∈ AdelicSphereSetup.boxA Q₀ ρ fun _ => univ := by
    simp only [latHat, Indefinite.finVec, AdelicSphereSetup.boxA, mem_setOf_eq, mem_univ, implies_true, true_and,
      IntVec, adV, HeightOneSpectrum.mem_adicCompletionIntegers]
    exact forall_comm
  have e : (fun y => Φ (τInfNF Q₀ ρ (AdelicSphereSetup.projRC Q₀ ρ y))) =
      fun y : adelicSphere Q₀ ρ => Φ (archVec y.1) := rfl
  rw [testFn, e]
  by_cases h : y ∈ AdelicSphereSetup.boxA Q₀ ρ fun _ => univ
  · rw [indicator_of_mem h, indicator_of_mem (hiff.mpr h), Pi.one_apply, mul_one]
  · rw [indicator_of_notMem h, indicator_of_notMem (mt hiff.mp h), mul_zero]

end DensitiesNF

open Classical in
/-- `sigInfNF` is $2^{(N-1)r_2}$ times the product of the $dx\,dy$-normalized Leray measures. -/
theorem sigInfNF_eq (m : F) (hm : m ≠ 0) :
    sigInfNF Q₀ m = (∏ _w : {w : InfinitePlace F // w.IsComplex}, (2 : ℝ≥0∞) ^ k) •
      ((Measure.pi fun w => sig (QRe Q₀ w) (σR w m)).prod (Measure.pi fun w => sigC (QCx Q₀ w) (mC m w))) := by
  have := fun w => sigmaFinite_sigC (Q := QCx Q₀ w) (mC_ne_zero hm w) (Nat.succ_pos k)
  rw [sigInfNF, pi_smul _ _ fun _ => ENNReal.pow_ne_top ENNReal.ofNat_ne_top, Measure.prod_smul_right]

/-- **`AdelicSphereDensities` over every number field** ($m\in\mathcal O_F\setminus0$, $N\ge4$):
$\int_{T(m)_{\mathbb A}}\Phi\otimes1_{\hat L}\,d\sigma_{\mathbb A} = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)
\int_{T_\infty}\Phi\,d\sigma_\infty$, $\sigma_\infty$ = `sigInfNF` (Weil's normalization at the complex places). -/
@[kb "weil1965" "Sur la formule de Siegel: Tamagawa measure of the sphere = ∏ local densities [unverified]"]
theorem adelicSphereDensitiesNF (hk : 3 ≤ k) {m : 𝓞 F} (S : AdelicSphereSetup Q₀ (m : F)) (hm : (m : F) ≠ 0) :
    AdelicSphereDensities Q₀ (S.sphereData hm hQ hk) (sigInfNF Q₀ (m : F)) (τInfNF Q₀ (m : F)) := by
  refine ⟨fun Φ hΦ => ?_⟩
  have := fun w => sigmaFinite_sig (Q := QRe Q₀ w) (mR_ne_zero hm w)
  have := fun w => sigmaFinite_sigC (Q := QCx Q₀ w) (mC_ne_zero hm w) (Nat.succ_pos k)
  have hfin : ∀ v, AdelicSphereSetup.sigV Q₀ (m : F) hQ v (AdelicSphereSetup.intSph Q₀ (m : F) v) ≠ ⊤ := fun v => by
    rw [AdelicSphereSetup.sigV_intSph hQ m hm v]; exact ENNReal.ofReal_ne_top
  have hW := AdelicSphereSetup.measurableSet_boxGNF (Q₀ := Q₀) (ρ := (m : F)) (fun _ => univ)
    (fun _ => MeasurableSet.univ) (fun _ => univ) (fun _ => MeasurableSet.univ)
    (fun v => AdelicSphereSetup.intSph Q₀ (m : F) v)
    (fun v => (measurableSet_intSph v))
  have hf : Measurable fun t => Φ (τInfNF Q₀ (m : F) t) := hΦ.comp (measurable_τInfNF Q₀ _)
  show ∫⁻ x, testFn Φ x.1 ∂S.sphereMeasure hm hQ hk = _
  simp_rw [DensitiesNF.testFn_eqNF]
  rw [lintegral_indicator hW, ← lintegral_map (f := fun t => Φ (τInfNF Q₀ (m : F) t)) hf
    AdelicSphereSetup.measurable_projRC,
    S.map_projRC_restrict_boxGNF hm hQ hk ∅ (fun v => AdelicSphereSetup.intSph Q₀ (m : F) v)
      (fun v => measurableSet_intSph v) (fun _ _ => rfl) hfin hfin,
    Measure.prod_smul_left, lintegral_smul_measure, sigInfNF_eq Q₀ (m : F) hm, lintegral_smul_measure]
  simp only [smul_eq_mul]
  rw [← mul_assoc]
  congr 1
  rw [AdelicSphereSetup.boxConstNF, ← AdelicSphereSetup.boxConst_eq hQ m hm]
  have hc1 : 0 < cF F (k + 1) := cF_pos' _
  have hc2 : 0 < cF F k := cF_pos' _
  have hw2 : 0 < cxWeil F k := cxWeil_pos
  have hP : 0 ≤ ∏' v, (AdelicSphereSetup.sigV Q₀ (m : F) hQ v (AdelicSphereSetup.intSph Q₀ (m : F) v)).toReal :=
    tprod_nonneg fun v => ENNReal.toReal_nonneg
  have e : cF F (k + 1) * cxWeil F (k + 1) / (cF F k * cxWeil F k) *
      ∏' v, (AdelicSphereSetup.sigV Q₀ (m : F) hQ v (AdelicSphereSetup.intSph Q₀ (m : F) v)).toReal =
      (cxWeil F (k + 1) / cxWeil F k) *
        (cF F (k + 1) / cF F k * ∏' v, (AdelicSphereSetup.sigV Q₀ (m : F) hQ v (AdelicSphereSetup.intSph Q₀ (m : F) v)).toReal) := by
    field_simp
  rw [e, ENNReal.ofReal_mul (div_nonneg cxWeil_pos.le hw2.le), cxWeil_succ, mul_div_assoc,
    div_self hw2.ne', mul_one, ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, Finset.prod_const,
    Finset.card_univ, ← pow_mul, mul_comm]

/-! ### The test function and the headline -/

include hQ in
/-- **The archimedean Leray measure of the quadric is nonzero** when $Q = m$ has a solution over $F$ (every number field):
otherwise the fibration would make $\mu_\infty$ zero. -/
theorem sigInfNF_ne_zero {m : F} (hm : m ≠ 0) (hk : 1 ≤ k) (η : RatSphere Q₀ m) : sigInfNF Q₀ m ≠ 0 :=
  (archFibrationNF Q₀ hQ hm hk).sigma_ne_zero (muArchTamSO_ne_zero' Q₀ hQ) (ratA_mem_quadricInfNF Q₀ m η)

include hQ in
/-- **A test function with $0 < \int\Phi\,d\sigma_\infty < \infty$** (every number field, $Q = m$ solvable over $F$): the
indicator of a large bounded piece of the archimedean quadric. -/
theorem exists_testFnNF {m : F} (hm : m ≠ 0) (hk : 1 ≤ k) (η : RatSphere Q₀ m) :
    ∃ Φ : VInf F (k + 1) → ℝ≥0∞, Measurable Φ ∧ ∫⁻ x, Φ (τInfNF Q₀ m x) ∂sigInfNF Q₀ m ≠ 0 ∧
      ∫⁻ x, Φ (τInfNF Q₀ m x) ∂sigInfNF Q₀ m ≠ ⊤ := by
  have := fun w => sigmaFinite_sig (Q := QRe Q₀ w) (mR_ne_zero hm w)
  have := fun w => sigmaFinite_sigC (Q := QCx Q₀ w) (mC_ne_zero hm w) (Nat.succ_pos k)
  have := fun w => sigmaFinite_smul (sigC (QCx Q₀ w) (mC m w)) (c := (2 : ℝ≥0∞) ^ k)
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  let S : ℕ → Set (VInf F (k + 1)) := fun R => {x | (∀ w, ‖x.1 w‖ ≤ R) ∧ ∀ w, ‖x.2 w‖ ≤ R}
  have hS : ∀ R, MeasurableSet (S R) := fun R => by
    simp only [S, ofPred_and, ofPred_forall]
    exact (MeasurableSet.iInter fun w => measurableSet_le
      (continuous_norm.comp ((continuous_apply w).comp continuous_fst)).measurable measurable_const).inter
      (MeasurableSet.iInter fun w => measurableSet_le
      (continuous_norm.comp ((continuous_apply w).comp continuous_snd)).measurable measurable_const)
  have hpre : ∀ R, τInfNF Q₀ m ⁻¹' S R =
      (univ.pi fun w => {y : Sph (QRe Q₀ w) (σR w m) | ‖(y : Fin (k + 1) → ℝ)‖ ≤ R}) ×ˢ
        (univ.pi fun w => ballS (QCx Q₀ w) (mC m w) R) := by
    intro R; ext t; simp [S, τInfNF, ballS]
  have hfin : ∀ R, sigInfNF Q₀ m (τInfNF Q₀ m ⁻¹' S R) ≠ ⊤ := by
    intro R
    rw [hpre, sigInfNF, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi]
    refine ENNReal.mul_ne_top (ENNReal.prod_ne_top fun w _ => ?_) (ENNReal.prod_ne_top fun w _ => ?_)
    · rw [sig, Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (nu_bounded_lt_top (mR_ne_zero hm w) R).ne
    · rw [Measure.smul_apply, smul_eq_mul, sigC, Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
        (ENNReal.mul_ne_top ENNReal.coe_ne_top (nuC_ballS_lt_top (mC_ne_zero hm w) (Nat.succ_pos k) R).ne)
  have hcov : ⋃ R : ℕ, τInfNF Q₀ m ⁻¹' S R = univ := by
    refine eq_univ_of_forall fun t => mem_iUnion.mpr ?_
    obtain ⟨R, hR⟩ := exists_nat_ge ((∑ w, ‖(τInfNF Q₀ m t).1 w‖) + ∑ w, ‖(τInfNF Q₀ m t).2 w‖)
    refine ⟨R, fun w => ?_, fun w => ?_⟩
    · exact ((Finset.single_le_sum (fun w _ => norm_nonneg ((τInfNF Q₀ m t).1 w)) (Finset.mem_univ w)).trans
        (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _))).trans hR
    · exact ((Finset.single_le_sum (fun w _ => norm_nonneg ((τInfNF Q₀ m t).2 w)) (Finset.mem_univ w)).trans
        (le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => norm_nonneg _))).trans hR
  obtain ⟨R, hR⟩ : ∃ R : ℕ, sigInfNF Q₀ m (τInfNF Q₀ m ⁻¹' S R) ≠ 0 := by
    by_contra h
    push Not at h
    apply sigInfNF_ne_zero Q₀ hQ hm hk η
    rw [← Measure.measure_univ_eq_zero, ← hcov]
    exact measure_iUnion_null h
  have hI : ∫⁻ x, (S R).indicator 1 (τInfNF Q₀ m x) ∂sigInfNF Q₀ m = sigInfNF Q₀ m (τInfNF Q₀ m ⁻¹' S R) := by
    rw [← lintegral_indicator_one ((measurable_τInfNF Q₀ m) (hS R))]
    rfl
  exact ⟨(S R).indicator 1, measurable_one.indicator (hS R), hI ▸ hR, hI ▸ hfin R⟩

/-- **Siegel's formula for indefinite forms over every number field — unconditional** (Siegel 1936, Hauptsatz for
indefinite forms, measure of representations; Weil 1965): for $F$ a number field, $Q_0$ nondegenerate over $\mathcal O_F$ in
$N = k+1\ge4$ variables of any signature, $m\in\mathcal O_F\setminus0$ with a rational point $\xi$ on $Q_0 = m$,
$$c_\infty(m)\sum_i\rho(M_i, m) = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\cdot\sum_iv(M_i),$$
the sums over the proper classes $M_i$ in the genus of $L = \mathcal O_F^N$, $v(M_i)$ = `unitVolume`, $\rho(M_i, m)$ =
`repMeasure` for the archimedean fibration `archFibrationNF` (the quotient measure $\mu_\infty/\sigma_\infty$ on the stabilizers,
$\sigma_\infty$ = `sigInfNF` the Leray measure of $\{Q = m\}\subseteq V_\infty$ in Weil's normalization), and
$c_\infty(m) = c_F(N)\prod_{w\mid\infty}|2m|_w^{-(N-1)}$ (`cInfNF`, normalized absolute values). No hypotheses beyond these; at a
complex place every form is indefinite, and at the real places any signature is allowed. -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form; every number field) [unverified]"]
theorem siegelIndefinite_uncond {Q₀ : QuadForm (𝓞 F) (k + 1)} (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k) {m : 𝓞 F}
    (hm : (m : F) ≠ 0) (ξ : RatSphere Q₀ (m : F)) :
    cInfNF (k := k) (m : F) * ∑' i, repMeasure Q₀ hQ (m : F) (archFibrationNF Q₀ hQ hm (by omega)) i =
      ENNReal.ofReal (finDensityProduct Q₀ m) * ∑' i, unitVolume Q₀ hQ i := by
  obtain ⟨S⟩ := exists_adelicSphereSetup hQ hm ξ (by omega)
  have := sigmaFinite_sigInfNF Q₀ hm
  obtain ⟨Φ, hΦ, h0, htop⟩ := exists_testFnNF Q₀ hQ hm (by omega) ξ
  exact siegelIndefinite_classical Q₀ hQ (by omega) hm (archFibrationNF Q₀ hQ hm (by omega))
    (ratA_mem_quadricInfNF Q₀ _) (S.sphereFibration hm hQ hk) (adelicSphereDensitiesNF Q₀ hQ hk S hm)
    (tauTwoAll_release_uncond (k + 1) (by omega) Q₀ hQ) (tauTwoAll_release_uncond k hk _ _) Φ hΦ
    (hΦ.comp (measurable_τInfNF Q₀ _)) h0 htop

end NF

end QuadFormsKB.Tamagawa.Indefinite
