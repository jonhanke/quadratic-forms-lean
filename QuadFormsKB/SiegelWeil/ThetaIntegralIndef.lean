/-
# The theta integral of an indefinite form over a number field, by orbits

**Layer:** global, $F$ any number field (real and complex places), $Q_0$ nondegenerate over $\mathcal O_F$ in
$N = k+1$ variables, any signature; $V = F^N$, $L = \mathcal O_F^N$, $G = SO(V)$ with Weil's Tamagawa measure $\mu$
(`muTam`), $\Phi\ge0$ measurable on $V_\infty$ and the test function $\Phi\otimes1_{\hat L}$ (`testFn`).

The **theta integral** (Weil 1965, *Sur la formule de Siegel*, §§ 1–4 [unverified]; Kudla, *Some extensions of the
Siegel–Weil formula*, §1 [unverified]) is the mean value over $G(F)\backslash G(\mathbb A)$ of the full theta function
$$\theta(g) = \sum_{\xi\in V(F)}(\Phi\otimes1_{\hat L})(g^{-1}\xi)\qquad(\texttt{thetaFull}),\qquad
  I(\Phi) = \frac1{\operatorname{vol}(G(F)\backslash G(\mathbb A))}\int_{G(F)\backslash G(\mathbb A)}\theta(g)\,dg\qquad(\texttt{thetaInt}),$$
computed on a fundamental domain $E$ (the value does not depend on $E$). It is a number in $[0,\infty]$; its
finiteness is the convergence of the theta integral.

**Proves**
* `thetaFull_eq_tsum`: $\theta = \sum_{m\in F}\theta_m$, $\theta_m$ the theta function of the quadric $\{Q = m\}$ (`thetaFn`).
* **`thetaInt_eq_tsum`**: $I(\Phi) = \sum_{m\in F}I_m(\Phi)$, $I_m$ = mean value of $\theta_m$ (`thetaMean`): the theta integral
  is the sum of its Fourier coefficients (orbit by orbit; Tonelli, no convergence hypothesis).
* `thetaMean_eq_finDensityProduct`: for $m\in\mathcal O_F\setminus0$ represented over $F$ and $N\ge4$,
  $I_m(\Phi) = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\int_{\{Q = m\}_\infty}\Phi\,d\sigma_\infty$ (the library's
  `siegelWeil_indefinite_uncond`), and $I_m(\Phi) = 0$ if $m$ is not represented (`thetaMean_eq_zero_of_isEmpty`).
* `thetaMean_zero_of_anisotropic`: for $V$ anisotropic over $F$, $I_0(\Phi) = \Phi(0)$.
* **`thetaInt_anisotropic`** (Weil's convergent range, anisotropic case):
  $$I(\Phi) = \Phi(0) + \sum_{m\in F^\times}I_m(\Phi).$$
  With `thetaMean_eq_finDensityProduct` the $m$-th term is the product of local densities and the archimedean orbital
  integral, which `OrbitalReal.whittaker_gaussMaj_eq_orbR` identifies with the archimedean Whittaker integral: this
  is the Siegel–Weil formula in its **Fourier-coefficient form**, term by term.
* **`tsum_thetaMean_lt_top`** (every $V$, $N\ge4$): for $\Phi$ bounded and vanishing outside a ball,
  $\sum_{m\in F^\times}I_m(\Phi)<\infty$: only finitely many $m$ contribute ($m\in\mathcal O_F$ by the finite part,
  bounded at every infinite place by the archimedean part; Northcott), each finite. The only possible divergence of
  the theta integral is the null-cone term $I_0(\Phi)$.
* **`thetaInt_lt_top_of_anisotropic`** (Weil's convergent range, anisotropic case, $N\ge4$): for $\Phi$ bounded with
  compact support, $I(\Phi)<\infty$.
-/
import QuadFormsKB.Tamagawa.Indefinite.SiegelIndefiniteFinish
import QuadFormsKB.Tamagawa.Measure.Weil.ConeAdelicSection

open MeasureTheory Measure Set NumberField IsDedekindDomain
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.SiegelWeil.Indefinite

open QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F] {k : ℕ} (Q₀ : QuadForm (𝓞 F) (k + 1))

/-- **The full theta function** $\theta(g) = \sum_{\xi\in V(F)}(\Phi\otimes1_{\hat L})(g^{-1}\xi)$ on $SO(V)(\mathbb A)$, values in
$[0,\infty]$. Parameters: `Q₀`, `Φ` (on $V_\infty$), `g`. -/
@[kb "weil1965" "Sur la formule de Siegel: the theta series Σ_{ξ∈V(F)} Φ(g⁻¹ξ) [unverified]"]
def thetaFull (Φ : VInf F (k + 1) → ℝ≥0∞) (g : SOAdele Q₀) : ℝ≥0∞ :=
  ∑' ξ : Fin (k + 1) → F, testFn Φ (g⁻¹ • diagVec F (Fin (k + 1)) ξ)

/-- **The theta function is the sum of its orbit pieces**: $\theta = \sum_{m\in F}\theta_m$, where $\theta_m$ = `thetaFn` sums
over the rational quadric $\{Q = m\}$. -/
theorem thetaFull_eq_tsum (Φ : VInf F (k + 1) → ℝ≥0∞) (g : SOAdele Q₀) :
    thetaFull Q₀ Φ g = ∑' m : F, thetaFn (ratA Q₀ m) (ratF Q₀ m) Φ (latHat F (k + 1)) g := by
  rw [thetaFull, ← (Equiv.sigmaFiberEquiv (qF Q₀)).tsum_eq, ENNReal.tsum_sigma']
  rfl

variable (hQ : Q₀.Nondegenerate)

/-- The covolume $\operatorname{vol}(SO(V)(F)\backslash SO(V)(\mathbb A))$ for Weil's measure ($= 2$ for $N\ge3$). -/
abbrev covolSO : ℝ≥0∞ := covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1)

/-- **The theta integral** $I(\Phi)$: the mean value of $\theta$ over $SO(V)(F)\backslash SO(V)(\mathbb A)$, computed on the
fundamental domain `E`. Parameters: `Q₀`, `hQ`, `Φ`, `E`. -/
@[kb "weil1965" "Sur la formule de Siegel: the theta integral ∫_{G(F)\\G(𝔸)} θ(g) dg [unverified]"]
def thetaInt (Φ : VInf F (k + 1) → ℝ≥0∞) (E : Set (SOAdele Q₀)) : ℝ≥0∞ :=
  (∫⁻ g in E, thetaFull Q₀ Φ g ∂muTam Q₀ hQ (fun _ => 1)) / covolSO Q₀ hQ

/-- **The $m$-th orbit piece of the theta integral**, $I_m(\Phi)$ = mean value of $\theta_m$. Parameters: `Q₀`, `hQ`, `Φ`,
`E`, `m`. -/
def thetaMean (Φ : VInf F (k + 1) → ℝ≥0∞) (E : Set (SOAdele Q₀)) (m : F) : ℝ≥0∞ :=
  (∫⁻ g in E, thetaFn (ratA Q₀ m) (ratF Q₀ m) Φ (latHat F (k + 1)) g ∂muTam Q₀ hQ (fun _ => 1)) / covolSO Q₀ hQ

theorem measurable_testFn_smul {Φ : VInf F (k + 1) → ℝ≥0∞} (hΦ : Measurable Φ) (y : AdeleSpace F (Fin (k + 1))) :
    Measurable fun g : SOAdele Q₀ => testFn Φ (g⁻¹ • y) :=
  (measurable_testFn hΦ).comp ((measurable_smul_const Q₀ y).comp measurable_inv)

theorem measurable_thetaFn {Φ : VInf F (k + 1) → ℝ≥0∞} (hΦ : Measurable Φ) (m : F) :
    Measurable (thetaFn (ratA Q₀ m) (ratF Q₀ m) Φ (latHat F (k + 1)) : SOAdele Q₀ → ℝ≥0∞) := by
  simp_rw [funext (thetaFn_eq_tsum Q₀ m Φ)]
  exact Measurable.tsum fun η => measurable_testFn_smul Q₀ hΦ _

/-- **The theta integral is the sum of its orbit pieces** (Tonelli; no convergence hypothesis, identity in $[0,\infty]$):
$$I(\Phi) = \sum_{m\in F}I_m(\Phi).$$ -/
@[kb "weil1965" "Sur la formule de Siegel: decomposition of the theta integral along the orbits Q = m [unverified]"]
theorem thetaInt_eq_tsum {Φ : VInf F (k + 1) → ℝ≥0∞} (hΦ : Measurable Φ) (E : Set (SOAdele Q₀)) :
    thetaInt Q₀ hQ Φ E = ∑' m : F, thetaMean Q₀ hQ Φ E m := by
  simp only [thetaInt, thetaMean, div_eq_mul_inv]
  simp_rw [thetaFull_eq_tsum]
  rw [lintegral_tsum fun m => (measurable_thetaFn Q₀ hΦ m).aemeasurable, ENNReal.tsum_mul_right]

/-- **The orbit pieces for $m\ne0$** (the library's indefinite Siegel formula, `siegelWeil_indefinite_uncond`): for
$N = k+1\ge4$, $m\in\mathcal O_F\setminus0$ with a rational point on $\{Q = m\}$ and $E$ a fundamental domain,
$$I_m(\Phi) = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\int_{T_\infty}\Phi\circ\tau_\infty\,d\sigma_\infty.$$ -/
theorem thetaMean_eq_finDensityProduct (hk : 3 ≤ k) {m : 𝓞 F} (hm : (m : F) ≠ 0) (ξ : RatSphere Q₀ (m : F))
    {Φ : VInf F (k + 1) → ℝ≥0∞} (hΦ : Measurable Φ) {E : Set (SOAdele Q₀)}
    (hE : IsFundamentalDomain (GammaSOAdele Q₀) E (muTam Q₀ hQ fun _ => 1)) :
    thetaMean Q₀ hQ Φ E m =
      ENNReal.ofReal (finDensityProduct Q₀ m) * ∫⁻ x, Φ (τInfNF Q₀ (m : F) x) ∂sigInfNF Q₀ (m : F) :=
  siegelWeil_indefinite_uncond hQ hk hm ξ hΦ hE

/-- An orbit piece with no rational point vanishes. -/
theorem thetaMean_eq_zero_of_isEmpty {m : F} (h : IsEmpty (RatSphere Q₀ m)) (Φ : VInf F (k + 1) → ℝ≥0∞)
    (E : Set (SOAdele Q₀)) : thetaMean Q₀ hQ Φ E m = 0 := by
  simp [thetaMean, thetaFn_eq_tsum, tsum_empty]

theorem smul_zero_adele (g : SOAdele Q₀) : g • (0 : AdeleSpace F (Fin (k + 1))) = 0 := by
  simpa using smul_smul_adele Q₀ g 0 0

theorem testFn_zero (Φ : VInf F (k + 1) → ℝ≥0∞) : testFn Φ (0 : AdeleSpace F (Fin (k + 1))) = Φ 0 := by
  have h0 : (0 : Fin (k + 1) → FiniteAdeleRing (𝓞 F) F) ∈ latHat F (k + 1) := fun j v => by
    simp only [Pi.zero_apply]
    exact (v.adicCompletionIntegers F).zero_mem
  simp only [testFn]
  rw [show archVec (0 : AdeleSpace F (Fin (k + 1))) = 0 from rfl,
    show finVec (0 : AdeleSpace F (Fin (k + 1))) = 0 from rfl, indicator_of_mem h0]
  simp

/-- **The zero orbit of an anisotropic space**: if $Q(\xi) = 0$ only for $\xi = 0$, then $I_0(\Phi) = \Phi(0)$ (for $N\ge3$,
where $\tau(SO(V)) = 2$, `tauTwoAll_release_uncond`). -/
theorem thetaMean_zero_of_anisotropic (hk : 2 ≤ k) (haniso : ∀ ξ : Fin (k + 1) → F, qF Q₀ ξ = 0 → ξ = 0)
    (Φ : VInf F (k + 1) → ℝ≥0∞) {E : Set (SOAdele Q₀)}
    (hE : IsFundamentalDomain (GammaSOAdele Q₀) E (muTam Q₀ hQ fun _ => 1)) :
    thetaMean Q₀ hQ Φ E 0 = Φ 0 := by
  have hτ : covolSO Q₀ hQ = 2 := tauTwoAll_release_uncond (k + 1) (by omega) Q₀ hQ
  have hθ : ∀ g, thetaFn (ratA Q₀ 0) (ratF Q₀ 0) Φ (latHat F (k + 1)) g = Φ 0 := fun g => by
    rw [thetaFn_eq_tsum]
    have : Unique (RatSphere Q₀ (0 : F)) :=
      ⟨⟨⟨0, by simp [qF, QuadForm.eval, QuadForm.evalIn]⟩⟩, fun η => Subtype.ext (haniso η.1 η.2)⟩
    rw [tsum_fintype, Fintype.sum_unique]
    rw [show (default : RatSphere Q₀ (0 : F)).1 = 0 from haniso _ (default : RatSphere Q₀ (0 : F)).2,
      map_zero, smul_zero_adele, testFn_zero]
  simp only [thetaMean, hθ, setLIntegral_const]
  rw [← covolume_muTam_eq Q₀ hQ _ hE]
  change Φ 0 * covolSO Q₀ hQ / covolSO Q₀ hQ = Φ 0
  rw [hτ, mul_div_assoc, ENNReal.div_self two_ne_zero ENNReal.ofNat_ne_top, mul_one]

/-- **The theta integral of an anisotropic space** (Weil's convergent range, the anisotropic case; every number field,
every signature, $N = k+1\ge3$):
$$I(\Phi) = \Phi(0) + \sum_{m\in F^\times}I_m(\Phi),$$
and for $N\ge4$ each $I_m(\Phi)$, $m\in\mathcal O_F\setminus0$, is the product of the local densities and the archimedean
orbital integral (`thetaMean_eq_finDensityProduct`). This is the theta side of the Siegel–Weil formula in
Fourier-coefficient form: $\Phi(0)$ is the constant term $f_\Phi(1)$ of $E(1, s_0, \Phi)$, and $I_m(\Phi)$ its $m$-th
Whittaker coefficient. -/
@[kb "weil1965" "Sur la formule de Siegel: theta integral = Φ(0) + Σ_m ∫_{V_m(𝔸)} Φ, V anisotropic [unverified]"]
theorem thetaInt_anisotropic (hk : 2 ≤ k) (haniso : ∀ ξ : Fin (k + 1) → F, qF Q₀ ξ = 0 → ξ = 0)
    {Φ : VInf F (k + 1) → ℝ≥0∞} (hΦ : Measurable Φ) {E : Set (SOAdele Q₀)}
    (hE : IsFundamentalDomain (GammaSOAdele Q₀) E (muTam Q₀ hQ fun _ => 1)) :
    thetaInt Q₀ hQ Φ E = Φ 0 + ∑' m : {m : F // m ≠ 0}, thetaMean Q₀ hQ Φ E m := by
  classical
  rw [thetaInt_eq_tsum Q₀ hQ hΦ E, ENNReal.tsum_eq_add_tsum_ite 0,
    thetaMean_zero_of_anisotropic Q₀ hQ hk haniso Φ hE]
  congr 1
  rw [show (∑' m : {m : F // m ≠ 0}, thetaMean Q₀ hQ Φ E m) =
    ∑' m : ({m : F | m ≠ 0} : Set F), thetaMean Q₀ hQ Φ E m from rfl, tsum_subtype]
  refine tsum_congr fun m => ?_
  by_cases hm : m = 0 <;> simp [hm]

/-! ### Convergence of the theta integral for compactly supported $\Phi$ -/

section Convergence

open QuadFormsKB.Tamagawa.Measure.SphereLeray QuadFormsKB.Tamagawa.Measure.SphereLerayC QuadFormsKB.Lattices
open QuadFormsKB.Tamagawa.Measure.LerayComplex
open scoped Matrix Classical

variable {Q₀}

/-- The archimedean component of $g^{-1}\eta$, $\eta\in T(m)(F)$, lies on the archimedean quadric $\{Q = m\}$. -/
theorem archVec_inv_smul_mem_quadricInfNF {m : F} (g : SOAdele Q₀) (η : RatSphere Q₀ m) :
    archVec (g⁻¹ • diagVec F (Fin (k + 1)) η.1) ∈ quadricInfNF Q₀ m := by
  rw [archVec_smul]
  obtain ⟨h1, h2⟩ := ratA_mem_quadricInfNF Q₀ m η
  refine ⟨fun w _ => ?_, fun w _ => ?_⟩
  · have := h1 w (mem_univ w)
    show (QRe Q₀ w).eval ((g⁻¹).1.1 w • (ratA Q₀ m η).1 w) = _
    rw [eval_archSO_smul]; exact this
  · have := h2 w (mem_univ w)
    show (QCx Q₀ w).eval ((g⁻¹).1.2 w • (ratA Q₀ m η).2 w) = _
    exact (eval_mulVec_of_isometryC (ArchSOC.isometry _ _) _).trans this

/-- A form with coefficients in $\mathcal O_F$ takes values in $\mathfrak o_v$ on $\mathfrak o_v^N$. -/
theorem eval_mem_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) {z : Fin (k + 1) → v.adicCompletion F}
    (hz : ∀ j, z j ∈ v.adicCompletionIntegers F) :
    ((Q₀.map (algebraMap (𝓞 F) F)).map (algebraMap F (v.adicCompletion F))).eval z ∈
      v.adicCompletionIntegers F := by
  simp only [QuadForm.evalIn, QuadForm.map, Matrix.map_apply, Algebra.algebraMap_self, RingHom.id_apply]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  split_ifs
  · refine mul_mem (mul_mem ?_ (hz i)) (hz j)
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      show (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (Q₀.coeff i j))) =
        ((algebraMap (𝓞 F) F (Q₀.coeff i j) : F) : v.adicCompletion F) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact v.valuation_le_one _
  · exact zero_mem _

/-- **Integrality from the finite part**: if $g^{-1}\eta\in\hat L$ for some $g\in SO(V)(\mathbb A)$ and $\eta\in T(m)(F)$,
then $m\in\mathcal O_F$ ($g$ preserves $Q$ at every finite place and $Q(\mathfrak o_v^N)\subseteq\mathfrak o_v$). -/
theorem mem_range_of_finVec_mem_latHat {m : F} (g : SOAdele Q₀) (η : RatSphere Q₀ m)
    (h : finVec (g⁻¹ • diagVec F (Fin (k + 1)) η.1) ∈ latHat F (k + 1)) :
    m ∈ (algebraMap (𝓞 F) F).range := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one F m fun v => ?_
  have hz : ∀ j, (finVec (g⁻¹ • diagVec F (Fin (k + 1)) η.1) j) v ∈ v.adicCompletionIntegers F :=
    fun j => h j v
  have key := eval_mem_adicCompletionIntegers (Q₀ := Q₀) v hz
  have hval : (fun j => (finVec (g⁻¹ • diagVec F (Fin (k + 1)) η.1) j) v) =
      ((((g⁻¹).2 : OAf (Q₀.map (algebraMap (𝓞 F) F))) v :
        orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) : GL (Fin (k + 1)) (v.adicCompletion F)).val *ᵥ
        fun j => algebraMap F (v.adicCompletion F) (η.1 j) := rfl
  rw [hval, QuadFormsKB.Tamagawa.eval_orth v, eval_map_comp,
    show (Q₀.map (algebraMap (𝓞 F) F)).eval η.1 = m from η.2] at key
  rw [HeightOneSpectrum.mem_adicCompletionIntegers,
    show algebraMap F (v.adicCompletion F) m = (m : v.adicCompletion F) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at key
  exact key

variable (Q₀) in
/-- **The values $m$ seen by a bounded set of $V_\infty$ are bounded at every infinite place**: for $R\ge0$ there is $B$
such that $x\in\{Q = m\}_\infty$ and $\lVert x\rVert\le R$ imply $|m|_w\le B$ for every infinite place $w$. -/
theorem exists_bound_place (R : ℝ) : ∃ B : ℝ, ∀ m : F, ∀ x ∈ quadricInfNF Q₀ m, ‖x‖ ≤ R →
    ∀ w : InfinitePlace F, w m ≤ B := by
  let f : VInf F (k + 1) → ℝ := fun x =>
    (∑ w, |(QRe Q₀ w).eval (x.1 w)|) + ∑ w, ‖(QCx Q₀ w).eval (x.2 w)‖
  have hf : Continuous f := by
    refine (continuous_finsetSum _ fun w _ => ?_).add (continuous_finsetSum _ fun w _ => ?_)
    · exact (QuadFormsKB.Siegel.continuous_eval_real _).comp ((continuous_apply w).comp continuous_fst) |>.abs
    · exact ((continuous_evalC _).comp ((continuous_apply w).comp continuous_snd)).norm
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : VInf F (k + 1)) R).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨B, fun m x hx hxR w => ?_⟩
  have hxB : (∑ w, |(QRe Q₀ w).eval (x.1 w)|) + ∑ w, ‖(QCx Q₀ w).eval (x.2 w)‖ ≤ B :=
    (le_abs_self _).trans (hB x (by simpa using hxR))
  have h1 : ∀ w, 0 ≤ |(QRe Q₀ w).eval (x.1 w)| := fun _ => abs_nonneg _
  have h2 : ∀ w, 0 ≤ ‖(QCx Q₀ w).eval (x.2 w)‖ := fun _ => norm_nonneg _
  rcases w.isReal_or_isComplex with hw | hw
  · have hQ' : (QRe Q₀ ⟨w, hw⟩).eval (x.1 ⟨w, hw⟩) = InfinitePlace.embedding_of_isReal hw m :=
      hx.1 ⟨w, hw⟩ (mem_univ _)
    have e : w m = |(QRe Q₀ ⟨w, hw⟩).eval (x.1 ⟨w, hw⟩)| := by
      rw [hQ', ← Real.norm_eq_abs, InfinitePlace.norm_embedding_of_isReal hw]
    rw [e]
    refine le_trans ?_ hxB
    have hs := Finset.single_le_sum (f := fun w => |(QRe Q₀ w).eval (x.1 w)|) (fun w _ => h1 w)
      (Finset.mem_univ ⟨w, hw⟩)
    exact hs.trans (le_add_of_nonneg_right (Finset.sum_nonneg fun w _ => h2 w))
  · have hQ' : (QCx Q₀ ⟨w, hw⟩).eval (x.2 ⟨w, hw⟩) = mC m ⟨w, hw⟩ := hx.2 ⟨w, hw⟩ (mem_univ _)
    have e : w m = ‖(QCx Q₀ ⟨w, hw⟩).eval (x.2 ⟨w, hw⟩)‖ := by
      rw [hQ']; exact (InfinitePlace.norm_embedding_eq w m).symm
    rw [e]
    refine le_trans ?_ hxB
    have hs := Finset.single_le_sum (f := fun w => ‖(QCx Q₀ w).eval (x.2 w)‖) (fun w _ => h2 w)
      (Finset.mem_univ ⟨w, hw⟩)
    exact hs.trans (le_add_of_nonneg_left (Finset.sum_nonneg fun w _ => h1 w))

/-- **Northcott finiteness**: integers of $F$ bounded at every infinite place form a finite set. -/
theorem finite_integers_bounded (B : ℝ) :
    {m : F | m ∈ (algebraMap (𝓞 F) F).range ∧ ∀ w : InfinitePlace F, w m ≤ B}.Finite := by
  refine (NumberField.Embeddings.finite_of_norm_le F ℂ B).subset fun m hm => ?_
  obtain ⟨⟨a, rfl⟩, hw⟩ := hm
  exact ⟨RingOfIntegers.isIntegral_coe a, fun φ => by simpa [InfinitePlace.apply] using hw (InfinitePlace.mk φ)⟩

/-- **Support of the orbit pieces**: if $I_m(\Phi)\ne0$ and $\Phi$ vanishes off the ball of radius $R$, then
$m\in\mathcal O_F$ and the archimedean quadric $\{Q = m\}_\infty$ meets that ball. -/
theorem thetaMean_ne_zero_imp {Φ : VInf F (k + 1) → ℝ≥0∞} {R : ℝ} (hR : ∀ x, Φ x ≠ 0 → ‖x‖ ≤ R)
    {E : Set (SOAdele Q₀)} {m : F} (h : thetaMean Q₀ hQ Φ E m ≠ 0) :
    m ∈ (algebraMap (𝓞 F) F).range ∧ ∃ x ∈ quadricInfNF Q₀ m, ‖x‖ ≤ R := by
  by_contra hc
  apply h
  have h0 : ∀ g, thetaFn (ratA Q₀ m) (ratF Q₀ m) Φ (latHat F (k + 1)) g = 0 := fun g => by
    rw [thetaFn_eq_tsum]
    refine ENNReal.tsum_eq_zero.2 fun η => ?_
    by_contra hne
    simp only [testFn] at hne
    obtain ⟨hΦ0, hind⟩ := mul_ne_zero_iff.mp hne
    exact hc ⟨mem_range_of_finVec_mem_latHat g η (Set.mem_of_indicator_ne_zero hind),
      _, archVec_inv_smul_mem_quadricInfNF g η, hR _ hΦ0⟩
  simp [thetaMean, h0]

/-- **The archimedean orbital integral of a bounded, compactly supported $\Phi$ is finite**:
$\int_{T_\infty}\Phi\circ\tau_\infty\,d\sigma_\infty<\infty$ for $m\ne0$. -/
theorem lintegral_sigInfNF_ne_top {m : F} (hm : m ≠ 0) {Φ : VInf F (k + 1) → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hΦC : ∀ x, Φ x ≤ C) {R : ℝ} (hR : ∀ x, Φ x ≠ 0 → ‖x‖ ≤ R) :
    ∫⁻ x, Φ (τInfNF Q₀ m x) ∂sigInfNF Q₀ m ≠ ⊤ := by
  let A : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (Sph (QRe Q₀ w) (σR w m)) :=
    fun w => {y | ‖(y : Fin (k + 1) → ℝ)‖ ≤ R}
  let A' : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (SphC (QCx Q₀ w) (mC m w)) :=
    fun w => ballS (QCx Q₀ w) (mC m w) R
  have hA : ∀ w, MeasurableSet (A w) := fun w =>
    measurableSet_le (continuous_norm.comp continuous_subtype_val).measurable measurable_const
  let S : Set (TInfNF Q₀ m) := (univ.pi A) ×ˢ (univ.pi A')
  have hS : MeasurableSet S :=
    (MeasurableSet.univ_pi hA).prod (MeasurableSet.univ_pi fun w => measurableSet_ballS R)
  have hle : ∀ x, Φ (τInfNF Q₀ m x) ≤ S.indicator (fun _ => C) x := fun x => by
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]; exact hΦC _
    · rw [indicator_of_notMem hx]
      by_contra hne
      have hτ := hR _ (by simpa using hne)
      apply hx
      refine ⟨fun w _ => ?_, fun w _ => ?_⟩
      · exact (norm_le_pi_norm (τInfNF Q₀ m x).1 w).trans ((norm_fst_le _).trans hτ)
      · exact (norm_le_pi_norm (τInfNF Q₀ m x).2 w).trans ((norm_snd_le _).trans hτ)
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
  have := fun w => sigmaFinite_sig (Q := QRe Q₀ w) (mR_ne_zero hm w)
  have := fun w => sigmaFinite_sigC (Q := QCx Q₀ w) (mC_ne_zero hm w) (Nat.succ_pos k)
  have := fun w => sigmaFinite_smul (sigC (QCx Q₀ w) (mC m w)) (c := (2 : ℝ≥0∞) ^ k)
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  rw [lintegral_indicator_const hS, sigInfNF, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi]
  refine ENNReal.mul_ne_top hC (ENNReal.mul_ne_top (ENNReal.prod_ne_top fun w _ => ?_)
    (ENNReal.prod_ne_top fun w _ => ?_))
  · rw [sig, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (nu_bounded_lt_top (mR_ne_zero hm w) R).ne
  · rw [Measure.smul_apply, smul_eq_mul, sigC, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (nuC_ballS_lt_top (mC_ne_zero hm w) (Nat.succ_pos k) R).ne)

/-- **Each orbit piece is finite** for $\Phi$ bounded with compact support ($m\ne0$, $N\ge4$). -/
theorem thetaMean_ne_top (hk : 3 ≤ k) {Φ : VInf F (k + 1) → ℝ≥0∞} (hΦ : Measurable Φ) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hΦC : ∀ x, Φ x ≤ C) {R : ℝ} (hR : ∀ x, Φ x ≠ 0 → ‖x‖ ≤ R) {E : Set (SOAdele Q₀)}
    (hE : IsFundamentalDomain (GammaSOAdele Q₀) E (muTam Q₀ hQ fun _ => 1)) {m : F} (hm : m ≠ 0) :
    thetaMean Q₀ hQ Φ E m ≠ ⊤ := by
  by_cases h0 : thetaMean Q₀ hQ Φ E m = 0
  · simp [h0]
  obtain ⟨⟨a, rfl⟩, -⟩ := thetaMean_ne_zero_imp hQ hR h0
  rcases isEmpty_or_nonempty (RatSphere Q₀ (algebraMap (𝓞 F) F a)) with he | hne
  · rw [thetaMean_eq_zero_of_isEmpty Q₀ hQ he]; exact ENNReal.zero_ne_top
  obtain ⟨ξ⟩ := hne
  rw [show algebraMap (𝓞 F) F a = (a : F) from rfl] at ξ hm ⊢
  rw [thetaMean_eq_finDensityProduct Q₀ hQ hk hm ξ hΦ hE]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_sigInfNF_ne_top hm hC hΦC hR)

/-- **The nonzero orbits contribute a finite amount, for every $V$** (isotropic or not; every number field, every
signature, $N = k+1\ge4$): for $\Phi\ge0$ measurable, bounded ($\Phi\le C<\infty$) and vanishing outside a ball
($\Phi(x)\ne0\Rightarrow\lVert x\rVert\le R$),
$$\sum_{m\in F^\times}I_m(\Phi)<\infty.$$
So the only possible divergence of the theta integral is the zero orbit $I_0(\Phi)$, the integral over the null cone:
this is where Weil's condition ($V$ anisotropic, or $\dim V-r>r+1$) enters.
*Proof.* A nonzero $I_m(\Phi)$ forces $m\in\mathcal O_F$ (the finite part, `mem_range_of_finVec_mem_latHat`) and
$|m|_w\le B$ at every infinite place (the archimedean part, `exists_bound_place`), so only finitely many $m$ contribute
(Northcott, `finite_integers_bounded`); each is finite by the indefinite Siegel formula (`thetaMean_ne_top`). -/
@[kb "weil1965" "Sur la formule de Siegel: the nonzero orbits of the theta integral converge [unverified]"]
theorem tsum_thetaMean_lt_top (hk : 3 ≤ k) {Φ : VInf F (k + 1) → ℝ≥0∞} (hΦ : Measurable Φ) {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (hΦC : ∀ x, Φ x ≤ C) {R : ℝ} (hR : ∀ x, Φ x ≠ 0 → ‖x‖ ≤ R) {E : Set (SOAdele Q₀)}
    (hE : IsFundamentalDomain (GammaSOAdele Q₀) E (muTam Q₀ hQ fun _ => 1)) :
    ∑' m : {m : F // m ≠ 0}, thetaMean Q₀ hQ Φ E m < ⊤ := by
  obtain ⟨B, hB⟩ := exists_bound_place Q₀ R
  have hfin : (Subtype.val ⁻¹' {m : F | m ∈ (algebraMap (𝓞 F) F).range ∧ ∀ w : InfinitePlace F, w m ≤ B} :
      Set {m : F // m ≠ 0}).Finite := (finite_integers_bounded B).preimage Subtype.val_injective.injOn
  rw [tsum_eq_sum (s := hfin.toFinset) fun b hb => ?_]
  · exact ENNReal.sum_lt_top.2 fun b _ => (thetaMean_ne_top hQ hk hΦ hC hΦC hR hE b.2).lt_top
  · by_contra hne
    obtain ⟨hint, x, hx, hxR⟩ := thetaMean_ne_zero_imp hQ hR hne
    exact hb (hfin.mem_toFinset.2 ⟨hint, hB _ x hx hxR⟩)

/-- **Convergence of the theta integral of an anisotropic space** (Weil's convergent range, anisotropic case; every
number field, real and complex places, every signature, $N = k+1\ge4$): for $V$ anisotropic over $F$ and
$\Phi\ge0$ measurable on $V_\infty$, bounded ($\Phi\le C<\infty$) and vanishing outside a compact set $K$, the theta
integral of $\Phi\otimes1_{\hat L}$ is finite:
$$\frac1{\operatorname{vol}(SO(V)(F)\backslash SO(V)(\mathbb A))}\int_{SO(V)(F)\backslash SO(V)(\mathbb A)}
  \sum_{\xi\in V(F)}(\Phi\otimes1_{\hat L})(g^{-1}\xi)\,dg<\infty.$$
From `thetaInt_anisotropic` ($I(\Phi) = \Phi(0)+\sum_{m\ne0}I_m(\Phi)$) and `tsum_thetaMean_lt_top`. -/
@[kb "weil1965" "Sur la formule de Siegel: absolute convergence of the theta integral, V anisotropic [unverified]"]
theorem thetaInt_lt_top_of_anisotropic (hk : 3 ≤ k) (haniso : ∀ ξ : Fin (k + 1) → F, qF Q₀ ξ = 0 → ξ = 0)
    {Φ : VInf F (k + 1) → ℝ≥0∞} (hΦ : Measurable Φ) {C : ℝ≥0∞} (hC : C ≠ ⊤) (hΦC : ∀ x, Φ x ≤ C)
    {K : Set (VInf F (k + 1))} (hK : IsCompact K) (hΦK : ∀ x, Φ x ≠ 0 → x ∈ K) {E : Set (SOAdele Q₀)}
    (hE : IsFundamentalDomain (GammaSOAdele Q₀) E (muTam Q₀ hQ fun _ => 1)) :
    thetaInt Q₀ hQ Φ E < ⊤ := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  rw [thetaInt_anisotropic Q₀ hQ (by omega) haniso hΦ hE]
  refine ENNReal.add_lt_top.2 ⟨(hΦC 0).trans_lt hC.lt_top, ?_⟩
  exact tsum_thetaMean_lt_top hQ hk hΦ hC hΦC (R := R) (fun x hx => by simpa using hR (hΦK x hx)) hE

end Convergence

end QuadFormsKB.SiegelWeil.Indefinite
