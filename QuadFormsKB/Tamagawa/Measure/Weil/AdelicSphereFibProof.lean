import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereCoord
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereCont

/-!
# Weil's adelic fibration over the sphere, proved

**Discharges the input `AdelicSphereFibration`** (and hence `AdelicSphereFamily.Fibration`) for the constructed
data, for every nondegenerate $Q_0$ over $\mathcal O_F$ in $N = k+1\ge4$ variables (any signature, every number field):

* **`AdelicSphereSetup.sphereData`**: the base point $\xi$, the stabilizer embedding $\iota$ (`iota`), the adelic sphere
  $T(\rho)_{\mathbb A}$ (`adelicSphere`), the orbit coordinates $(x, h)\mapsto\iota(h)s(x)^{-1}$ (`coordEquiv`) and the
  **quotient measure** $\sigma(A) = \mu(\mathrm{coord}(A\times U))/\mu'(U)$ (`quotMeasure`, $\mu = $ `muTam Q₀`,
  $\mu' = $ `muTam Q'`).
* **`AdelicSphereSetup.sphereFibration`**: `AdelicSphereFibration Q₀ hQ hQ' (S.sphereData …)`.
* **`sphereFamily`**, **`sphereFamily_fibration`**: the family over all represented square classes and its fibration.
* **`adelicZetaPlus_eq_tsum_covolume_uncond`**: the unfolding $Z^+(s) = \sum_c\frac{\operatorname{covol}(G'_c)}2Z(s,c)$ with
  no input.

$\sigma$ is the measure of the quotient $SO(Q')(\mathbb A)\backslash SO(V)(\mathbb A)$ transported to $T(\rho)_{\mathbb A}$; it does
not depend on the auxiliary set $U$ (`quotMeasure_mul`). Its product decomposition into local Leray measures (Weil's
$\sigma = \bigotimes_v\sigma_v$) is a separate statement, needed for `AdelicSphericalEuler` and `AdelicSphereDensities`.

*Hypothesis $k\ge3$.* `muTam Q'` must be nonzero (`muTam_ne_zero`, $k\ge3$). For $k = 2$ and a split binary complement,
$\prod_v\mu_v(SO(L'_v)) = \prod_v(1 - q_v^{-1}) = 0$ (convergence factors $\lambda_v = 1$), so `muTam Q'` = 0 and the input is
false.
-/

open MeasureTheory Set Matrix
open scoped ENNReal RestrictedProduct Pointwise

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure

variable {F : Type} [Field F] [NumberField F] {k : ℕ} {Q₀ : QuadForm (𝓞 F) (k + 1)} {ρ : F}

namespace AdelicSphereSetup

variable (S : AdelicSphereSetup Q₀ ρ) (hρ : ρ ≠ 0) (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k)

/-- An auxiliary set $U\subseteq SO(Q')(\mathbb A)$ with $0 < \mu'(U) < \infty$. -/
def refSet : Set (SOAdele S.C.Q') :=
  (OrbitSection.exists_pos_lt_top (muTam S.C.Q' S.C.hQ' fun _ => 1) (muTam_ne_zero S.C.Q' S.C.hQ' hk)).choose

theorem refSet_spec : MeasurableSet (S.refSet hk) ∧ muTam S.C.Q' S.C.hQ' (fun _ => 1) (S.refSet hk) ≠ 0 ∧
    muTam S.C.Q' S.C.hQ' (fun _ => 1) (S.refSet hk) ≠ ∞ :=
  (OrbitSection.exists_pos_lt_top (muTam S.C.Q' S.C.hQ' fun _ => 1) (muTam_ne_zero S.C.Q' S.C.hQ' hk)).choose_spec

/-- **The measure $\sigma$ on the adelic sphere**: the quotient measure of `muTam Q₀` by `muTam Q'`. -/
@[kb "weil1982" "Lemma 2.4.1, Thm 2.4.3 [unverified page]; §4.5, p. 109 (the measure on T(ρ)_A)"]
def sphereMeasure : Measure (adelicSphere Q₀ ρ) :=
  quotMeasure (S.coordEquiv hρ) (muTam Q₀ hQ fun _ => 1) (S.refSet hk) (muTam S.C.Q' S.C.hQ' fun _ => 1)

/-- **The adelic sphere data** for $T(\rho)$. -/
def sphereData : AdelicSphereData Q₀ ρ S.C.Q' where
  ξ := S.ξ
  ι := S.iota
  T := adelicSphere Q₀ ρ
  σ := S.sphereMeasure hρ hQ hk
  coord := S.coordEquiv hρ

/-- The covering sets $A_i = \{x : s(x)^{-1}\in C_i\}$ ($C_i$ the compact covering of $SO(V)(\mathbb A)$). -/
def coverSet (i : ℕ) : Set (adelicSphere Q₀ ρ) :=
  (fun x => (S.sphereSection hρ x)⁻¹) ⁻¹' compactCovering (SOAdele Q₀) i

theorem measurableSet_coverSet (i : ℕ) : MeasurableSet (S.coverSet hρ i) :=
  (S.measurable_sphereSection hρ).inv (isCompact_compactCovering (SOAdele Q₀) i).isClosed.measurableSet

theorem iUnion_coverSet : ⋃ i, S.coverSet hρ i = univ := by
  simp only [coverSet, ← preimage_iUnion, iUnion_compactCovering, preimage_univ]

include hQ in
theorem coverSet_fin (i : ℕ) (K : Set (SOAdele S.C.Q')) (hK : IsCompact K) :
    muTam Q₀ hQ (fun _ => 1) ((S.coordEquiv hρ).symm ⁻¹' (S.coverSet hρ i ×ˢ K)) ≠ ∞ := by
  have := isFiniteMeasureOnCompacts_muTam' Q₀ hQ (fun _ => 1)
  have hc : IsCompact (S.iota '' K * compactCovering (SOAdele Q₀) i) :=
    (hK.image S.continuous_iota).mul (isCompact_compactCovering (SOAdele Q₀) i)
  refine ne_top_of_le_ne_top hc.measure_lt_top.ne (measure_mono ?_)
  intro g hg
  simp only [mem_preimage, mem_prod] at hg
  have e : g = S.coordFun hρ ((S.coordEquiv hρ).symm g) := ((S.coordEquiv hρ).apply_symm_apply g).symm
  rw [e]
  exact Set.mul_mem_mul ⟨_, hg.2, rfl⟩ hg.1

include hQ in
/-- **Weil's adelic fibration over the sphere** (the input `AdelicSphereFibration`, proved), $N = k + 1\ge4$. -/
@[kb "weil1982" "Lemma 2.4.1, Thm 2.4.3 [unverified page]; §4.5, p. 109 (fibration over T(ρ))"]
theorem sphereFibration : AdelicSphereFibration Q₀ hQ S.C.hQ' (S.sphereData hρ hQ hk) := by
  have hμ' := isFiniteMeasureOnCompacts_muTam' S.C.Q' S.C.hQ' (fun _ => 1)
  have hspec := S.refSet_spec hk
  have hμ : ∀ (h' : SOAdele S.C.Q') (E : Set (SOAdele Q₀)), MeasurableSet E →
      muTam Q₀ hQ (fun _ => 1) ((fun g => S.iota h' * g) ⁻¹' E) = muTam Q₀ hQ (fun _ => 1) E :=
    fun h' E _ => measure_preimage_mul _ _ _
  refine ⟨fun x h h' => S.coordFun_mul hρ x h h', fun x h => S.coordFun_inv_smul hρ (x, h),
    fun h hh => S.iota_mem_gamma hh, fun γ hγ hfix => S.exists_iota_gamma hρ hγ hfix, ?_, ?_⟩
  · have := sigmaFinite_quotMeasure (S.coordEquiv hρ) S.iota (fun x h h' => S.coordFun_mul hρ x h h')
      (muTam Q₀ hQ fun _ => 1) hμ (muTam S.C.Q' S.C.hQ' fun _ => 1) (muTam_ne_zero S.C.Q' S.C.hQ' hk) hspec.1 hspec.2.1
      hspec.2.2 (S.coverSet hρ) (S.measurableSet_coverSet hρ) (S.iUnion_coverSet hρ) (S.coverSet_fin hρ hQ)
    show SFinite (S.sphereMeasure hρ hQ hk)
    unfold sphereMeasure
    infer_instance
  · exact map_prod_quotMeasure (S.coordEquiv hρ) S.iota (fun x h h' => S.coordFun_mul hρ x h h')
      (muTam Q₀ hQ fun _ => 1) hμ (muTam S.C.Q' S.C.hQ' fun _ => 1) (muTam_ne_zero S.C.Q' S.C.hQ' hk) hspec.1 hspec.2.1
      hspec.2.2 (S.coverSet hρ) (S.measurableSet_coverSet hρ) (S.iUnion_coverSet hρ) (S.coverSet_fin hρ hQ)

end AdelicSphereSetup

/-! ### The family over the represented square classes -/

/-- A setup for every represented square class ($k\ge1$). -/
def classSetup (hQ : Q₀.Nondegenerate) (hk : 1 ≤ k) (c : RepClasses Q₀) : AdelicSphereSetup Q₀ (repρ c) :=
  Classical.choice (exists_adelicSphereSetup hQ (repρ_ne_zero c) ⟨c.2.choose, c.2.choose_spec⟩ hk)

/-- **The constructed sphere family** (complements and adelic sphere data for every represented class). -/
def sphereFamily (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k) : AdelicSphereFamily Q₀ where
  Q' c := (classSetup hQ (by omega) c).C.Q'
  hQ' c := (classSetup hQ (by omega) c).C.hQ'
  data c := (classSetup hQ (by omega) c).sphereData (repρ_ne_zero c) hQ hk

/-- **`AdelicSphereFamily.Fibration`, proved** for the constructed family ($N = k + 1\ge4$). -/
@[kb "weil1982" "Lemma 2.4.1, Thm 2.4.3 [unverified page]; §4.5, p. 109 (fibration over T(ρ))"]
theorem sphereFamily_fibration (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k) : (sphereFamily hQ hk).Fibration hQ :=
  ⟨fun c => (classSetup hQ (by omega) c).sphereFibration (repρ_ne_zero c) hQ hk⟩

/-- **The adelic spherical unfolding, unconditional** (`adelicZetaPlus_eq_tsum_covolume` without the fibration
input; $N = k+1\ge4$, any signature, every number field): for measurable $\Phi\ge0$ and every real $s$,
$Z^+(s) = \sum_c\frac{\operatorname{covol}(SO(Q'_c)(F)\backslash SO(Q'_c)(\mathbb A))}2\,Z(s,c)$ for the constructed family. -/
@[kb "weil1982" "§4.5, p. 109 (Z⁺(s) = Σ_ρ (τ(G'_ρ)/2)Z(s,ρ) before τ(G'_ρ) = 2 is used)"]
theorem adelicZetaPlus_eq_tsum_covolume_uncond (hQ : Q₀.Nondegenerate) (hk : 3 ≤ k)
    {Φ : AdeleSpace F (Fin (k + 1)) → ℝ≥0∞} (hΦ : Measurable Φ)
    {D : Set (SOAdele Q₀)} (hD : IsFundamentalDomain (GammaSOAdele Q₀) D (muTam Q₀ hQ 1))
    {DM : Set (Adeles F)ˣ} (hDM : IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F)) (s : ℝ) :
    adelicZetaPlus Q₀ hQ Φ D DM s =
      ∑' c, (sphereFamily hQ hk).covol c / 2 * adelicSphZeta ((sphereFamily hQ hk).data c) Φ s :=
  adelicZetaPlus_eq_tsum_covolume (by omega) _ (sphereFamily_fibration hQ hk) hΦ hD hDM s

end QuadFormsKB.Tamagawa.Measure.Weil

end
