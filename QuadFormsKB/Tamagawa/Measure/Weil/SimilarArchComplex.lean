import QuadFormsKB.Tamagawa.Measure.LerayComplex
import QuadFormsKB.Tamagawa.Measure.LerayUnimodularC
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarDet

/-!
# The complex Leray measure under a similarity

Let $Q, Q'$ be quadratic forms over $\mathbb C$ in $n$ variables with $Q' = c\cdot(Q\circ G)$, i.e. with Hessians
related by $H_{Q'} = c\,G^{\mathsf T}H_QG$ ($G \in \mathrm{GL}_n(\mathbb C)$, $c \in \mathbb C^\times$). Write
$L = c\cdot(\,\cdot\,G) : \mathbb C^{n(n+1)/2} \to \mathbb C^{n(n+1)/2}$ for the $\mathbb C$-linear map `c • act G` on
coefficient coordinates. Conjugation $g \mapsto G^{-1}gG$ is an isomorphism of topological groups
$SO(Q)(\mathbb C) \to SO(Q')(\mathbb C)$, and the Leray measures (`lerayMeasureC`, `LerayComplex.lean`) transform by the
factor $|\det_{\mathbb C}L|^2$.

**Results.**
* `conjSOC` (needs $c \ne 0$): the isomorphism $SO(Q)(\mathbb C) \simeq_{\mathrm{top}} SO(Q')(\mathbb C)$,
  $g \mapsto G^{-1}gG$ (`conjSOC_mat`).
* `phi_simConj`: $\Phi_{Q'}(G^{-1}XG) = L\,\Phi_Q(X)$.
* `tendsto_approxGen`: the Leray limit along any shrinking family of measurable neighbourhoods of $c_Q$.
* `map_lerayMeasureC_conjSOC`: $(\mathrm{conj})_*\mu_Q = |\det_{\mathbb C}L|^2\,\mu_{Q'}$.
* `map_lerayMeasureC_conjSOC'`: the same with the factor $|c|^{n(n+1)}|\det G|^{2(n+1)}$ (`det_smul_act`).

The proof compares the Leray limits (`tendsto_lerayApproxC`): the preimage under $L$ of the shrinking balls
about $c_{Q'} = L(c_Q)$ is a family of shrinking neighbourhoods of $c_Q$ (not balls), so we first generalize the Leray
limit to such families (`tendsto_approxGen`), then transport by the measure-preserving linear map
$X \mapsto G^{-1}XG$ of $M_n(\mathbb C)$, and conclude with uniqueness (`lerayMeasureC_unique`).
-/

open MeasureTheory Measure Matrix Set Filter Topology TopologicalSpace
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.LerayComplex

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa.ArchVol

variable {n : ℕ}

local notation "𝕄" => Matrix (Fin n) (Fin n) ℂ

/-! ### Matrix identities -/

section Algebra

variable {Q Q' : QuadForm ℂ n} {G : GL (Fin n) ℂ} {c : ℂ}

theorem gramC_similar
    (hH : Q'.hessian = c • ((G : 𝕄)ᵀ * Q.hessian * (G : 𝕄))) :
    gramC Q' = c • ((G : 𝕄)ᵀ * gramC Q * (G : 𝕄)) := by
  simp only [gramC, hH, Matrix.mul_smul, Matrix.smul_mul]
  rw [smul_comm]

theorem units_mul_inv_val (G : GL (Fin n) ℂ) : (G : 𝕄) * ((G⁻¹ : GL (Fin n) ℂ) : 𝕄) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem units_inv_mul_val (G : GL (Fin n) ℂ) : ((G⁻¹ : GL (Fin n) ℂ) : 𝕄) * (G : 𝕄) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

/-- Conjugating by $G^{-1}$ (with $A' = c\,G^{\mathsf T}AG$) carries isometries of $A$ to isometries of $A'$. -/
theorem conj_isometry {A A' : 𝕄} (hA : A' = c • ((G : 𝕄)ᵀ * A * (G : 𝕄))) {g : 𝕄}
    (hg : gᵀ * A * g = A) :
    (((G⁻¹ : GL (Fin n) ℂ) : 𝕄) * g * (G : 𝕄))ᵀ * A' *
      (((G⁻¹ : GL (Fin n) ℂ) : 𝕄) * g * (G : 𝕄)) = A' := by
  set Gm : 𝕄 := (G : 𝕄)
  set Gi : 𝕄 := ((G⁻¹ : GL (Fin n) ℂ) : 𝕄)
  have h2 : Gm * Gi = 1 := units_mul_inv_val G
  have h1 : Gi * Gm = 1 := units_inv_mul_val G
  have h3 : Giᵀ * Gmᵀ = 1 := by rw [← transpose_mul, h2, transpose_one]
  have h3' : ∀ Z : 𝕄, Giᵀ * (Gmᵀ * Z) = Z := fun Z => by rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
  have h2' : ∀ Z : 𝕄, Gm * (Gi * Z) = Z := fun Z => by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have key : (Gi * g * Gm)ᵀ * (Gmᵀ * A * Gm) * (Gi * g * Gm) = Gmᵀ * (gᵀ * A * g) * Gm := by
    simp only [transpose_mul, Matrix.mul_assoc, h3', h2']
  rw [hA, Matrix.mul_smul, Matrix.smul_mul, key, hg]

theorem det_conj_val (G : GL (Fin n) ℂ) (M : 𝕄) :
    (((G⁻¹ : GL (Fin n) ℂ) : 𝕄) * M * (G : 𝕄)).det = M.det := by
  have := det_conj_P G⁻¹ M
  rwa [inv_inv] at this

end Algebra

/-! ### The conjugation isomorphism -/

section Conj

variable {Q Q' : QuadForm ℂ n} (G : GL (Fin n) ℂ) (c : ℂ)
  (hH : Q'.hessian = c • ((G : Matrix (Fin n) (Fin n) ℂ)ᵀ * Q.hessian * (G : Matrix (Fin n) (Fin n) ℂ)))

include hH

theorem conj_mem (g : GL (Fin n) ℂ) (hg : g ∈ soC Q) : G⁻¹ * g * G ∈ soC Q' := by
  rw [mem_soC_iff] at hg ⊢
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul]
    exact conj_isometry (gramC_similar hH) hg.1
  · rw [Units.val_mul, Units.val_mul, det_conj_val, hg.2]

theorem conj_mem_inv (hc : c ≠ 0) (h : GL (Fin n) ℂ) (hh : h ∈ soC Q') : G * h * G⁻¹ ∈ soC Q := by
  rw [mem_soC_iff] at hh ⊢
  have hA : gramC Q = c⁻¹ • (((G⁻¹ : GL (Fin n) ℂ) : 𝕄)ᵀ * gramC Q' * ((G⁻¹ : GL (Fin n) ℂ) : 𝕄)) := by
    rw [gramC_similar hH]
    set Gm : 𝕄 := (G : 𝕄)
    set Gi : 𝕄 := ((G⁻¹ : GL (Fin n) ℂ) : 𝕄)
    have h2 : Gm * Gi = 1 := units_mul_inv_val G
    have h1 : Gi * Gm = 1 := units_inv_mul_val G
    have h3 : Giᵀ * Gmᵀ = 1 := by rw [← transpose_mul, h2, transpose_one]
    have h4 : Gmᵀ * Giᵀ = 1 := by rw [← transpose_mul, h1, transpose_one]
    have h3' : ∀ Z : 𝕄, Giᵀ * (Gmᵀ * Z) = Z := fun Z => by rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
    have h2' : ∀ Z : 𝕄, Gm * (Gi * Z) = Z := fun Z => by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, h3', inv_mul_cancel₀ hc,
      one_smul, h2, Matrix.mul_one]
  have hiso := conj_isometry (G := G⁻¹) (c := c⁻¹) (A := gramC Q') (A' := gramC Q) hA hh.1
  rw [inv_inv] at hiso
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul]
    exact hiso
  · rw [Units.val_mul, Units.val_mul]
    have hd := det_conj_val G⁻¹ (h : 𝕄)
    rw [inv_inv] at hd
    rw [hd]; exact hh.2

/-- **The conjugation isomorphism** $g \mapsto G^{-1}gG$ of topological groups
$SO(Q)(\mathbb C) \to SO(Q')(\mathbb C)$, for $Q' = c\cdot(Q \circ G)$ (`hH`), $c \ne 0$. -/
def conjSOC (hc : c ≠ 0) : ArchSOC Q ≃ₜ* ArchSOC Q' where
  toFun g := ArchSOC.mk Q' (G⁻¹ * ArchSOC.incl Q g * G) (conj_mem G c hH _ (ArchSOC.incl_mem Q g))
  invFun h := ArchSOC.mk Q (G * ArchSOC.incl Q' h * G⁻¹) (conj_mem_inv G c hH hc _ (ArchSOC.incl_mem Q' h))
  left_inv g := Subtype.ext (by
    show G * (G⁻¹ * (ArchSOC.incl Q g) * G) * G⁻¹ = (ArchSOC.incl Q g)
    group)
  right_inv h := Subtype.ext (by
    show G⁻¹ * (G * (ArchSOC.incl Q' h) * G⁻¹) * G = (ArchSOC.incl Q' h)
    group)
  map_mul' a b := Subtype.ext (by
    show G⁻¹ * ((ArchSOC.incl Q a) * (ArchSOC.incl Q b)) * G =
      (G⁻¹ * (ArchSOC.incl Q a) * G) * (G⁻¹ * (ArchSOC.incl Q b) * G)
    group)
  continuous_toFun := by
    show Continuous fun g : soC Q =>
      (⟨G⁻¹ * (g : GL (Fin n) ℂ) * G, conj_mem G c hH _ g.2⟩ : soC Q')
    exact Continuous.subtype_mk
      ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  continuous_invFun := by
    show Continuous fun h : soC Q' =>
      (⟨G * (h : GL (Fin n) ℂ) * G⁻¹, conj_mem_inv G c hH hc _ h.2⟩ : soC Q)
    exact Continuous.subtype_mk
      ((continuous_const.mul continuous_subtype_val).mul continuous_const) _

theorem conjSOC_mat (hc : c ≠ 0) (g : ArchSOC Q) :
    ArchSOC.mat Q' (conjSOC G c hH hc g) =
      ((G⁻¹ : GL (Fin n) ℂ) : 𝕄) * ArchSOC.mat Q g * (G : 𝕄) := rfl

/-- **$\Phi$ under conjugation**: $\Phi_{Q'}(G^{-1}XG) = (c\cdot(\,\cdot\,G))\,\Phi_Q(X)$. -/
theorem phi_simConj (X : 𝕄) :
    phi Q' (((G⁻¹ : GL (Fin n) ℂ) : 𝕄) * X * (G : 𝕄)) = (c • act (G : 𝕄)) (phi Q X) := by
  rw [LinearMap.smul_apply, phi, phi, act_apply, symOf_wtU (gram_sym_mul Q X), ← wtU_smul, gramC_similar hH]
  congr 1
  set Gm : 𝕄 := (G : 𝕄)
  set Gi : 𝕄 := ((G⁻¹ : GL (Fin n) ℂ) : 𝕄)
  have h2 : Gm * Gi = 1 := units_mul_inv_val G
  have h3 : Giᵀ * Gmᵀ = 1 := by rw [← transpose_mul, h2, transpose_one]
  have h3' : ∀ Z : 𝕄, Giᵀ * (Gmᵀ * Z) = Z := fun Z => by rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
  have h2' : ∀ Z : 𝕄, Gm * (Gi * Z) = Z := fun Z => by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  simp only [transpose_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, h3', h2']

end Conj

/-! ### The Leray limit along general shrinking families -/

/-- **Averages over a shrinking family of sets**: if $S_\varepsilon$ ($\varepsilon > 0$) are measurable sets of finite
positive $\mu$-mass that eventually lie in every ball about $c_0$, and $G \ge 0$ is continuous on an open $U \ni c_0$,
then $\frac{1}{\mu(S_\varepsilon)}\int_{S_\varepsilon}G\,d\mu \to G(c_0)$ as $\varepsilon \to 0^+$. -/
theorem tendsto_avg_family {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (μ : Measure E) {c₀ : E} (S : ℝ → Set E) (hmeas : ∀ ε, MeasurableSet (S ε))
    (hpos : ∀ ε > 0, 0 < μ (S ε)) (hfin : ∀ ε > 0, μ (S ε) ≠ ∞)
    (hshr : ∀ δ > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ), S ε ⊆ Metric.ball c₀ δ)
    {U : Set E} (hU : IsOpen U) (hc : c₀ ∈ U) {G : E → ℝ}
    (hGc : ContinuousOn G U) (hG0 : ∀ t ∈ U, 0 ≤ G t) :
    Tendsto (fun ε => (∫⁻ t in S ε, ENNReal.ofReal (G t) ∂μ).toReal / (μ (S ε)).toReal) (𝓝[>] 0)
      (𝓝 (G c₀)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  have hcont : ContinuousAt G c₀ := hGc.continuousAt (hU.mem_nhds hc)
  obtain ⟨δ1, hδ1, h1⟩ := Metric.continuousAt_iff.mp hcont (η / 2) (by positivity)
  obtain ⟨δ2, hδ2, h2⟩ := Metric.isOpen_iff.mp hU c₀ hc
  filter_upwards [hshr (min δ1 δ2) (lt_min hδ1 hδ2), self_mem_nhdsWithin] with ε hS hε
  have hε : 0 < ε := hε
  set B := S ε
  have hsub : ∀ t ∈ B, dist t c₀ < min δ1 δ2 := fun t ht => Metric.mem_ball.mp (hS ht)
  have hU' : ∀ t ∈ B, t ∈ U := fun t ht =>
    h2 (Metric.mem_ball.mpr ((hsub t ht).trans_le (min_le_right _ _)))
  have hclose : ∀ t ∈ B, |G t - G c₀| < η / 2 := fun t ht => by
    rw [← Real.dist_eq]; exact h1 ((hsub t ht).trans_le (min_le_left _ _))
  have hmeasB : MeasurableSet B := hmeas ε
  have hV : μ B ≠ ∞ := hfin ε hε
  have hV0 : 0 < (μ B).toReal := ENNReal.toReal_pos (hpos ε hε).ne' hV
  have hG0' := hG0 c₀ hc
  have hup : ∫⁻ t in B, ENNReal.ofReal (G t) ∂μ ≤ ENNReal.ofReal (G c₀ + η / 2) * μ B := by
    rw [← setLIntegral_const]
    refine setLIntegral_mono' hmeasB fun t ht => ?_
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.mp (hclose t ht)).2])
  have hlo : ENNReal.ofReal (G c₀ - η / 2) * μ B ≤ ∫⁻ t in B, ENNReal.ofReal (G t) ∂μ := by
    rw [← setLIntegral_const]
    refine setLIntegral_mono' hmeasB fun t ht => ?_
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.mp (hclose t ht)).1])
  have hfin' : ∫⁻ t in B, ENNReal.ofReal (G t) ∂μ ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV) hup
  have hup' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV) hup
  have hlo' := ENNReal.toReal_mono hfin' hlo
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hup'
  rw [ENNReal.toReal_mul] at hlo'
  have hlo'' : (G c₀ - η / 2) * (μ B).toReal ≤ (∫⁻ t in B, ENNReal.ofReal (G t) ∂μ).toReal :=
    le_trans (mul_le_mul_of_nonneg_right (by rw [ENNReal.toReal_ofReal']; exact le_max_left _ _) hV0.le) hlo'
  rw [Real.dist_eq, abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hV0]; nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hV0]; nlinarith

section General

variable {Q : QuadForm ℂ n} (D : DiagC Q)

/-- **The Leray approximant along a family $S_\varepsilon$ of neighbourhoods of $c_Q$**:
$\frac{1}{\mathrm{Leb}(S_\varepsilon)}\int_{\{\operatorname{Re}\det X > 0,\ \Phi_Q(X) \in S_\varepsilon\}}f(X)\,dX$.
For $S_\varepsilon = \bar B_\varepsilon(c_Q)$ this is `lerayApproxC`. -/
def approxGen (Q : QuadForm ℂ n) (S : ℝ → Set (UIdx n → ℂ)) (f : (Fin n → Fin n → ℂ) → ℝ) (ε : ℝ) : ℝ :=
  (∫ X in regionC Q (S ε), f X) / (volume (S ε)).toReal

/-- The fibration identity on a region over a measurable $E \subseteq U_0$, for $f \ge 0$. -/
theorem lintegral_regionC_nonneg {f : (Fin n → Fin n → ℂ) → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hf0 : ∀ X, 0 ≤ f X) {E : Set (UIdx n → ℂ)} (hE : MeasurableSet E)
    (hEU : E ⊆ U0 D) :
    ∫⁻ X in regionC Q E, ENNReal.ofReal (f X) =
      ∫⁻ c in E, ENNReal.ofReal (fibreInt D f (sec D c) * rho D c) := by
  rw [lintegral_regionC D (φ := fun X => ENNReal.ofReal (f X))
    (ENNReal.measurable_ofReal.comp hf.measurable) hE hEU]
  refine setLIntegral_congr_fun hE fun c _ => ?_
  have hinner : ∫⁻ g, ENNReal.ofReal (f (chart D (g, sec D c))) ∂lerayDC D =
      ENNReal.ofReal (fibreInt D f (sec D c)) := by
    rw [fibreInt, ofReal_integral_eq_lintegral_ofReal]
    · exact (hf.comp ((continuous_chart D).comp (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport
        (hasCompactSupport_fibre D hfc _)
    · exact Filter.Eventually.of_forall fun g => hf0 _
  have h0 : 0 ≤ fibreInt D f (sec D c) := integral_nonneg fun g => hf0 _
  rw [hinner, mul_comm, ← ENNReal.ofReal_mul h0]

theorem eventually_subset_U0 {S : ℝ → Set (UIdx n → ℂ)} {c₀ : UIdx n → ℂ} (hc₀ : c₀ = coeffUC Q)
    (hshr : ∀ δ > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ), S ε ⊆ Metric.ball c₀ δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), S ε ⊆ U0 D := by
  subst hc₀
  obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp (isOpen_U0 D) _ (coeffUC_mem_U0 D)
  filter_upwards [hshr δ hδ] with ε hε
  exact hε.trans hsub

/-- **The Leray limit along a shrinking family, $f \ge 0$.** -/
theorem tendsto_approxGen_of_nonneg (S : ℝ → Set (UIdx n → ℂ)) (hmeas : ∀ ε, MeasurableSet (S ε))
    (hpos : ∀ ε > 0, 0 < volume (S ε)) (hfin : ∀ ε > 0, volume (S ε) ≠ ∞)
    (hshr : ∀ δ > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ), S ε ⊆ Metric.ball (coeffUC Q) δ)
    {f : (Fin n → Fin n → ℂ) → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hf0 : ∀ X, 0 ≤ f X) :
    Tendsto (approxGen Q S f) (𝓝[>] 0) (𝓝 (∫ g, f (cols (ArchSOC.mat Q g)) ∂lerayDC D)) := by
  set H : (UIdx n → ℂ) → ℝ := fun c => fibreInt D f (sec D c) * rho D c
  have hHc : ContinuousOn H (U0 D) :=
    ((continuous_fibreInt D hf hfc).comp_continuousOn (continuousOn_sec D)).mul (continuousOn_rho D)
  have hH0 : ∀ c ∈ U0 D, 0 ≤ H c := fun c _ => mul_nonneg (integral_nonneg fun g => hf0 _) (rho_nonneg D c)
  have h := tendsto_avg_family volume (c₀ := coeffUC Q) S hmeas hpos hfin hshr (isOpen_U0 D)
    (coeffUC_mem_U0 D) hHc hH0
  have hH1 : H (coeffUC Q) = ∫ g, f (cols (ArchSOC.mat Q g)) ∂lerayDC D := by
    simp only [H, rho_coeffUC, mul_one, sec_coeffUC, fibreInt, chart, SliceB.mat_one]
  rw [hH1] at h
  refine h.congr' ?_
  filter_upwards [eventually_subset_U0 D rfl hshr] with ε hsub
  rw [approxGen, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun X => hf0 X)
      hf.aestronglyMeasurable, lintegral_regionC_nonneg D hf hfc hf0 (hmeas ε) hsub]

/-- **The Leray limit along a shrinking family**: for every compactly supported continuous $f$,
$\frac{1}{\mathrm{Leb}(S_\varepsilon)}\int_{\{\operatorname{Re}\det X > 0,\ \Phi_Q(X) \in S_\varepsilon\}}f\,dX
\to \int_{SO(Q)(\mathbb C)}f\,d\mu_Q$. -/
theorem tendsto_approxGen (S : ℝ → Set (UIdx n → ℂ)) (hmeas : ∀ ε, MeasurableSet (S ε))
    (hpos : ∀ ε > 0, 0 < volume (S ε)) (hfin : ∀ ε > 0, volume (S ε) ≠ ∞)
    (hshr : ∀ δ > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ), S ε ⊆ Metric.ball (coeffUC Q) δ)
    {f : (Fin n → Fin n → ℂ) → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (approxGen Q S f) (𝓝[>] 0) (𝓝 (∫ g, f (cols (ArchSOC.mat Q g)) ∂lerayDC D)) := by
  set fp : (Fin n → Fin n → ℂ) → ℝ := fun X => max (f X) 0
  set fm : (Fin n → Fin n → ℂ) → ℝ := fun X => max (-f X) 0
  have hfp : Continuous fp := hf.max continuous_const
  have hfm : Continuous fm := hf.neg.max continuous_const
  have hfpc : HasCompactSupport fp := hfc.mono' (fun X hX => by
    by_contra h; exact hX (by simp [fp, Function.notMem_support.mp (fun h' => h (subset_tsupport f h'))]))
  have hfmc : HasCompactSupport fm := hfc.mono' (fun X hX => by
    by_contra h; exact hX (by simp [fm, Function.notMem_support.mp (fun h' => h (subset_tsupport f h'))]))
  have hp := tendsto_approxGen_of_nonneg D S hmeas hpos hfin hshr hfp hfpc (fun X => le_max_right _ _)
  have hm := tendsto_approxGen_of_nonneg D S hmeas hpos hfin hshr hfm hfmc (fun X => le_max_right _ _)
  have hsplit : ∀ ε, approxGen Q S f ε = approxGen Q S fp ε - approxGen Q S fm ε := by
    intro ε
    have hip : IntegrableOn fp (regionC Q (S ε)) := (hfp.integrable_of_hasCompactSupport hfpc).integrableOn
    have him : IntegrableOn fm (regionC Q (S ε)) := (hfm.integrable_of_hasCompactSupport hfmc).integrableOn
    rw [approxGen, approxGen, approxGen, ← sub_div, ← integral_sub hip him]
    congr 2; funext X; exact (max_zero_sub_max_neg_zero_eq_self (f X)).symm
  have hG : ∫ g, f (cols (ArchSOC.mat Q g)) ∂lerayDC D =
      ∫ g, fp (cols (ArchSOC.mat Q g)) ∂lerayDC D - ∫ g, fm (cols (ArchSOC.mat Q g)) ∂lerayDC D := by
    have hc1 := hasCompactSupport_fibre D hfpc 1
    have hc2 := hasCompactSupport_fibre D hfmc 1
    simp only [chart, SliceB.mat_one, Matrix.mul_one] at hc1 hc2
    have i1 : Integrable (fun g => fp (cols (ArchSOC.mat Q g))) (lerayDC D) :=
      (hfp.comp (continuous_cols.comp (ArchSOC.continuous_mat Q))).integrable_of_hasCompactSupport hc1
    have i2 : Integrable (fun g => fm (cols (ArchSOC.mat Q g))) (lerayDC D) :=
      (hfm.comp (continuous_cols.comp (ArchSOC.continuous_mat Q))).integrable_of_hasCompactSupport hc2
    rw [← integral_sub i1 i2]
    congr 1; funext g; exact (max_zero_sub_max_neg_zero_eq_self _).symm
  rw [hG, show approxGen Q S f = fun ε => approxGen Q S fp ε - approxGen Q S fm ε from funext hsplit]
  exact hp.sub hm

end General

/-! ### Transport by $X \mapsto G^{-1}XG$ -/

section Transport

variable (G : GL (Fin n) ℂ)

/-- **The linear map** $X \mapsto G^{-1}XG$ on $M_n(\mathbb C)$ in column coordinates. -/
def conjL : (Fin n → Fin n → ℂ) →ₗ[ℂ] (Fin n → Fin n → ℂ) :=
  rmulL (G : 𝕄) ∘ₗ lmulL ((G⁻¹ : GL (Fin n) ℂ) : 𝕄)

/-- **The inverse linear map** $X \mapsto GXG^{-1}$. -/
def conjL' : (Fin n → Fin n → ℂ) →ₗ[ℂ] (Fin n → Fin n → ℂ) :=
  rmulL ((G⁻¹ : GL (Fin n) ℂ) : 𝕄) ∘ₗ lmulL (G : 𝕄)

theorem conjL_apply (X : Fin n → Fin n → ℂ) :
    conjL G X = cols (((G⁻¹ : GL (Fin n) ℂ) : 𝕄) * ofCols X * (G : 𝕄)) := by
  rw [cols_mul_right, cols_mul_left]; rfl

theorem conjL'_apply (X : Fin n → Fin n → ℂ) :
    conjL' G X = cols ((G : 𝕄) * ofCols X * ((G⁻¹ : GL (Fin n) ℂ) : 𝕄)) := by
  rw [cols_mul_right, cols_mul_left]; rfl

theorem conj_cancel (A B : 𝕄) (h : A * B = 1) (M : 𝕄) : A * (B * M * A) * B = M :=
  calc A * (B * M * A) * B = (A * B) * M * (A * B) := by simp only [Matrix.mul_assoc]
    _ = M := by rw [h, Matrix.one_mul, Matrix.mul_one]

/-- **$X \mapsto G^{-1}XG$ as a homeomorphism** of $M_n(\mathbb C)$ (column coordinates). -/
def conjH : (Fin n → Fin n → ℂ) ≃ₜ (Fin n → Fin n → ℂ) where
  toFun := conjL G
  invFun := conjL' G
  left_inv X := by
    show conjL' G (conjL G X) = X
    rw [conjL_apply, conjL'_apply, ofCols_cols, conj_cancel _ _ (units_mul_inv_val G)]; rfl
  right_inv X := by
    show conjL G (conjL' G X) = X
    rw [conjL'_apply, conjL_apply, ofCols_cols, conj_cancel _ _ (units_inv_mul_val G)]; rfl
  continuous_toFun := LinearMap.continuous_of_finiteDimensional _
  continuous_invFun := LinearMap.continuous_of_finiteDimensional _

theorem conjH_apply (X : Fin n → Fin n → ℂ) : conjH G X = conjL G X := rfl

theorem ofCols_conjH (X : Fin n → Fin n → ℂ) :
    ofCols (conjH G X) = ((G⁻¹ : GL (Fin n) ℂ) : 𝕄) * ofCols X * (G : 𝕄) := by
  rw [conjH_apply, conjL_apply, ofCols_cols]

theorem det_conjL : LinearMap.det (conjL G) = 1 := by
  rw [conjL, LinearMap.det_comp, det_rmulL, det_lmulL, ← mul_pow, mul_comm, ← det_mul,
    units_inv_mul_val G, det_one, one_pow]

/-- **$X \mapsto G^{-1}XG$ preserves the Lebesgue measure** of $M_n(\mathbb C)$. -/
theorem measurePreserving_conjH :
    MeasurePreserving (conjH G).toMeasurableEquiv volume volume := by
  refine ⟨(conjH G).toMeasurableEquiv.measurable, ?_⟩
  have h := map_clm_addHaar (volume : Measure (Fin n → Fin n → ℂ)) (conjL G)
    (by rw [det_conjL]; exact one_ne_zero)
  rw [det_conjL] at h
  have h' : Measure.map (⇑(conjL G)) volume = volume := by simpa using h
  exact h'

variable {Q Q' : QuadForm ℂ n} (c : ℂ)

/-- **The region under conjugation**: $\{X : \operatorname{Re}\det X > 0,\ \Phi_Q(X) \in L^{-1}B\} =
\{X : G^{-1}XG \in \text{region of } Q' \text{ over } B\}$. -/
theorem regionC_simConj
    (hH : Q'.hessian = c • ((G : 𝕄)ᵀ * Q.hessian * (G : 𝕄))) (B : Set (UIdx n → ℂ)) :
    regionC Q ((c • act (G : 𝕄)) ⁻¹' B) = conjH G ⁻¹' regionC Q' B := by
  ext X
  simp only [regionC, mem_ofPred_eq, mem_preimage, ofCols_conjH, det_conj_val, phi_simConj G c hH]

theorem setIntegral_simConj
    (hH : Q'.hessian = c • ((G : 𝕄)ᵀ * Q.hessian * (G : 𝕄))) (B : Set (UIdx n → ℂ))
    (f : (Fin n → Fin n → ℂ) → ℝ) :
    ∫ Y in regionC Q' B, f Y = ∫ X in regionC Q ((c • act (G : 𝕄)) ⁻¹' B), f (conjH G X) := by
  rw [regionC_simConj G c hH B]
  exact ((measurePreserving_conjH G).setIntegral_preimage_emb
    (conjH G).toMeasurableEquiv.measurableEmbedding f _).symm

end Transport

/-! ### The Leray measure under a similarity -/

section Main

variable {Q Q' : QuadForm ℂ n} (G : GL (Fin n) ℂ) (c : ℂ)

theorem coeffUC_simArch (hH : Q'.hessian = c • ((G : 𝕄)ᵀ * Q.hessian * (G : 𝕄))) :
    coeffUC Q' = (c • act (G : 𝕄)) (coeffUC Q) := by
  have h := phi_simConj G c hH 1
  rw [Matrix.mul_one, units_inv_mul_val G, phi_one, phi_one] at h
  exact h

/-- The inverse of $c\cdot\mathrm{act}\,G$ on coefficient space. -/
theorem simArch_inv (hc : c ≠ 0) (v : UIdx n → ℂ) :
    (c⁻¹ • act ((G⁻¹ : GL (Fin n) ℂ) : 𝕄)) ((c • act (G : 𝕄)) v) = v ∧
    (c • act (G : 𝕄)) ((c⁻¹ • act ((G⁻¹ : GL (Fin n) ℂ) : 𝕄)) v) = v := by
  constructor
  · simp only [LinearMap.smul_apply, map_smul, smul_smul]
    rw [← act_mul, units_mul_inv_val G, act_one]
    simp [hc]
  · simp only [LinearMap.smul_apply, map_smul, smul_smul]
    rw [← act_mul, units_inv_mul_val G, act_one]
    simp [hc]

/-- **Shrinking family**: the preimages $L^{-1}\bar B_\varepsilon(L c_0)$ eventually lie in every ball about $c_0$. -/
theorem simArch_shrink (hc : c ≠ 0) (c₀ : UIdx n → ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (c • act (G : 𝕄)) ⁻¹' Metric.closedBall ((c • act (G : 𝕄)) c₀) ε ⊆ Metric.ball c₀ δ := by
  have hcont : Continuous ⇑(c⁻¹ • act ((G⁻¹ : GL (Fin n) ℂ) : 𝕄)) :=
    LinearMap.continuous_of_finiteDimensional _
  obtain ⟨ε0, hε0, h0⟩ := Metric.continuousAt_iff.mp hcont.continuousAt δ hδ
  filter_upwards [Ioo_mem_nhdsGT hε0] with ε hε z hz
  have hz' : dist ((c • act (G : 𝕄)) z) ((c • act (G : 𝕄)) c₀) ≤ ε := hz
  have hd : dist ((c • act (G : 𝕄)) z - (c • act (G : 𝕄)) c₀) 0 < ε0 := by
    rw [dist_zero_right, ← dist_eq_norm]; exact lt_of_le_of_lt hz' hε.2
  have := h0 hd
  rw [map_zero, dist_zero_right, map_sub, (simArch_inv G c hc z).1, (simArch_inv G c hc c₀).1,
    ← dist_eq_norm] at this
  exact this

/-- **The Leray measure under a similarity**, in terms of $L = c\cdot\mathrm{act}\,G$:
$(\mathrm{conj})_*\mu_Q = |\det_{\mathbb C}L|^2\mu_{Q'}$, where $\mathrm{conj}(g) = G^{-1}gG$ and
$H_{Q'} = c\,G^{\mathsf T}H_QG$, $c \ne 0$, both forms nondegenerate. -/
theorem map_lerayMeasureC_conjSOC
    (hH : Q'.hessian = c • ((G : 𝕄)ᵀ * Q.hessian * (G : 𝕄))) (hc : c ≠ 0)
    (hQ : gramDetC Q ≠ 0) (hQ' : gramDetC Q' ≠ 0) :
    (lerayMeasureC Q hQ).map (conjSOC G c hH hc) =
      ENNReal.ofReal (‖LinearMap.det (c • act (G : 𝕄))‖ ^ 2) • lerayMeasureC Q' hQ' := by
  set L : (UIdx n → ℂ) →ₗ[ℂ] (UIdx n → ℂ) := c • act (G : 𝕄) with hL
  have hdet : LinearMap.det L ≠ 0 :=
    det_ne_zero_of_inv L (c⁻¹ • act ((G⁻¹ : GL (Fin n) ℂ) : 𝕄)) (fun v => (simArch_inv G c hc v).2)
  set k : ℝ≥0 := ‖LinearMap.det L‖₊ ^ 2 with hk
  have hk0 : k ≠ 0 := pow_ne_zero _ (nnnorm_ne_zero_iff.mpr hdet)
  have hkR : (k : ℝ) = ‖LinearMap.det L‖ ^ 2 := by simp [hk]
  set D := DiagC.ofExists Q hQ with hD
  -- the comparison measure
  set e := conjSOC G c hH hc
  haveI : (lerayMeasureC Q hQ).IsHaarMeasure := isHaarMeasure_lerayMeasureC hQ
  haveI : ((lerayMeasureC Q hQ).map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ e
  set μ'' : Measure (ArchSOC Q') := ((k⁻¹ : ℝ≥0) : ℝ≥0∞) • (lerayMeasureC Q hQ).map e with hμ''
  haveI : μ''.IsHaarMeasure :=
    Measure.IsHaarMeasure.smul _ (by simpa using hk0) ENNReal.coe_ne_top
  -- the shrinking family
  set S : ℝ → Set (UIdx n → ℂ) := fun ε => L ⁻¹' Metric.closedBall (coeffUC Q') ε with hS
  have hcc : coeffUC Q' = L (coeffUC Q) := coeffUC_simArch G c hH
  have hLc : Continuous L := LinearMap.continuous_of_finiteDimensional _
  have hmeas : ∀ ε, MeasurableSet (S ε) := fun ε =>
    hLc.measurable Metric.isClosed_closedBall.measurableSet
  have hvol : ∀ ε, volume (S ε) = ((k⁻¹ : ℝ≥0) : ℝ≥0∞) * volume (Metric.closedBall (coeffUC Q') ε) := by
    intro ε
    have h := map_clm_addHaar (volume : Measure (UIdx n → ℂ)) L hdet
    rw [← Measure.map_apply hLc.measurable Metric.isClosed_closedBall.measurableSet, h,
      Measure.smul_apply, smul_eq_mul]
  have hpos : ∀ ε > 0, 0 < volume (S ε) := fun ε hε => by
    rw [hvol]
    exact ENNReal.mul_pos (by simpa using hk0) (volume_closedBall_pos (Q := Q') hε).ne'
  have hfin : ∀ ε > 0, volume (S ε) ≠ ∞ := fun ε hε => by
    rw [hvol]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (volume_closedBall_ne_top (Q := Q') ε)
  have hshr : ∀ δ > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ), S ε ⊆ Metric.ball (coeffUC Q) δ := fun δ hδ => by
    have := simArch_shrink G c hc (coeffUC Q) hδ
    rw [← hcc] at this
    exact this
  have hvolR : ∀ ε, (volume (Metric.closedBall (coeffUC Q') ε)).toReal = k * (volume (S ε)).toReal := by
    intro ε
    rw [hvol, ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_inv]
    have : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
    field_simp
  -- the Leray limit for the comparison measure
  have hlim : ∀ f : (Fin n → Fin n → ℂ) → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (lerayApproxC Q' f) (𝓝[>] 0) (𝓝 (∫ g, f (cols (ArchSOC.mat Q' g)) ∂μ'')) := by
    intro f hf hfc
    have hfH : Continuous (f ∘ conjH G) := hf.comp (conjH G).continuous
    have hfHc : HasCompactSupport (f ∘ conjH G) := hfc.comp_homeomorph (conjH G)
    have h1 := (tendsto_approxGen D S hmeas hpos hfin hshr hfH hfHc).const_mul ((k : ℝ)⁻¹)
    have hint : ∫ g, f (cols (ArchSOC.mat Q' g)) ∂μ'' =
        (k : ℝ)⁻¹ * ∫ g, (f ∘ conjH G) (cols (ArchSOC.mat Q g)) ∂lerayDC D := by
      rw [hμ'', integral_smul_measure, ENNReal.coe_toReal, NNReal.coe_inv, smul_eq_mul]
      congr 1
      have hm : AEStronglyMeasurable (fun g : ArchSOC Q' => f (cols (ArchSOC.mat Q' g)))
          ((lerayMeasureC Q hQ).map e) :=
        (hf.comp (continuous_cols.comp (ArchSOC.continuous_mat Q'))).aestronglyMeasurable
      rw [integral_map (μ := lerayMeasureC Q hQ) (φ := ⇑e)
        (f := fun g : ArchSOC Q' => f (cols (ArchSOC.mat Q' g))) e.continuous.measurable.aemeasurable hm]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      simp only [Function.comp]
      rw [conjSOC_mat, conjH_apply, conjL_apply, ofCols_cols]
    rw [hint]
    refine h1.congr fun ε => ?_
    rw [lerayApproxC, approxGen, lerayRegionC, setIntegral_simConj G c hH, hvolR]
    simp only [hS, Function.comp]
    ring
  have huniq := lerayMeasureC_unique hQ' μ'' hlim
  have hmap : (lerayMeasureC Q hQ).map e = (k : ℝ≥0∞) • μ'' := by
    rw [hμ'', smul_smul, ← ENNReal.coe_mul, mul_inv_cancel₀ hk0, ENNReal.coe_one, one_smul]
  rw [hmap, huniq, ← ENNReal.ofReal_coe_nnreal, hkR]

/-- **The Leray measure under a similarity, explicit factor**:
$(\mathrm{conj})_*\mu_Q = |c|^{2\cdot n(n+1)/2}\,|\det G|^{2(n+1)}\,\mu_{Q'}$. For $G = 1$, $Q' = cQ$ this is
$\mu_Q = |c|^{n(n+1)}\mu_{cQ}$. -/
theorem map_lerayMeasureC_conjSOC'
    (hH : Q'.hessian = c • ((G : 𝕄)ᵀ * Q.hessian * (G : 𝕄))) (hc : c ≠ 0)
    (hQ : gramDetC Q ≠ 0) (hQ' : gramDetC Q' ≠ 0) :
    (lerayMeasureC Q hQ).map (conjSOC G c hH hc) =
      ENNReal.ofReal (‖c‖ ^ (2 * (n * (n + 1) / 2)) * ‖(G : 𝕄).det‖ ^ (2 * (n + 1))) •
        lerayMeasureC Q' hQ' := by
  rw [map_lerayMeasureC_conjSOC G c hH hc hQ hQ', det_smul_act, norm_mul, norm_pow, norm_pow, mul_pow,
    ← pow_mul, ← pow_mul, mul_comm (n * (n + 1) / 2) 2, mul_comm (n + 1) 2]

end Main

end QuadFormsKB.Tamagawa.Measure.LerayComplex
