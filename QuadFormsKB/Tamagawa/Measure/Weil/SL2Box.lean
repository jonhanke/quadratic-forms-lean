import QuadFormsKB.Tamagawa.Measure.Weil.SL2Fibration
import QuadFormsKB.Tamagawa.Measure.Weil.AdditiveChart
import QuadFormsKB.Tamagawa.Measure.Weil.AdditiveScaling
import QuadFormsKB.Tamagawa.Measure.Weil.Ideles
import QuadFormsKB.Tamagawa.Measure.Weil.SL2Tamagawa

/-!
# The local factors of $\mu_T$ on $\mathrm{SL}_2(\mathbb A_F)$: the box computation

$F$ any number field. The fibration measure $\mu_T$ (`SL2Measure.lean`, = `OrbitSection.fibMeasure` by
`muT_eq_fibMeasure`) is compared with Weil's product $\prod_v|\omega|_v$ of local gauge-form measures (AAG §2.2–2.3).

* **Primitive vectors in $\hat{\mathcal O}^2$.** `primHat` $=\{z\in\hat{\mathcal O}^2 : z_v$ primitive for every $v\}$
  $=\prod_v\mathrm{Prim}(\mathcal O_v^2)$; **`muFinVec_primHat`**:
  $\mu_f^{\otimes 2}(\mathrm{primHat}) = \operatorname{vol}(\hat{\mathcal O})^2\prod_v(1 - N(v)^{-2})$, from the infinite
  product description of $\mu_f$ on $\prod_v\mathcal O_v^2$ (`comap_jj_muFinVec`, uniqueness of Haar measure on a
  compact group) and the local value $\mathrm{vol}(\mathrm{Prim}(\mathcal O_v^2)) = (1 - N(v)^{-2})\,\mathrm{vol}(\mathcal O_v)^2$
  (**`selfDualV_primV`**, the complement is $\mathfrak p_v\times\mathfrak p_v$).
* **The box computation** (**`muT_box`**): for every measurable set $U$ of archimedean matrices,
  $$\mu_T\{g : g_f\in M_2(\hat{\mathcal O}),\ g_\infty\in U\} = \mu_{T,\infty}(U)\cdot\operatorname{vol}(\hat{\mathcal O})^3
  \cdot\prod_v\big(1 - N(v)^{-2}\big),$$
  where $\mu_{T,\infty}$ (`muTInf`) is the archimedean fibration measure $\Psi_{\infty*}(dy_\infty|_{P_\infty}\otimes dx_\infty)$
  and $\operatorname{vol}(\hat{\mathcal O}) = |d_F|^{-1/2} = \prod_v\operatorname{vol}(\mathcal O_v)$. Since
  $\mathrm{vol}_v(\mathrm{SL}_2(\mathcal O_v)) = \mathrm{vol}(\mathrm{Prim}(\mathcal O_v^2))\cdot\mathrm{vol}(\mathcal O_v)
  = (1 - N(v)^{-2})\operatorname{vol}(\mathcal O_v)^3$ is the local gauge-form volume (Weil's Thm 2.2.5:
  $q^{-3}\#\mathrm{SL}_2(\mathbb F_q) = 1 - q^{-2}$), this says that $\mu_T$ is $\mu_{T,\infty}\otimes\prod_v|\omega|_v$ on
  $\mathrm{SL}_2(F_\infty)\times\prod_v\mathrm{SL}_2(\mathcal O_v)$, with convergence factors $\lambda_v = 1$.
-/

open IsDedekindDomain NumberField MeasureTheory Measure Filter Topology NumberField.mixedEmbedding
open scoped ENNReal NNReal Classical MatrixGroups

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### Primitive vectors at one place -/

/-- For integral $a, c$: $(a, c)$ is primitive iff not both lie in $\mathfrak p_v$. -/
theorem isPrim_iff_of_integral (v : HeightOneSpectrum (𝓞 F)) {a c : v.adicCompletion F} (ha : valV v a ≤ 1)
    (hc : valV v c ≤ 1) : IsPrim (valV v) a c ↔ ¬ (valV v a < 1 ∧ valV v c < 1) := by
  have key : ∀ x : v.adicCompletion F, valV v x ≤ 1 → ((x ≠ 0 ∧ valV v x⁻¹ ≤ 1) ↔ ¬ valV v x < 1) := by
    intro x hx
    constructor
    · rintro ⟨hx0, hxi⟩ hlt
      rw [map_inv₀] at hxi
      have h0 : valV v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
      have : 1 ≤ valV v x := (inv_le_one₀ (zero_lt_iff.2 h0)).1 hxi
      exact absurd hlt (not_lt.2 this)
    · intro hn
      have h1 : valV v x = 1 := le_antisymm hx (not_lt.1 hn)
      refine ⟨fun h => by rw [h, map_zero] at h1; exact zero_ne_one h1, ?_⟩
      rw [map_inv₀, h1, inv_one]
  unfold IsPrim
  rw [key a ha, key c hc]
  tauto

variable (F) in
/-- $\prod_v\mathcal O_v^2$. -/
abbrev O2Prod : Type := ∀ v : HeightOneSpectrum (𝓞 F), (Fin 2 → v.adicCompletionIntegers F)

/-- The primitive vectors of $\mathcal O_v^2$. -/
def primV (v : HeightOneSpectrum (𝓞 F)) : Set (Fin 2 → v.adicCompletionIntegers F) :=
  {z | IsPrim (valV v) (z 0 : v.adicCompletion F) (z 1 : v.adicCompletion F)}

/-- $\mathfrak p_v$ inside $\mathcal O_v$. -/
def maxV (v : HeightOneSpectrum (𝓞 F)) : Set (v.adicCompletionIntegers F) :=
  {t | valV v (t : v.adicCompletion F) < 1}

theorem primV_compl (v : HeightOneSpectrum (𝓞 F)) : (primV v)ᶜ = Set.univ.pi fun _ => maxV v := by
  ext z
  simp only [primV, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_univ_pi, maxV]
  rw [isPrim_iff_of_integral v (z 0).2 (z 1).2, not_not]
  constructor
  · rintro ⟨h0, h1⟩ i; fin_cases i <;> assumption
  · intro h; exact ⟨h 0, h 1⟩

theorem measurableSet_maxV (v : HeightOneSpectrum (𝓞 F)) : MeasurableSet (maxV v) := by
  have : maxV v = Subtype.val ⁻¹' (Analysis.latticeV v 1 : Set (v.adicCompletion F)) := by
    ext t; simp [maxV, lt_one_iff_mem_latticeV]
  rw [this]
  exact measurable_subtype_coe (Analysis.measurableSet_latticeV v 1)

theorem measurableSet_primV (v : HeightOneSpectrum (𝓞 F)) : MeasurableSet (primV v) := by
  rw [← compl_compl (primV v), primV_compl]
  exact (MeasurableSet.univ_pi fun _ => measurableSet_maxV v).compl

/-- $\mathrm{vol}_{\mathrm{sd}}(\mathfrak p_v) = N(v)^{-1}\,\mathrm{vol}_{\mathrm{sd}}(\mathcal O_v)$. -/
theorem selfDualV_latticeV_one (v : HeightOneSpectrum (𝓞 F)) :
    Analysis.selfDualV v (Analysis.latticeV v 1) = ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) * volO v := by
  have e1 : Analysis.selfDualV v (Analysis.latticeV v 1) =
      ENNReal.ofReal ((Analysis.selfDualV v).real (Analysis.latticeV v 1)) :=
    (ENNReal.ofReal_toReal ((Analysis.isCompact_latticeV v 1).measure_lt_top.ne)).symm
  rw [e1, volO_eq_ofReal, ← ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg _)),
    Analysis.selfDualV_real_latticeV, Analysis.selfDualV_real_latticeV, ← Analysis.modV_eq]
  congr 1
  simp only [zpow_one, zpow_zero, mul_one]
  ring

/-- The normalized measure of $\mathfrak p_v$ is $N(v)^{-1}$. -/
theorem haarO_maxV (v : HeightOneSpectrum (𝓞 F)) :
    haarO v (maxV v) = ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) := by
  rw [haarO_apply]
  have : Subtype.val '' maxV v = (Analysis.latticeV v 1 : Set (v.adicCompletion F)) := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩; exact (lt_one_iff_mem_latticeV v _).1 hs
    · intro ht
      have hlt := (lt_one_iff_mem_latticeV v t).2 ht
      exact ⟨⟨t, hlt.le⟩, hlt, rfl⟩
  rw [this, selfDualV_latticeV_one, mul_comm, mul_assoc, ENNReal.mul_inv_cancel (volO_pos v).ne'
    (volO_ne_top v), mul_one]

theorem absNorm_inv_le_one (v : HeightOneSpectrum (𝓞 F)) : (Ideal.absNorm v.asIdeal : ℝ)⁻¹ ≤ 1 := by
  have h2 : 2 ≤ Ideal.absNorm v.asIdeal := QuadFormsKB.NFEuler.two_le_normP v
  have : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast le_trans (by norm_num) h2
  exact inv_le_one_of_one_le₀ this

/-- **The normalized local volume of the primitive vectors:** $1 - N(v)^{-2}$. -/
theorem haarO_pi_primV (v : HeightOneSpectrum (𝓞 F)) :
    (Measure.pi fun _ : Fin 2 => haarO v) (primV v) = ENNReal.ofReal (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹ ^ 2) := by
  have hc := prob_compl_eq_one_sub (μ := Measure.pi fun _ : Fin 2 => haarO v) (measurableSet_primV v)
  rw [primV_compl, Measure.pi_pi, Fin.prod_univ_two, haarO_maxV] at hc
  have hq := absNorm_inv_le_one v
  have hq0 : (0 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hfin : (Measure.pi fun _ : Fin 2 => haarO v) (primV v) ≠ ∞ := measure_ne_top _ _
  have h1 : (Measure.pi fun _ : Fin 2 => haarO v) (primV v) =
      1 - ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) * ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) := by
    rw [hc, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
  rw [h1, ← ENNReal.ofReal_mul hq0, ← sq, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub _ (sq_nonneg _)]

/-- **The local factor:** $\mathrm{vol}_{\mathrm{sd}}(\mathrm{Prim}(\mathcal O_v^2)) = (1 - N(v)^{-2})\,
\mathrm{vol}_{\mathrm{sd}}(\mathcal O_v)^2$, hence the gauge-form volume of $\mathrm{SL}_2(\mathcal O_v) =
\{s(y)n(x) : y\in\mathrm{Prim}(\mathcal O_v^2),\ x\in\mathcal O_v\}$ is $(1 - N(v)^{-2})\,\mathrm{vol}(\mathcal O_v)^3$
(Weil's Thm 2.2.5 for $\mathrm{SL}_2$: $q^{-3}\#\mathrm{SL}_2(\mathbb F_q) = 1 - q^{-2}$). -/
@[kb "weil1982" "§2.2, Thm 2.2.5 (volume of G(O_v)) [unverified page]"]
theorem selfDualV_primV (v : HeightOneSpectrum (𝓞 F)) :
    (Measure.pi fun _ : Fin 2 => Analysis.selfDualV v)
        ((fun z : Fin 2 → v.adicCompletionIntegers F => fun i => (z i : v.adicCompletion F)) '' primV v) =
      ENNReal.ofReal (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹ ^ 2) * volO v ^ 2 := by
  have hset : (fun z : Fin 2 → v.adicCompletionIntegers F => fun i => (z i : v.adicCompletion F)) '' primV v =
      Set.univ.pi (fun _ => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) \
        Set.univ.pi (fun _ => (Analysis.latticeV v 1 : Set (v.adicCompletion F))) := by
    ext z
    simp only [Set.mem_image, Set.mem_sdiff, Set.mem_univ_pi]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨fun i => (w i).2, fun h => ?_⟩
      have := (isPrim_iff_of_integral v (w 0).2 (w 1).2).1 hw
      exact this ⟨(lt_one_iff_mem_latticeV v _).2 (h 0), (lt_one_iff_mem_latticeV v _).2 (h 1)⟩
    · rintro ⟨hO, hn⟩
      refine ⟨fun i => ⟨z i, hO i⟩, ?_, rfl⟩
      show IsPrim (valV v) (z 0) (z 1)
      rw [isPrim_iff_of_integral v (hO 0) (hO 1)]
      rintro ⟨h0, h1⟩
      apply hn
      intro i; fin_cases i
      · exact (lt_one_iff_mem_latticeV v _).1 h0
      · exact (lt_one_iff_mem_latticeV v _).1 h1
  have hsub : Set.univ.pi (fun _ : Fin 2 => (Analysis.latticeV v 1 : Set (v.adicCompletion F))) ⊆
      Set.univ.pi (fun _ => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
    intro z hz i _
    exact ((lt_one_iff_mem_latticeV v _).2 (hz i (Set.mem_univ _))).le
  rw [hset, measure_sdiff hsub (MeasurableSet.univ_pi fun _ => Analysis.measurableSet_latticeV v 1).nullMeasurableSet
      (measure_ne_top_of_subset hsub), Measure.pi_pi, Measure.pi_pi, Fin.prod_univ_two, Fin.prod_univ_two,
    selfDualV_latticeV_one]
  · rw [show Analysis.selfDualV v (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = volO v from rfl]
    have hq0 : (0 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    have hq := absNorm_inv_le_one v
    rw [volO_eq_ofReal]
    set V := (Analysis.selfDualV v).real (Analysis.latticeV v 0)
    have hV : 0 ≤ V := measureReal_nonneg
    set q := (Ideal.absNorm v.asIdeal : ℝ)⁻¹
    rw [← ENNReal.ofReal_mul hq0, ← ENNReal.ofReal_mul hV, ← ENNReal.ofReal_mul (mul_nonneg hq0 hV),
      ← ENNReal.ofReal_pow hV, ← ENNReal.ofReal_mul (by nlinarith), ← ENNReal.ofReal_sub _ (by positivity)]
    congr 1
    ring

where
  measure_ne_top_of_subset {s t : Set (Fin 2 → v.adicCompletion F)} (h : s ⊆ t)
      (ht : t = Set.univ.pi (fun _ => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by rfl) :
      (Measure.pi fun _ : Fin 2 => Analysis.selfDualV v) s ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono h)
    rw [ht, Measure.pi_pi]
    exact ENNReal.prod_ne_top fun _ _ => volO_ne_top v

/-! ### Primitive vectors in $\hat{\mathcal O}^2$ -/

variable (F) in
/-- The infinite product $\bigotimes_v(\mu_v|_{\mathcal O_v}/\mu_v(\mathcal O_v))^{\otimes 2}$ on $\prod_v\mathcal O_v^2$. -/
def nu2 : Measure (O2Prod F) := Measure.infinitePi fun v => Measure.pi fun _ : Fin 2 => haarO v

instance : IsProbabilityMeasure (nu2 F) := by unfold nu2; infer_instance

instance (v : HeightOneSpectrum (𝓞 F)) : (Measure.pi fun _ : Fin 2 => haarO v).IsAddLeftInvariant := by
  infer_instance

instance : (nu2 F).IsAddLeftInvariant := by
  unfold nu2; exact Measure.infinitePi_isAddLeftInvariant _

variable (F) in
/-- The embedding $\prod_v\mathcal O_v^2\to\mathbb A_f^2$. -/
def jj (z : O2Prod F) : Fin 2 → AF := fun i => iK F fun v => z v i

theorem jj_add (x y : O2Prod F) : jj F (x + y) = jj F x + jj F y := rfl

theorem range_jj : Set.range (jj F) = {y : Fin 2 → AF | ∀ i, y i ∈ OHat} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩ i v; exact (z v i).2
  · intro hy; exact ⟨fun v i => ⟨y i v, hy i v⟩, rfl⟩

theorem jj_injective : Function.Injective (jj F) := by
  intro x y h
  funext v i
  exact Subtype.ext (congrArg (fun z : Fin 2 → AF => z i v) h)

variable (F) in
/-- $\prod_v\mathcal O_v^2\cong(\prod_v\mathcal O_v)^2$. -/
def ePi : O2Prod F ≃ₜ (Fin 2 → OProd F) where
  toFun z i v := z v i
  invFun w v i := w i v
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi fun i => continuous_pi fun v =>
    (continuous_apply i).comp (continuous_apply v)
  continuous_invFun := continuous_pi fun v => continuous_pi fun i =>
    (continuous_apply v).comp (continuous_apply i)

theorem isOpenEmbedding_jj : Topology.IsOpenEmbedding (jj F) :=
  (Topology.IsOpenEmbedding.piMap fun _ : Fin 2 => isOpenEmbedding_iK (F := F)).comp (ePi F).isOpenEmbedding

theorem measurableEmbedding_jj : MeasurableEmbedding (jj F) := isOpenEmbedding_jj.measurableEmbedding

instance : (Measure.comap (jj F) (muFinVec F (Fin 2))).IsAddLeftInvariant := by
  refine ⟨fun x => Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply (measurable_const_add x) hs, measurableEmbedding_jj.comap_apply,
    measurableEmbedding_jj.comap_apply]
  have : jj F '' ((x + ·) ⁻¹' s) = (jj F x + ·) ⁻¹' (jj F '' s) := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨x + z, hz, (jj_add x z)⟩
    · rintro ⟨w, hw, hwy⟩
      have hy : y ∈ Set.range (jj F) := by
        rw [range_jj]
        have : y = jj F w - jj F x := by rw [hwy]; abel
        intro i
        rw [this]
        exact sub_mem_OHat (fun v => (w v i).2) (fun v => (x v i).2)
      obtain ⟨z, rfl⟩ := hy
      refine ⟨z, ?_, rfl⟩
      have : x + z = w := jj_injective (by rw [jj_add, hwy])
      rw [this]; exact hw
  rw [this, measure_preimage_add]

theorem comap_jj_univ :
    Measure.comap (jj F) (muFinVec F (Fin 2)) Set.univ = ENNReal.ofReal (ohatVol F) ^ 2 := by
  rw [measurableEmbedding_jj.comap_apply, Set.image_univ, range_jj]
  have : {y : Fin 2 → AF | ∀ i, y i ∈ OHat} = Set.univ.pi fun _ => OHat := by
    ext y; simp
  rw [this, muFinVec, Measure.pi_pi, Fin.prod_univ_two, muFin_OHat, sq]

instance : IsFiniteMeasure (Measure.comap (jj F) (muFinVec F (Fin 2))) :=
  ⟨by rw [comap_jj_univ]; exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top⟩

/-- **`muFin^{⊗2}` on $\hat{\mathcal O}^2$ is the infinite product of the local measures:** the pull-back to
$\prod_v\mathcal O_v^2$ is $\operatorname{vol}(\hat{\mathcal O})^2\cdot$ `nu2` (uniqueness of Haar measure on a compact
group). -/
theorem comap_jj_muFinVec :
    Measure.comap (jj F) (muFinVec F (Fin 2)) = ENNReal.ofReal (ohatVol F) ^ 2 • nu2 F := by
  set lam := Measure.comap (jj F) (muFinVec F (Fin 2))
  have h1 := Measure.isAddInvariant_eq_smul_of_compactSpace lam (Measure.addHaar (G := O2Prod F))
  have h2 := Measure.isAddInvariant_eq_smul_of_compactSpace (nu2 F) (Measure.addHaar (G := O2Prod F))
  set c₁ := Measure.addHaarScalarFactor lam Measure.addHaar
  set c₂ := Measure.addHaarScalarFactor (nu2 F) Measure.addHaar
  have hc₂ : (c₂ : ℝ≥0∞) ≠ 0 := by
    intro h0
    have : (nu2 F) Set.univ = 0 := by
      rw [h2, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, h0, zero_mul]
    simp at this
  have h3 : lam = ((c₁ : ℝ≥0∞) * (c₂ : ℝ≥0∞)⁻¹) • nu2 F := by
    rw [h1]
    conv_rhs => rw [h2]
    ext s hs
    simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def]
    rw [← mul_assoc, mul_assoc (c₁ : ℝ≥0∞), ENNReal.inv_mul_cancel hc₂ ENNReal.coe_ne_top, mul_one]
  have h4 : lam Set.univ = (c₁ : ℝ≥0∞) * (c₂ : ℝ≥0∞)⁻¹ := by
    rw [h3, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← comap_jj_univ, h4]
  exact h3

variable (F) in
/-- **The vectors of $\hat{\mathcal O}^2$ that are primitive at every finite place.** -/
def primHat : Set (Fin 2 → AF) :=
  {z | (∀ i, z i ∈ OHat) ∧ ∀ v, IsPrim (valV v) (z 0 v) (z 1 v)}

theorem primHat_eq_image : primHat F = jj F '' Set.univ.pi primV := by
  ext z
  constructor
  · rintro ⟨hO, hP⟩
    exact ⟨fun v i => ⟨z i v, hO i v⟩, fun v _ => hP v, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨fun i v => (w v i).2, fun v => hw v (Set.mem_univ v)⟩

/-- **$\mu_f^{\otimes2}(\mathrm{primHat}) = \operatorname{vol}(\hat{\mathcal O})^2\prod_v(1 - N(v)^{-2})$.** -/
@[kb "weil1982" "§2.3, p. 21 (product of local volumes, λ_v = 1) [page checked in the design table]"]
theorem muFinVec_primHat :
    muFinVec F (Fin 2) (primHat F) =
      ENNReal.ofReal (ohatVol F) ^ 2 * ∏' v : HeightOneSpectrum (𝓞 F),
        ENNReal.ofReal (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹ ^ 2) := by
  rw [primHat_eq_image, ← measurableEmbedding_jj.comap_apply, comap_jj_muFinVec, Measure.smul_apply,
    smul_eq_mul, nu2, Measure.infinitePi_pi_univ _ measurableSet_primV]
  congr 1
  exact tprod_congr fun v => haarO_pi_primV v

/-! ### The archimedean fibration measure -/

/-- The archimedean vector $a\in F_\infty^2$ viewed as an adelic vector with finite part $0$. -/
def liftInf (a : Fin 2 → mixedSpace F) : AdeleSpace F (Fin 2) := fun i => (a i, 0)

theorem measurable_liftInf : Measurable (liftInf (F := F)) :=
  measurable_pi_iff.mpr fun i => (measurable_pi_apply i).prodMk measurable_const

/-- **The archimedean coordinates** $\Psi_\infty(a, x) = s_\infty(a)\,n(x)
= \begin{pmatrix} a_0 & a_0x + b_\infty(a)\\ a_1 & a_1x + d_\infty(a)\end{pmatrix}$ (the archimedean section). -/
def psiInf (p : (Fin 2 → mixedSpace F) × mixedSpace F) : Matrix (Fin 2) (Fin 2) (mixedSpace F) :=
  !![p.1 0, p.1 0 * p.2 + secBInf (liftInf p.1); p.1 1, p.1 1 * p.2 + secDInf (liftInf p.1)]

theorem measurable_psiInf : Measurable (psiInf (F := F)) := by
  have hB : Measurable fun p : (Fin 2 → mixedSpace F) × mixedSpace F => secBInf (liftInf p.1) :=
    measurable_secBInf.comp (measurable_liftInf.comp measurable_fst)
  have hD : Measurable fun p : (Fin 2 → mixedSpace F) × mixedSpace F => secDInf (liftInf p.1) :=
    measurable_secDInf.comp (measurable_liftInf.comp measurable_fst)
  have h0 : Measurable fun p : (Fin 2 → mixedSpace F) × mixedSpace F => p.1 0 :=
    (measurable_pi_apply 0).comp measurable_fst
  have h1 : Measurable fun p : (Fin 2 → mixedSpace F) × mixedSpace F => p.1 1 :=
    (measurable_pi_apply 1).comp measurable_fst
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  fin_cases i <;> fin_cases j
  · exact h0
  · exact (h0.mul measurable_snd).add hB
  · exact h1
  · exact (h1.mul measurable_snd).add hD

variable (F) in
/-- The archimedean primitive vectors: $(a_0, a_1)\ne 0$ at every infinite place. -/
def primInf : Set (Fin 2 → mixedSpace F) :=
  {a | (∀ w, (a 0).1 w ≠ 0 ∨ (a 1).1 w ≠ 0) ∧ ∀ w, (a 0).2 w ≠ 0 ∨ (a 1).2 w ≠ 0}

theorem measurableSet_primInf : MeasurableSet (primInf F) := by
  have : primInf F = (⋂ w, {a : Fin 2 → mixedSpace F | (a 0).1 w ≠ 0 ∨ (a 1).1 w ≠ 0}) ∩
      ⋂ w, {a : Fin 2 → mixedSpace F | (a 0).2 w ≠ 0 ∨ (a 1).2 w ≠ 0} := by
    ext a; simp [primInf, Set.mem_iInter]
  rw [this]
  refine MeasurableSet.inter (MeasurableSet.iInter fun w => ?_) (MeasurableSet.iInter fun w => ?_)
  · exact (((measurable_pi_apply w).comp (measurable_fst.comp (measurable_pi_apply 0))) (measurableSet_singleton
      0).compl).union (((measurable_pi_apply w).comp (measurable_fst.comp (measurable_pi_apply 1)))
        (measurableSet_singleton 0).compl)
  · exact (((measurable_pi_apply w).comp (measurable_snd.comp (measurable_pi_apply 0))) (measurableSet_singleton
      0).compl).union (((measurable_pi_apply w).comp (measurable_snd.comp (measurable_pi_apply 1)))
        (measurableSet_singleton 0).compl)

variable (F) in
/-- **The archimedean fibration measure** $\mu_{T,\infty} = \Psi_{\infty*}(dy_\infty|_{P_\infty}\otimes dx_\infty)$ on
$M_2(F_\infty)$ (supported on $\mathrm{SL}_2(F_\infty)$), with $dy_\infty, dx_\infty$ the self-dual measures. -/
def muTInf : Measure (Matrix (Fin 2) (Fin 2) (mixedSpace F)) :=
  (((Measure.pi fun _ : Fin 2 => Analysis.selfDualInf (F := F)).restrict (primInf F)).prod
    (Analysis.selfDualInf (F := F))).map psiInf

/-- The archimedean part of $g\in\mathrm{SL}_2(\mathbb A_F)$. -/
def archPart (g : SL2A F) : Matrix (Fin 2) (Fin 2) (mixedSpace F) :=
  (g : Matrix (Fin 2) (Fin 2) (Adeles F)).map Prod.fst

theorem measurable_archPart : Measurable (archPart (F := F)) :=
  measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => measurable_fst.comp (measurable_SL2A_entry i j)

variable (F) in
/-- The elements of $\mathrm{SL}_2(\mathbb A_F)$ whose finite part lies in $\mathrm{SL}_2(\hat{\mathcal O})$. -/
def intFin : Set (SL2A F) := {g | ∀ i j, ((g : Matrix (Fin 2) (Fin 2) (Adeles F)) i j).2 ∈ OHat}

theorem measurableSet_intFin : MeasurableSet (intFin F) := by
  have : intFin F = ⋂ i, ⋂ j, (fun g : SL2A F => ((g : Matrix (Fin 2) (Fin 2) (Adeles F)) i j).2) ⁻¹' OHat := by
    ext g; simp [intFin, Set.mem_iInter]
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    (measurable_snd.comp (measurable_SL2A_entry i j)) measurableSet_OHat

/-! ### The set identity -/

/-- The finite part of an adelic vector. -/
def finVec (y : AdeleSpace F (Fin 2)) : Fin 2 → AF := fun i => (y i).2

/-- The archimedean part of an adelic vector. -/
def infVec (y : AdeleSpace F (Fin 2)) : Fin 2 → mixedSpace F := fun i => (y i).1

theorem ofCoord_mat {y : AdeleSpace F (Fin 2)} (hy : y ∈ primSet F) (x : Adeles F) :
    (ofCoord F (⟨y, hy⟩, x) : Matrix (Fin 2) (Fin 2) (Adeles F)) =
      !![y 0, y 0 * x + (secBInf y, secBFin y); y 1, y 1 * x + (secDInf y, secDFin y)] := by
  have hsec : ((sec y : SL2A F) : Matrix (Fin 2) (Fin 2) (Adeles F)) = secMat y := by
    simp only [sec, hy, ↓reduceDIte]; rfl
  show ((sec y * nA x : SL2A F) : Matrix (Fin 2) (Fin 2) (Adeles F)) = _
  rw [Matrix.SpecialLinearGroup.coe_mul, hsec]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [secMat, nA, Matrix.mul_apply, Fin.sum_univ_two]

theorem archPart_ofCoord {y : AdeleSpace F (Fin 2)} (hy : y ∈ primSet F) (x : Adeles F) :
    archPart (ofCoord F (⟨y, hy⟩, x)) = psiInf (infVec y, x.1) := by
  rw [archPart, ofCoord_mat hy]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> rfl

/-- If $(a, c)$ is primitive, $b, d$ integral, and $ax + b$, $cx + d$ integral, then $x$ is integral. -/
theorem integral_of_prim {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (w : Valuation K Γ₀)
    {a c b d x : K} (h : IsPrim w a c) (hb : w b ≤ 1) (hd : w d ≤ 1) (h1 : w (a * x + b) ≤ 1)
    (h2 : w (c * x + d) ≤ 1) : w x ≤ 1 := by
  obtain ⟨-, -, hu⟩ := h
  rcases hu with ⟨ha0, hai⟩ | ⟨hc0, hci⟩
  · have : x = a⁻¹ * ((a * x + b) - b) := by field_simp; ring
    rw [this, Valuation.map_mul]
    exact mul_le_one' hai ((Valuation.map_sub _ _ _).trans (max_le h1 hb))
  · have : x = c⁻¹ * ((c * x + d) - d) := by field_simp; ring
    rw [this, Valuation.map_mul]
    exact mul_le_one' hci ((Valuation.map_sub _ _ _).trans (max_le h2 hd))

theorem isPrim_ne_zero {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (w : Valuation K Γ₀)
    {a c : K} (h : IsPrim w a c) : a ≠ 0 ∨ c ≠ 0 := by
  rcases h.2.2 with ⟨ha, -⟩ | ⟨hc, -⟩
  · exact Or.inl ha
  · exact Or.inr hc

/-- **The set identity:** in the coordinates, $g = s(y)n(x)$ lies in $\{g_f\in\mathrm{SL}_2(\hat{\mathcal O}),\
g_\infty\in U\}$ iff $(y_\infty, x_\infty)\in\Psi_\infty^{-1}(U)$, $y_f\in\mathrm{primHat}$ and $x_f\in\hat{\mathcal O}$
(the section is integral at primitive vectors). -/
theorem mem_box_iff (U : Set (Matrix (Fin 2) (Fin 2) (mixedSpace F))) (y : AdeleSpace F (Fin 2)) (x : Adeles F) :
    (∃ hy : y ∈ primSet F, ofCoord F (⟨y, hy⟩, x) ∈ intFin F ∩ archPart ⁻¹' U) ↔
      infVec y ∈ primInf F ∧ psiInf (infVec y, x.1) ∈ U ∧ finVec y ∈ primHat F ∧ x.2 ∈ OHat := by
  constructor
  · rintro ⟨hy, hint, hU⟩
    have hm := ofCoord_mat hy x
    have hdet : (ofCoord F (⟨y, hy⟩, x) : Matrix (Fin 2) (Fin 2) (Adeles F)).det = 1 :=
      (ofCoord F (⟨y, hy⟩, x)).2
    rw [hm, Matrix.det_fin_two_of] at hdet
    have e00 : ∀ v, valV v ((y 0).2 v) ≤ 1 := by
      have := hint 0 0; rw [hm] at this; exact this
    have e01 : ∀ v, valV v ((y 0).2 v * x.2 v + secBFin y v) ≤ 1 := by
      have := hint 0 1; rw [hm] at this; exact this
    have e10 : ∀ v, valV v ((y 1).2 v) ≤ 1 := by
      have := hint 1 0; rw [hm] at this; exact this
    have e11 : ∀ v, valV v ((y 1).2 v * x.2 v + secDFin y v) ≤ 1 := by
      have := hint 1 1; rw [hm] at this; exact this
    have hprim : ∀ v, IsPrim (valV v) ((y 0).2 v) ((y 1).2 v) := fun v =>
      isPrim_of_det (valV v) (e00 v) (e01 v) (e10 v) (e11 v) (congrArg (fun z : Adeles F => z.2 v) hdet)
    refine ⟨⟨hy.1, hy.2.1⟩, ?_, ⟨fun i => ?_, hprim⟩, fun v => ?_⟩
    · rw [← archPart_ofCoord hy x]; exact hU
    · fin_cases i
      · exact e00
      · exact e10
    · have hev : ∀ᶠ v in cofinite, IsPrim (valV v) ((y 0).2 v) ((y 1).2 v) := Filter.Eventually.of_forall hprim
      have hB : valV v (secBFin y v) ≤ 1 := by
        rw [secBFin_apply, if_pos hev]; exact locB_integral (valV v) (hprim v)
      have hD : valV v (secDFin y v) ≤ 1 := by
        rw [secDFin_apply, if_pos hev]; exact locD_integral (valV v) (hprim v)
      exact integral_of_prim (valV v) (hprim v) hB hD (e01 v) (e11 v)
  · rintro ⟨hinf, hU, ⟨hO, hprim⟩, hx⟩
    have hev : ∀ᶠ v in cofinite, IsPrim (valV v) ((y 0).2 v) ((y 1).2 v) := Filter.Eventually.of_forall hprim
    have hy : y ∈ primSet F := ⟨hinf.1, hinf.2, fun v => isPrim_ne_zero (valV v) (hprim v), hev⟩
    refine ⟨hy, ?_, ?_⟩
    · intro i j
      rw [ofCoord_mat hy x]
      have hB : ∀ v, valV v (secBFin y v) ≤ 1 := fun v => by
        rw [secBFin_apply, if_pos hev]; exact locB_integral (valV v) (hprim v)
      have hD : ∀ v, valV v (secDFin y v) ≤ 1 := fun v => by
        rw [secDFin_apply, if_pos hev]; exact locD_integral (valV v) (hprim v)
      fin_cases i <;> fin_cases j
      · exact hO 0
      · intro v
        show valV v ((y 0).2 v * x.2 v + secBFin y v) ≤ 1
        have hmul : valV v ((y 0).2 v * x.2 v) ≤ 1 := by
          rw [Valuation.map_mul]; exact mul_le_one' (hO 0 v) (hx v)
        exact (Valuation.map_add _ _ _).trans (max_le hmul (hB v))
      · exact hO 1
      · intro v
        show valV v ((y 1).2 v * x.2 v + secDFin y v) ≤ 1
        have hmul : valV v ((y 1).2 v * x.2 v) ≤ 1 := by
          rw [Valuation.map_mul]; exact mul_le_one' (hO 1 v) (hx v)
        exact (Valuation.map_add _ _ _).trans (max_le hmul (hD v))
    · show archPart _ ∈ U
      rw [archPart_ofCoord hy x]; exact hU

/-! ### The box computation -/

theorem measurable_infVec : Measurable (infVec (F := F)) :=
  measurable_pi_iff.mpr fun i => measurable_fst.comp (measurable_pi_apply i)

theorem measurable_finVec : Measurable (finVec (F := F)) :=
  measurable_pi_iff.mpr fun i => measurable_snd.comp (measurable_pi_apply i)

theorem measurableSet_primHat : MeasurableSet (primHat F) := by
  rw [primHat_eq_image]
  exact measurableEmbedding_jj.measurableSet_image.2 (MeasurableSet.univ_pi measurableSet_primV)

variable (F) in
/-- The box in the coordinates: $(y_\infty, x_\infty)\in\Psi_\infty^{-1}(U)$ with $y_\infty$ primitive,
$y_f\in\mathrm{primHat}$, $x_f\in\hat{\mathcal O}$. -/
def boxCoord (U : Set (Matrix (Fin 2) (Fin 2) (mixedSpace F))) : Set (AdeleSpace F (Fin 2) × Adeles F) :=
  {p | infVec p.1 ∈ primInf F ∧ psiInf (infVec p.1, p.2.1) ∈ U ∧ finVec p.1 ∈ primHat F ∧ p.2.2 ∈ OHat}

theorem measurableSet_boxCoord {U : Set (Matrix (Fin 2) (Fin 2) (mixedSpace F))} (hU : MeasurableSet U) :
    MeasurableSet (boxCoord F U) := by
  have h1 : Measurable fun p : AdeleSpace F (Fin 2) × Adeles F => psiInf (infVec p.1, p.2.1) :=
    measurable_psiInf.comp ((measurable_infVec.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))
  exact ((measurable_infVec.comp measurable_fst) measurableSet_primInf).inter ((h1 hU).inter
    (((measurable_finVec.comp measurable_fst) measurableSet_primHat).inter
      ((measurable_snd.comp measurable_snd) measurableSet_OHat)))

/-- Step 1: $\mu_T(\text{box}) = (dy\otimes dx)(\text{box in coordinates})$. -/
theorem muT_box_eq_coord {U : Set (Matrix (Fin 2) (Fin 2) (mixedSpace F))} (hU : MeasurableSet U) :
    muT F (intFin F ∩ archPart ⁻¹' U) = ((muAddVec F (Fin 2)).prod (muAdd F)) (boxCoord F U) := by
  have hE : MeasurableSet (intFin F ∩ archPart ⁻¹' U) := measurableSet_intFin.inter (measurable_archPart hU)
  have hS := measurableSet_boxCoord hU
  set G : AdeleSpace F (Fin 2) → ℝ≥0∞ := fun z => muAdd F (Prod.mk z ⁻¹' boxCoord F U)
  have hG : Measurable G := measurable_measure_prodMk_left hS
  have hslice : ∀ y : primSet F, Prod.mk y ⁻¹' (ofCoord F ⁻¹' (intFin F ∩ archPart ⁻¹' U)) =
      Prod.mk (y : AdeleSpace F (Fin 2)) ⁻¹' boxCoord F U := by
    intro y
    ext x
    simp only [Set.mem_preimage]
    have := mem_box_iff U (y : AdeleSpace F (Fin 2)) x
    rw [boxCoord, Set.mem_ofPred_eq, ← this]
    exact ⟨fun h => ⟨y.2, h⟩, fun ⟨_, h⟩ => h⟩
  rw [muT_apply hE, Measure.prod_apply (measurable_ofCoord hE), Measure.prod_apply hS]
  simp_rw [hslice]
  have hmc : (dyP F).map Subtype.val = (muAddVec F (Fin 2)).restrict (primSet F) := by
    rw [dyP, measurableEmbedding_primSet_val.map_comap, Subtype.range_coe]
  calc ∫⁻ y : primSet F, G y ∂dyP F = ∫⁻ z, G z ∂((dyP F).map Subtype.val) :=
        (lintegral_map hG measurable_subtype_coe).symm
    _ = ∫⁻ z in primSet F, G z ∂muAddVec F (Fin 2) := by rw [hmc]
    _ = ∫⁻ z, G z ∂muAddVec F (Fin 2) := by
        refine setLIntegral_eq_of_support_subset fun z hz => ?_
        by_contra hzP
        apply hz
        show muAdd F (Prod.mk z ⁻¹' boxCoord F U) = 0
        have : Prod.mk z ⁻¹' boxCoord F U = ∅ := by
          ext x
          simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
          intro hx
          obtain ⟨hy, -⟩ := (mem_box_iff U z x).2 hx
          exact hzP hy
        rw [this, measure_empty]

/-- Step 2: the coordinate box has measure $\mu_{T,\infty}(U)\cdot\mu_f^{\otimes2}(\mathrm{primHat})\cdot
\mu_f(\hat{\mathcal O})$. -/
theorem measure_boxCoord {U : Set (Matrix (Fin 2) (Fin 2) (mixedSpace F))} (hU : MeasurableSet U) :
    ((muAddVec F (Fin 2)).prod (muAdd F)) (boxCoord F U) =
      muTInf F U * (muFinVec F (Fin 2) (primHat F) * muFin F OHat) := by
  have hS := measurableSet_boxCoord hU
  set A : (Fin 2 → mixedSpace F) → ℝ≥0∞ := (primInf F).indicator fun a =>
    Analysis.selfDualInf (F := F) {t | psiInf (a, t) ∈ U}
  set B : (Fin 2 → AF) → ℝ≥0∞ := (primHat F).indicator fun _ => muFin F OHat
  have hA : Measurable A :=
    (measurable_measure_prodMk_left (measurable_psiInf hU)).indicator measurableSet_primInf
  have hB : Measurable B := measurable_const.indicator measurableSet_primHat
  have hslice : ∀ z, muAdd F (Prod.mk z ⁻¹' boxCoord F U) = A (infVec z) * B (finVec z) := by
    intro z
    by_cases h1 : infVec z ∈ primInf F
    · by_cases h2 : finVec z ∈ primHat F
      · have : Prod.mk z ⁻¹' boxCoord F U = {t | psiInf (infVec z, t) ∈ U} ×ˢ OHat := by
          ext x; simp [boxCoord, h1, h2]
        rw [this, muAdd, Measure.prod_prod]
        simp only [A, B, Set.indicator_of_mem h1, Set.indicator_of_mem h2]
      · have : Prod.mk z ⁻¹' boxCoord F U = ∅ := by ext x; simp [boxCoord, h2]
        rw [this, measure_empty]
        simp only [B, Set.indicator_of_notMem h2, mul_zero]
    · have : Prod.mk z ⁻¹' boxCoord F U = ∅ := by ext x; simp [boxCoord, h1]
      rw [this, measure_empty]
      simp only [A, Set.indicator_of_notMem h1, zero_mul]
  have hmp := measurePreserving_arrowProdEquivProdArrow (mixedSpace F) AF (Fin 2)
    (fun _ => Analysis.selfDualInf (F := F)) (fun _ => muFin F)
  rw [Measure.prod_apply hS]
  simp_rw [hslice]
  have e1 : ∫⁻ z, A (infVec z) * B (finVec z) ∂muAddVec F (Fin 2) =
      ∫⁻ q, A q.1 * B q.2 ∂((Measure.pi fun _ : Fin 2 => Analysis.selfDualInf (F := F)).prod
        (Measure.pi fun _ : Fin 2 => muFin F)) :=
    hmp.lintegral_comp ((hA.comp measurable_fst).mul (hB.comp measurable_snd))
  rw [e1, lintegral_prod_mul hA.aemeasurable hB.aemeasurable]
  congr 1
  · rw [muTInf, Measure.map_apply measurable_psiInf hU, Measure.prod_apply (measurable_psiInf hU),
      lintegral_indicator measurableSet_primInf]
    rfl
  · rw [lintegral_indicator_const measurableSet_primHat, mul_comm]

/-- **The box computation for $\mu_T$** (the gap 1, finite places): for every measurable set $U$ of archimedean
matrices,
$$\mu_T\{g : g_f\in\mathrm{SL}_2(\hat{\mathcal O}),\ g_\infty\in U\} = \mu_{T,\infty}(U)\cdot
\operatorname{vol}(\hat{\mathcal O})^3\cdot\prod_v\big(1 - N(v)^{-2}\big),$$
$\operatorname{vol}(\hat{\mathcal O}) = |d_F|^{-1/2} = \prod_v\operatorname{vol}(\mathcal O_v)$ (`ohatVol_eq_finprod`). With
`selfDualV_primV` this is $\mu_T = \mu_{T,\infty}\otimes\prod_v|\omega|_v$ on $\mathrm{SL}_2(F_\infty)\times
\prod_v\mathrm{SL}_2(\mathcal O_v)$, $|\omega|_v(\mathrm{SL}_2(\mathcal O_v)) = (1 - N(v)^{-2})\operatorname{vol}(\mathcal O_v)^3$
(Weil's normalization, convergence factors $\lambda_v = 1$). -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure as a product of local measures, λ_v = 1) [page checked in the design table]; §2.2, Thm 2.2.5 [unverified page]"]
theorem muT_box {U : Set (Matrix (Fin 2) (Fin 2) (mixedSpace F))} (hU : MeasurableSet U) :
    muT F (intFin F ∩ archPart ⁻¹' U) =
      muTInf F U * (ENNReal.ofReal (ohatVol F) ^ 3 *
        ∏' v : HeightOneSpectrum (𝓞 F), ENNReal.ofReal (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹ ^ 2)) := by
  rw [muT_box_eq_coord hU, measure_boxCoord hU, muFinVec_primHat, muFin_OHat]
  congr 1
  ring

/-! ### The archimedean factor is Weil's gauge-form measure $|da\,db\,dc/a|_\infty$ -/

variable (F) in
/-- The archimedean vectors whose first coordinate is a unit of $F_\infty$. -/
def unitFirst : Set (Fin 2 → mixedSpace F) := {y | (∀ w, (y 0).1 w ≠ 0) ∧ ∀ w, (y 0).2 w ≠ 0}

theorem measurableSet_unitFirst : MeasurableSet (unitFirst F) := by
  have : unitFirst F = (⋂ w, {y : Fin 2 → mixedSpace F | (y 0).1 w ≠ 0}) ∩
      ⋂ w, {y : Fin 2 → mixedSpace F | (y 0).2 w ≠ 0} := by
    ext a; simp [unitFirst, Set.mem_iInter]
  rw [this]
  exact MeasurableSet.inter (MeasurableSet.iInter fun w =>
      ((measurable_pi_apply w).comp (measurable_fst.comp (measurable_pi_apply 0))) (measurableSet_singleton 0).compl)
    (MeasurableSet.iInter fun w =>
      ((measurable_pi_apply w).comp (measurable_snd.comp (measurable_pi_apply 0))) (measurableSet_singleton 0).compl)

theorem unitFirst_subset_primInf : unitFirst F ⊆ primInf F :=
  fun _ hy => ⟨fun w => Or.inl (hy.1 w), fun w => Or.inl (hy.2 w)⟩

theorem pi_selfDualInf_compl_unitFirst :
    (Measure.pi fun _ : Fin 2 => Analysis.selfDualInf (F := F)) (unitFirst F)ᶜ = 0 := by
  have hnull : ∀ Z : Set (mixedSpace F), Analysis.selfDualInf Z = 0 →
      (Measure.pi fun _ : Fin 2 => Analysis.selfDualInf (F := F)) {y | y 0 ∈ Z} = 0 := by
    intro Z hZ
    have : {y : Fin 2 → mixedSpace F | y 0 ∈ Z} = Set.univ.pi (Function.update (fun _ => Set.univ) 0 Z) := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_univ_pi]
      constructor
      · intro h i
        by_cases hi : i = 0
        · subst hi; simpa using h
        · simp [Function.update_of_ne hi]
      · intro h; simpa using h 0
    rw [this, Measure.pi_pi, Fin.prod_univ_two]
    simp [hZ]
  have hsub : (unitFirst F)ᶜ ⊆ (⋃ w, {y : Fin 2 → mixedSpace F | y 0 ∈ {x : mixedSpace F | x.1 w = 0}}) ∪
      ⋃ w, {y : Fin 2 → mixedSpace F | y 0 ∈ {x : mixedSpace F | x.2 w = 0}} := by
    intro y hy
    simp only [unitFirst, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or, not_forall, not_not] at hy
    rcases hy with ⟨w, hw⟩ | ⟨w, hw⟩
    · exact Or.inl (Set.mem_iUnion.2 ⟨w, hw⟩)
    · exact Or.inr (Set.mem_iUnion.2 ⟨w, hw⟩)
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · exact measure_iUnion_null fun w => hnull _ (selfDualInf_real_eq_zero w)
  · exact measure_iUnion_null fun w => hnull _ (selfDualInf_complex_eq_zero w)

/-- $|N(a)|_\infty = |\det(x\mapsto ax)| = \prod_{\text{real}}|a_w|\prod_{\text{complex}}|a_w|^2$
(`det_mulLeft_mixedSpace`). -/
def normInf (a : mixedSpace F) : ℝ≥0∞ := ENNReal.ofReal |LinearMap.det (LinearMap.mulLeft ℝ a)|

theorem measurable_normInf : Measurable (normInf (F := F)) :=
  ENNReal.measurable_ofReal.comp continuous_abs_det_mulLeft.measurable

theorem det_mulLeft_ne_zero {a : mixedSpace F} (h1 : ∀ w, a.1 w ≠ 0) (h2 : ∀ w, a.2 w ≠ 0) :
    LinearMap.det (LinearMap.mulLeft ℝ a) ≠ 0 := by
  rw [det_mulLeft_mixedSpace]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun w _ => h1 w)
    (Finset.prod_ne_zero_iff.2 fun w _ => (Complex.normSq_pos.2 (h2 w)).ne')

/-- **Weil's chart** $(a, c, b)\mapsto\begin{pmatrix} a & b\\ c & (1 + bc)/a\end{pmatrix}$ of $\mathrm{SL}_2$ on
$\{a\ne 0\}$. -/
def gaugeChart (p : (Fin 2 → mixedSpace F) × mixedSpace F) : Matrix (Fin 2) (Fin 2) (mixedSpace F) :=
  !![p.1 0, p.2; p.1 1, (1 + p.1 1 * p.2) * (p.1 0)⁻¹]

theorem measurable_inv_mixedSpace : Measurable fun a : mixedSpace F => a⁻¹ :=
  (measurable_pi_iff.2 fun w => ((measurable_pi_apply w).comp measurable_fst).inv).prodMk
    (measurable_pi_iff.2 fun w => ((measurable_pi_apply w).comp measurable_snd).inv)

theorem measurable_gaugeChart : Measurable (gaugeChart (F := F)) := by
  have h0 : Measurable fun p : (Fin 2 → mixedSpace F) × mixedSpace F => p.1 0 :=
    (measurable_pi_apply 0).comp measurable_fst
  have h1 : Measurable fun p : (Fin 2 → mixedSpace F) × mixedSpace F => p.1 1 :=
    (measurable_pi_apply 1).comp measurable_fst
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  fin_cases i <;> fin_cases j
  · exact h0
  · exact measurable_snd
  · exact h1
  · exact (measurable_const.add (h1.mul measurable_snd)).mul (measurable_inv_mixedSpace.comp h0)

variable (F) in
/-- **Weil's archimedean gauge-form measure** $|\omega|_\infty$ for $\omega = da\wedge db\wedge dc/a$ on
$\mathrm{SL}_2(F_\infty)$ (the Leray form $dX/d\det$), in the chart `gaugeChart`, with the self-dual measures:
$|N(a)|_\infty^{-1}\,da\,dc\,db$ on $\{a\in F_\infty^\times\}$. -/
def muGaugeInf : Measure (Matrix (Fin 2) (Fin 2) (mixedSpace F)) :=
  ((((Measure.pi fun _ : Fin 2 => Analysis.selfDualInf (F := F)).restrict (unitFirst F)).withDensity
    fun y => (normInf (y 0))⁻¹).prod (Analysis.selfDualInf (F := F))).map gaugeChart

theorem psiInf_eq_gaugeChart {y : Fin 2 → mixedSpace F} (hy : y ∈ unitFirst F) (x : mixedSpace F) :
    psiInf (y, x) = gaugeChart (y, y 0 * x + secBInf (liftInf y)) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · rfl
  · show y 1 * x + secDInf (liftInf y) = (1 + y 1 * (y 0 * x + secBInf (liftInf y))) * (y 0)⁻¹
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · show (y 1).1 w * x.1 w + locD ballR ((y 0).1 w) ((y 1).1 w) =
        (1 + (y 1).1 w * ((y 0).1 w * x.1 w + locB ballR ((y 0).1 w) ((y 1).1 w))) * ((y 0).1 w)⁻¹
      have ha := hy.1 w
      have hdet := locB_det zero_mem_ballR (Or.inl ha : (y 0).1 w ≠ 0 ∨ (y 1).1 w ≠ 0)
      rw [eq_mul_inv_iff_mul_eq₀ ha]
      linear_combination hdet
    · show (y 1).2 w * x.2 w + locD ballC ((y 0).2 w) ((y 1).2 w) =
        (1 + (y 1).2 w * ((y 0).2 w * x.2 w + locB ballC ((y 0).2 w) ((y 1).2 w))) * ((y 0).2 w)⁻¹
      have ha := hy.2 w
      have hdet := locB_det zero_mem_ballC (Or.inl ha : (y 0).2 w ≠ 0 ∨ (y 1).2 w ≠ 0)
      rw [eq_mul_inv_iff_mul_eq₀ ha]
      linear_combination hdet

/-- **The archimedean factor of $\mu_T$ is Weil's gauge-form measure:** $\mu_{T,\infty} = |\omega|_\infty$ for
$\omega = da\wedge db\wedge dc/a$ (in the fibre over $y = (a, c)$, $b = ax + b_\infty(y)$ and $db = |N(a)|_\infty\,dx$). -/
@[kb "weil1982" "§2.2 (gauge forms and local measures); §2.4, Thm 2.4.3 [unverified page]"]
theorem muTInf_eq_muGaugeInf : muTInf F = muGaugeInf F := by
  ext U hU
  set μ := Measure.pi fun _ : Fin 2 => Analysis.selfDualInf (F := F)
  have hg : Measurable fun y : Fin 2 → mixedSpace F => (normInf (y 0))⁻¹ :=
    (measurable_normInf.comp (measurable_pi_apply (0 : Fin 2))).inv
  have hh : Measurable fun y : Fin 2 → mixedSpace F =>
      Analysis.selfDualInf (F := F) (Prod.mk y ⁻¹' (gaugeChart ⁻¹' U)) :=
    measurable_measure_prodMk_left (measurable_gaugeChart hU)
  rw [muTInf, muGaugeInf, Measure.map_apply measurable_psiInf hU, Measure.map_apply measurable_gaugeChart hU,
    Measure.prod_apply (measurable_psiInf hU), Measure.prod_apply (measurable_gaugeChart hU),
    lintegral_withDensity_eq_lintegral_mul _ hg hh]
  -- replace `primInf` by the conull subset `unitFirst`
  have hae : primInf F =ᵐ[μ] unitFirst F := by
    refine (ae_eq_set.2 ⟨measure_mono_null (fun y hy => hy.2) pi_selfDualInf_compl_unitFirst, ?_⟩)
    rw [Set.sdiff_eq_empty.2 unitFirst_subset_primInf, measure_empty]
  rw [Measure.restrict_congr_set hae]
  refine setLIntegral_congr_fun measurableSet_unitFirst fun y hy => ?_
  have hdet := det_mulLeft_ne_zero hy.1 hy.2
  have hset : Prod.mk y ⁻¹' (psiInf ⁻¹' U) =
      (LinearMap.mulLeft ℝ (y 0)) ⁻¹' ((· + secBInf (liftInf y)) ⁻¹' (Prod.mk y ⁻¹' (gaugeChart ⁻¹' U))) := by
    ext x
    simp only [Set.mem_preimage, LinearMap.mulLeft_apply]
    rw [psiInf_eq_gaugeChart hy]
  simp only [Pi.mul_apply]
  rw [hset, Measure.addHaar_preimage_linearMap _ hdet, measure_preimage_add_right, normInf, abs_inv,
    ENNReal.ofReal_inv_of_pos (abs_pos.2 hdet)]

/-! ### $\tau(\mathrm{SL}_2) = 1$ for Weil's Tamagawa measure -/

/-- The product of the local volumes at the finite places: $\operatorname{vol}(\hat{\mathcal O})^3\prod_v(1 - N(v)^{-2})$
$= \prod_v|\omega|_v(\mathrm{SL}_2(\mathcal O_v))$. -/
def finFactorSL2 (F : Type) [Field F] [NumberField F] : ℝ≥0∞ :=
  ENNReal.ofReal (ohatVol F) ^ 3 *
    ∏' v : HeightOneSpectrum (𝓞 F), ENNReal.ofReal (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹ ^ 2)

/-- **$\mu_T$ is Weil's product measure** on the charts $U\times\mathrm{SL}_2(\hat{\mathcal O})$:
$\mu_T(\{g_f\in\mathrm{SL}_2(\hat{\mathcal O}),\ g_\infty\in U\}) = |\omega|_\infty(U)\cdot\prod_v|\omega|_v(\mathrm{SL}_2(\mathcal O_v))$
for the gauge form $\omega = da\wedge db\wedge dc/a$ (`muT_box` + `muTInf_eq_muGaugeInf`). -/
@[kb "weil1982" "§2.3, p. 21 (λ_v = 1) [page checked in the design table]; §2.2 [unverified page]"]
theorem muT_box_gauge {U : Set (Matrix (Fin 2) (Fin 2) (mixedSpace F))} (hU : MeasurableSet U) :
    muT F (intFin F ∩ archPart ⁻¹' U) = muGaugeInf F U * finFactorSL2 F := by
  rw [muT_box hU, muTInf_eq_muGaugeInf, finFactorSL2]

variable (F) in
/-- The archimedean condition of `slNbhd`. -/
def slNbhdInf : Set (Matrix (Fin 2) (Fin 2) (mixedSpace F)) :=
  {X | ‖X 0 0 - 1‖ < 1 / 2 ∧ ‖X 0 1‖ < 1 / 4 ∧ ‖X 1 0‖ < 1 / 4 ∧ ‖X 1 1 - 1‖ < 1 / 2}

theorem measurableSet_slNbhdInf : MeasurableSet (slNbhdInf F) := by
  have hc : ∀ i j, Continuous fun X : Matrix (Fin 2) (Fin 2) (mixedSpace F) => X i j :=
    fun i j => (continuous_apply j).comp (continuous_apply i)
  refine (IsOpen.inter ?_ (IsOpen.inter ?_ (IsOpen.inter ?_ ?_))).measurableSet
  · exact isOpen_lt (((hc 0 0).sub continuous_const).norm) continuous_const
  · exact isOpen_lt (hc 0 1).norm continuous_const
  · exact isOpen_lt (hc 1 0).norm continuous_const
  · exact isOpen_lt (((hc 1 1).sub continuous_const).norm) continuous_const

theorem slNbhd_eq : slNbhd F = intFin F ∩ archPart ⁻¹' slNbhdInf F := rfl

/-- **$\tau(\mathrm{SL}_2) = 1$ for Weil's Tamagawa measure.** Every σ-finite left-invariant measure $\mu$ on
$\mathrm{SL}_2(\mathbb A_F)$ that is Weil's product $|\omega|_\infty\otimes\prod_v|\omega|_v$ on the charts
$U\times\mathrm{SL}_2(\hat{\mathcal O})$ (`hbox`; one $U$, namely `slNbhdInf`, suffices) has
$\operatorname{vol}(\mathrm{SL}_2(\mathbb A_F)/\mathrm{SL}_2(F)) = 1$: such a $\mu$ is $\mu_T$, and `tamagawa_SL2`
applies. -/
@[kb "weil1982" "§3.7 (τ(SL₂) = 1); §2.3, p. 21 [unverified page for §3.7]"]
theorem tamagawa_SL2_weil (μ : Measure (SL2A F)) [SigmaFinite μ] [μ.IsMulLeftInvariant]
    (hbox : μ (intFin F ∩ archPart ⁻¹' slNbhdInf F) = muGaugeInf F (slNbhdInf F) * finFactorSL2 F) :
    covolume (SL(2, F)) (SL2A F) μ = 1 := by
  have hs := haar_slNbhd_pos_lt_top (muT F)
  have heq : μ (slNbhd F) = muT F (slNbhd F) := by
    rw [slNbhd_eq, hbox, muT_box_gauge measurableSet_slNbhdInf]
  have hμ : μ = muT F := by
    rw [measure_eq_div_smul μ (muT F) hs.1 hs.2, heq, ENNReal.div_self hs.1 hs.2, one_smul]
  rw [hμ]
  exact tamagawa_SL2

end

end QuadFormsKB.Tamagawa.Measure.Weil
