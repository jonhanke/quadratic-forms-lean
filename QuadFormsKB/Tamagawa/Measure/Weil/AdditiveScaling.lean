import QuadFormsKB.Tamagawa.Measure.Weil.AdditiveChart
import Mathlib.RingTheory.Complex

/-!
# Scaling of the self-dual measure on $\mathbb A_F$ by ideles

For $g\in\mathbb A_F^\times$ acting on $\mathbb A_F$ by multiplication,
$$g_*\mu = \|g\|_{\mathbb A}^{-1}\,\mu,\qquad \|g\|_{\mathbb A} = |\det(g_\infty\cdot)|\cdot\prod_v\Delta_v(g_v),$$
with $\Delta_v$ the Haar character (modulus) of $F_v^\times$ (`distribHaarChar`; $\Delta_v(\varpi_v) = N(v)^{-1}$ is the library's
`modV_eq`) and $|\det(g_\infty\cdot)| = \prod_{w\text{ real}}|g_w|\prod_{w\text{ complex}}|g_w|^2$ (`det_mulLeft_mixedSpace`).

* `map_smul_eq_distribHaarChar_inv` (generic): $g_*\mu = \Delta_A(g)^{-1}\mu$ for any regular Haar measure on a locally
  compact ring $A$;
* `distribHaarChar_mixedSpace`: $\Delta_\infty(t) = |\det(t\cdot)|$ (`addHaar_image_linearMap`);
* `distribHaarChar_finiteAdeleRing`: $\Delta_f(g) = \prod_v\Delta_v(g_v)$ (the chart lemma `muFin_box` for integral $g$,
  then clearing denominators by an integer);
* **`map_smul_muAdd`**: $g_*\,\mu_{\mathbb A} = \|g\|^{-1}\mu_{\mathbb A}$.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology RestrictedProduct NumberField.mixedEmbedding
open scoped Classical ENNReal NNReal Pointwise

namespace MeasureTheory

/-- For a regular Haar measure $\mu$ on a locally compact topological ring $A$ and $g\in A^\times$,
$g_*\mu = \Delta_A(g)^{-1}\mu$, $\Delta_A$ = `distribHaarChar`. -/
theorem map_smul_eq_distribHaarChar_inv {A : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
    [LocallyCompactSpace A] [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure]
    [μ.Regular] (g : Aˣ) :
    Measure.map (g • ·) μ = (distribHaarChar A g)⁻¹ • μ := by
  ext s hs
  rw [Measure.map_apply (measurable_const_smul g) hs]
  have : (g • ·) ⁻¹' s = g⁻¹ • s := by
    ext x; simp [Set.mem_smul_set_iff_inv_smul_mem]
  rw [this, ← distribHaarChar_mul μ g⁻¹ s, map_inv, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

end MeasureTheory

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### The archimedean factor -/

/-- $\det_{\mathbb R}(t\cdot) = \prod_{w\text{ real}}t_w\prod_{w\text{ complex}}|t_w|^2$ on $F_\infty$. -/
theorem det_mulLeft_mixedSpace (t : mixedSpace F) :
    LinearMap.det (LinearMap.mulLeft ℝ t) = (∏ w, t.1 w) * ∏ w, Complex.normSq (t.2 w) := by
  have h1 : LinearMap.mulLeft ℝ t = LinearMap.prodMap (LinearMap.mulLeft ℝ t.1) (LinearMap.mulLeft ℝ t.2) :=
    LinearMap.ext fun _ => rfl
  have h2 : LinearMap.mulLeft ℝ t.1 =
      LinearMap.pi fun w => (LinearMap.mulLeft ℝ (t.1 w)).comp (LinearMap.proj w) :=
    LinearMap.ext fun _ => rfl
  have h3 : LinearMap.mulLeft ℝ t.2 =
      LinearMap.pi fun w => (LinearMap.mulLeft ℝ (t.2 w)).comp (LinearMap.proj w) :=
    LinearMap.ext fun _ => rfl
  have hc : ∀ z : ℂ, LinearMap.det (LinearMap.mulLeft ℝ z) = Complex.normSq z := fun z => by
    rw [← Algebra.norm_complex_apply, Algebra.norm_apply]; rfl
  rw [h1, LinearMap.det_prodMap, h2, h3, LinearMap.det_pi, LinearMap.det_pi]
  simp_rw [LinearMap.det_mulLeft, hc]

/-- **Archimedean modulus**: $\Delta_\infty(t) = |\det(t\cdot)|$ on $F_\infty$. -/
theorem distribHaarChar_mixedSpace (t : (mixedSpace F)ˣ) :
    (distribHaarChar (mixedSpace F) t : ℝ) = |LinearMap.det (LinearMap.mulLeft ℝ (t : mixedSpace F))| := by
  have : (volume : Measure (mixedSpace F)).Regular :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  set s : Set (mixedSpace F) := Metric.ball 0 1
  have hs0 : (volume : Measure (mixedSpace F)) s ≠ 0 := (Metric.measure_ball_pos _ _ one_pos).ne'
  have hsT : (volume : Measure (mixedSpace F)) s ≠ ⊤ := measure_ball_lt_top.ne
  have himg : t • s = LinearMap.mulLeft ℝ (t : mixedSpace F) '' s := by
    ext x; simp [Set.mem_smul_set, Units.smul_def]
  have := distribHaarChar_eq_of_measure_smul_eq_mul (μ := volume) (g := t) hs0 hsT
    (r := Real.toNNReal |LinearMap.det (LinearMap.mulLeft ℝ (t : mixedSpace F))|) (by
      rw [himg, Measure.addHaar_image_linearMap, ENNReal.ofReal])
  rw [this, Real.coe_toNNReal _ (abs_nonneg _)]

/-! ### The finite factor -/

/-- The $v$-component of a finite idele, as a unit of $F_v$. -/
def unitAt (g : AFˣ) (v : HeightOneSpectrum (𝓞 F)) : (v.adicCompletion F)ˣ where
  val := (g : AF) v
  inv := ((g⁻¹ : AFˣ) : AF) v
  val_inv := congrArg (fun x : AF => x v) g.mul_inv
  inv_val := congrArg (fun x : AF => x v) g.inv_mul

@[simp] theorem unitAt_val (g : AFˣ) (v : HeightOneSpectrum (𝓞 F)) : (unitAt g v : v.adicCompletion F) = (g : AF) v :=
  rfl

theorem unitAt_mul (g h : AFˣ) (v : HeightOneSpectrum (𝓞 F)) : unitAt (g * h) v = unitAt g v * unitAt h v :=
  Units.ext rfl

/-- The local modulus $\Delta_v(g_v)$. -/
def modAt (g : AFˣ) (v : HeightOneSpectrum (𝓞 F)) : ℝ≥0 := distribHaarChar (v.adicCompletion F) (unitAt g v)

instance (v : HeightOneSpectrum (𝓞 F)) : (Analysis.selfDualV v).Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

theorem smul_O_eq_of_mem {v : HeightOneSpectrum (𝓞 F)} (u : (v.adicCompletion F)ˣ)
    (hu : (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F)
    (hu' : ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F) :
    u • (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = v.adicCompletionIntegers F := by
  ext x
  simp only [Set.mem_smul_set, Units.smul_def, SetLike.mem_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact mul_mem hu hy
  · intro hx
    exact ⟨((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x, mul_mem hu' hx, by simp⟩

theorem distribHaarChar_eq_one_of_mem {v : HeightOneSpectrum (𝓞 F)} (u : (v.adicCompletion F)ˣ)
    (hu : (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F)
    (hu' : ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F) :
    distribHaarChar (v.adicCompletion F) u = 1 :=
  distribHaarChar_eq_of_measure_smul_eq_mul (μ := Analysis.selfDualV v) (volO_pos v).ne' (volO_ne_top v)
    (by rw [smul_O_eq_of_mem u hu hu', ENNReal.coe_one, one_mul])

/-- The places where $g_v$ or $g_v^{-1}$ is not integral (a finite set). -/
theorem finite_bad (g : AFˣ) :
    {v | (g : AF) v ∉ v.adicCompletionIntegers F ∨
      ((g⁻¹ : AFˣ) : AF) v ∉ v.adicCompletionIntegers F}.Finite :=
  (show {v | (g : AF) v ∉ v.adicCompletionIntegers F}.Finite from (g : AF).2).union
    (show {v | ((g⁻¹ : AFˣ) : AF) v ∉ v.adicCompletionIntegers F}.Finite from ((g⁻¹ : AFˣ) : AF).2)

theorem modAt_eq_one {g : AFˣ} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ (finite_bad g).toFinset) :
    modAt g v = 1 := by
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_or, not_not] at hv
  exact distribHaarChar_eq_one_of_mem _ hv.1 hv.2

theorem mulSupport_modAt_finite (g : AFˣ) : (Function.mulSupport (modAt g)).Finite :=
  (finite_bad g).subset fun v hv => by
    by_contra h
    exact hv (modAt_eq_one (by simpa using h))

instance : (muFin F).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

theorem muFin_OHat_ne_zero : muFin F OHat ≠ 0 := by
  rw [muFin_OHat]; simpa using ohatVol_pos

theorem muFin_OHat_ne_top : muFin F OHat ≠ ⊤ := by
  rw [muFin_OHat]; exact ENNReal.ofReal_ne_top

/-- $\Delta_f(g) = \prod_v\Delta_v(g_v)$ for an **integral** finite idele $g$ (chart lemma). -/
theorem distribHaarChar_finiteAdeleRing_of_integral (g : AFˣ)
    (hg : ∀ v, (g : AF) v ∈ v.adicCompletionIntegers F) :
    distribHaarChar AF g = ∏ᶠ v, modAt g v := by
  set S := (finite_bad g).toFinset
  set U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F) :=
    fun v => unitAt g v • (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hUm : ∀ v ∈ S, MeasurableSet (U v) := fun v _ => (measurableSet_O v).const_smul _
  have hUO : ∀ v ∈ S, U v ⊆ v.adicCompletionIntegers F := by
    rintro v _ _ ⟨y, hy, rfl⟩; exact mul_mem (hg v) hy
  have hset : g • (OHat : Set AF) = {x | (∀ v ∈ S, x v ∈ U v) ∧ x ∈ OHat} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨fun v _ => ⟨y v, hy v, rfl⟩, fun v => mul_mem (hg v) (hy v)⟩
    · rintro ⟨hS, hO⟩
      refine ⟨((g⁻¹ : AFˣ) : AF) * x, fun v => ?_, by simp⟩
      change ((g⁻¹ : AFˣ) : AF) v * x v ∈ v.adicCompletionIntegers F
      by_cases hv : v ∈ S
      · obtain ⟨z, hz, hzx⟩ := hS v hv
        rw [← hzx]
        change ((g⁻¹ : AFˣ) : AF) v * ((g : AF) v * z) ∈ _
        rw [← mul_assoc]
        have : ((g⁻¹ : AFˣ) : AF) v * (g : AF) v = 1 := congrArg (fun x : AF => x v) g.inv_mul
        rw [this, one_mul]; exact hz
      · simp only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_or, not_not] at hv
        exact mul_mem hv.2 (hO v)
  have hloc : ∀ v, Analysis.selfDualV v (U v) = modAt g v * volO v := fun v =>
    (distribHaarChar_mul (Analysis.selfDualV v) (unitAt g v) _).symm
  refine distribHaarChar_eq_of_measure_smul_eq_mul muFin_OHat_ne_zero muFin_OHat_ne_top ?_
  rw [hset, muFin_box S U hUm hUO, mul_comm]
  congr 1
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) fun v hv => by
    by_contra h; exact hv (modAt_eq_one h)]
  rw [ENNReal.ofNNReal_finsetProd]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [hloc, mul_comm, mul_assoc, ENNReal.mul_inv_cancel (volO_pos v).ne' (volO_ne_top v), mul_one]

/-- A nonzero natural number as a finite idele. -/
def natUnit (d : ℕ) (hd : d ≠ 0) : AFˣ :=
  Units.map (algebraMap F AF).toMonoidHom (Units.mk0 (d : F) (by exact_mod_cast hd))

theorem natUnit_val (d : ℕ) (hd : d ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    ((natUnit d hd : AFˣ) : AF) v = (d : v.adicCompletion F) := by
  change algebraMap F (v.adicCompletion F) (d : F) = _
  simp

theorem natCast_mem_O (d : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    (d : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
  have : (d : v.adicCompletion F) = algebraMap F _ (algebraMap (𝓞 F) F (d : 𝓞 F)) := by simp
  rw [this, HeightOneSpectrum.mem_adicCompletionIntegers, HN.valued_algebraMap]
  exact v.valuation_le_one _

/-- **Finite modulus**: $\Delta_f(g) = \prod_v\Delta_v(g_v)$ for every finite idele $g$. -/
theorem distribHaarChar_finiteAdeleRing (g : AFˣ) : distribHaarChar AF g = ∏ᶠ v, modAt g v := by
  have hfin : {v | (g : AF) v ∉ v.adicCompletionIntegers F}.Finite := (g : AF).2
  obtain ⟨d, hd0, hd⟩ := Analysis.exists_nat_clear hfin.toFinset (fun v => (g : AF) v)
  set u := natUnit (F := F) d hd0
  have hu : ∀ v, ((u : AFˣ) : AF) v ∈ v.adicCompletionIntegers F := fun v => by
    rw [natUnit_val]; exact natCast_mem_O d v
  have hug : ∀ v, ((u * g : AFˣ) : AF) v ∈ v.adicCompletionIntegers F := by
    intro v
    change ((u : AFˣ) : AF) v * (g : AF) v ∈ _
    rw [natUnit_val]
    by_cases hv : v ∈ hfin.toFinset
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hd v hv
    · exact mul_mem (natCast_mem_O d v) (by simpa using hv)
  have h1 := distribHaarChar_finiteAdeleRing_of_integral (u * g) hug
  have h2 := distribHaarChar_finiteAdeleRing_of_integral u hu
  have hmul : ∏ᶠ v, modAt (u * g) v = (∏ᶠ v, modAt u v) * ∏ᶠ v, modAt g v := by
    rw [← finprod_mul_distrib (mulSupport_modAt_finite u) (mulSupport_modAt_finite g)]
    refine finprod_congr fun v => ?_
    rw [modAt, unitAt_mul, map_mul]; rfl
  rw [map_mul, h2, hmul] at h1
  have hpos : (∏ᶠ v, modAt u v) ≠ 0 := by rw [← h2]; exact distribHaarChar_pos.ne'
  exact mul_left_cancel₀ hpos h1

/-! ### The global modulus on $\mathbb A_F$ and on $\mathbb A_F^\iota$ -/

/-- The archimedean component of an idele. -/
def infPart (g : (Adeles F)ˣ) : (mixedSpace F)ˣ := Units.map (MonoidHom.fst _ _) g

/-- The finite component of an idele. -/
def finPart (g : (Adeles F)ˣ) : AFˣ := Units.map (MonoidHom.snd _ _) g

variable (F) in
/-- **The idele norm** $\|g\|_{\mathbb A} = |\det(g_\infty\cdot)|\cdot\prod_v\Delta_v(g_v)$. -/
def ideleNorm (g : (Adeles F)ˣ) : ℝ :=
  |LinearMap.det (LinearMap.mulLeft ℝ ((infPart g : mixedSpace F)))| * ∏ᶠ v, (modAt (finPart g) v : ℝ)

instance : (Analysis.selfDualInf (F := F)).Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

instance : (muAdd F).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

theorem muAdd_fundDom : muAdd F (fundDom F) = 1 := by
  have h := addCovolume_muAdd (F := F)
  rwa [(isAddFundamentalDomain_fundDom (muAdd F)).covolume_eq_volume] at h

theorem smul_prod_eq (g : (Adeles F)ˣ) (A : Set (mixedSpace F)) (B : Set AF) :
    g • (A ×ˢ B) = (infPart g • A) ×ˢ (finPart g • B) := by
  ext ⟨x, y⟩
  simp only [Set.mem_smul_set, Set.mem_prod]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, h⟩
    have h' := Prod.ext_iff.mp h
    exact ⟨⟨a, ha, h'.1⟩, ⟨b, hb, h'.2⟩⟩
  · rintro ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩
    exact ⟨(a, b), ⟨ha, hb⟩, Prod.ext h1 h2⟩

/-- **The modulus of $\mathbb A_F$**: $\Delta_{\mathbb A}(g) = \|g\|_{\mathbb A}$. -/
theorem distribHaarChar_adeles (g : (Adeles F)ˣ) : (distribHaarChar (Adeles F) g : ℝ) = ideleNorm F g := by
  have h0 : muAdd F (fundDom F) ≠ 0 := by rw [muAdd_fundDom]; exact one_ne_zero
  have hT : muAdd F (fundDom F) ≠ ⊤ := by rw [muAdd_fundDom]; exact ENNReal.one_ne_top
  set r : ℝ≥0 := distribHaarChar (mixedSpace F) (infPart g) * distribHaarChar AF (finPart g)
  have hr := distribHaarChar_eq_of_measure_smul_eq_mul (μ := muAdd F) (g := g) h0 hT (r := r) (by
    rw [fundDom, smul_prod_eq, muAdd, Measure.prod_prod, Measure.prod_prod,
      ← distribHaarChar_mul Analysis.selfDualInf, ← distribHaarChar_mul (muFin F), ENNReal.coe_mul]
    ring)
  rw [hr, NNReal.coe_mul, distribHaarChar_mixedSpace, distribHaarChar_finiteAdeleRing, ideleNorm]
  congr 1
  exact MonoidHom.map_finprod NNReal.toRealHom.toMonoidHom (mulSupport_modAt_finite _)

theorem ideleNorm_pos (g : (Adeles F)ˣ) : 0 < ideleNorm F g := by
  rw [← distribHaarChar_adeles]; exact_mod_cast distribHaarChar_pos

/-- **Scaling ($A = F$)**: for $g\in\mathbb A_F^\times$, $g_*\mu_{\mathbb A} = \|g\|_{\mathbb A}^{-1}\mu_{\mathbb A}$. -/
@[kb "weil1982" "§2.1 [unverified page]"]
theorem map_smul_muAdd (g : (Adeles F)ˣ) :
    Measure.map (g • ·) (muAdd F) = ENNReal.ofReal (ideleNorm F g)⁻¹ • muAdd F := by
  rw [map_smul_eq_distribHaarChar_inv, ← distribHaarChar_adeles]
  rw [show ((distribHaarChar (Adeles F) g)⁻¹ : ℝ≥0) • muAdd F =
    (((distribHaarChar (Adeles F) g)⁻¹ : ℝ≥0) : ℝ≥0∞) • muAdd F from rfl]
  congr 1
  rw [← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]

section Vec

set_option synthInstance.maxHeartbeats 200000

variable {ι : Type} [Fintype ι]

/-- The norm $N_{A/F}(g) = \prod_i g_i$ of $g\in(F^\iota\otimes\mathbb A)^\times$, through the idele norm:
$\|N(g)\| = \prod_i\|g_i\|_{\mathbb A}$. -/
def ideleNormVec (g : (AdeleSpace F ι)ˣ) : ℝ := ∏ i, ideleNorm F (Units.map (Pi.evalMonoidHom _ i) g)

instance : (muAddVec F ι).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

theorem muAddVec_fundDomVec : muAddVec F ι (fundDomVec F ι) = 1 := by
  have h := addCovolume_muAddVec (F := F) (ι := ι)
  rwa [(isAddFundamentalDomain_fundDomVec (muAddVec F ι)).covolume_eq_volume] at h

theorem distribHaarChar_adeleSpace (g : (AdeleSpace F ι)ˣ) :
    (distribHaarChar (AdeleSpace F ι) g : ℝ) = ideleNormVec g := by
  have h0 : muAddVec F ι (fundDomVec F ι) ≠ 0 := by rw [muAddVec_fundDomVec]; exact one_ne_zero
  have hT : muAddVec F ι (fundDomVec F ι) ≠ ⊤ := by rw [muAddVec_fundDomVec]; exact ENNReal.one_ne_top
  set gi : ι → (Adeles F)ˣ := fun i => Units.map (Pi.evalMonoidHom _ i) g
  have hset : g • fundDomVec F ι = Set.univ.pi fun i => gi i • fundDom F := by
    ext x
    simp only [fundDomVec, Set.mem_smul_set, Set.mem_univ_pi, Units.smul_def]
    constructor
    · rintro ⟨y, hy, rfl⟩ i
      exact ⟨y i, hy i, rfl⟩
    · intro h
      choose y hy hyx using h
      exact ⟨y, hy, funext fun i => hyx i⟩
  have hr := distribHaarChar_eq_of_measure_smul_eq_mul (μ := muAddVec F ι) (g := g) h0 hT
    (r := ∏ i, distribHaarChar (Adeles F) (gi i)) (by
      rw [hset, muAddVec, Measure.pi_pi]
      simp_rw [← distribHaarChar_mul (muAdd F), muAdd_fundDom]
      rw [fundDomVec, Measure.pi_pi]
      simp [muAdd_fundDom])
  rw [hr, NNReal.coe_prod, ideleNormVec]
  exact Finset.prod_congr rfl fun i _ => distribHaarChar_adeles (gi i)

theorem ideleNormVec_pos (g : (AdeleSpace F ι)ˣ) : 0 < ideleNormVec g := by
  rw [← distribHaarChar_adeleSpace]; exact_mod_cast distribHaarChar_pos

/-- **Scaling ($A = F^\iota$)**: $g_*\mu = \|N_{A/F}(g)\|_{\mathbb A}^{-1}\mu$. -/
theorem map_smul_muAddVec (g : (AdeleSpace F ι)ˣ) :
    Measure.map (g • ·) (muAddVec F ι) = ENNReal.ofReal (ideleNormVec g)⁻¹ • muAddVec F ι := by
  rw [map_smul_eq_distribHaarChar_inv, ← distribHaarChar_adeleSpace]
  rw [show ((distribHaarChar (AdeleSpace F ι) g)⁻¹ : ℝ≥0) • muAddVec F ι =
    (((distribHaarChar (AdeleSpace F ι) g)⁻¹ : ℝ≥0) : ℝ≥0∞) • muAddVec F ι from rfl]
  congr 1
  rw [← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]

end Vec

end

end QuadFormsKB.Tamagawa.Measure.Weil
