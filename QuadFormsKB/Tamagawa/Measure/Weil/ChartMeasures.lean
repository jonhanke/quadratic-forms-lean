import QuadFormsKB.Tamagawa.Measure.Weil.QuatTamagawa

/-!
# Chart lemmas without finiteness hypotheses, and as equalities of measures
Instances of the abstract results `ChartData.measure_chartBox_of_measurable` (monotone exhaustion) and
`ChartData.map_restrict_chart_eq_pi` (π-λ, `Measure.pi_eq`) of `ChartAbstract.lean`:

* **Ideles** (`ideleChart F`: projections `unitAt`, sections `mulSingleAt`, standard sets $\mathcal O_v^\times$):
  **`muFinUnits_ideleBox_of_measurable`**: $\mu_f(\prod_{v\in S}U_v\times\prod_{v\notin S}\mathcal O_v^\times) =
  \mu_f(\hat{\mathcal O}^\times)\prod_{v\in S}\omega_v(U_v)/\omega_v(\mathcal O_v^\times)$ for all measurable $U_v$;
  **`map_restrict_idele_eq_pi`**: on $\{g : g_v\in\mathcal O_v^\times\ (v\notin S)\}$, the image of $\mu_f$ under
  $(g_v)_{v\in S}$ is $\mu_f(\hat{\mathcal O}^\times)\bigotimes_{v\in S}\omega_v(\mathcal O_v^\times)^{-1}\omega_v$.
* **Quaternions** ($a, b$ integral, nonzero): **`muFinQuat_quatBox_of_measurable`** and
  **`map_restrict_quat_eq_pi`**, the same with $\Lambda_v^\times$ and $\omega_v = \|\operatorname{nrd}\|_v^{-2}dx_v$.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Quaternion Pointwise Classical

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

set_option synthInstance.maxHeartbeats 400000

/-! ### Ideles -/

/-- $g\mapsto g_v$ as a homomorphism $\mathbb A_f^\times\to F_v^\times$. -/
def unitAtHom (v : HeightOneSpectrum (𝓞 F)) : AFˣ →* (v.adicCompletion F)ˣ where
  toFun g := unitAt g v
  map_one' := unitAt_one v
  map_mul' g h := unitAt_mul g h v

theorem mulSingleAt_mul (w : HeightOneSpectrum (𝓞 F)) (x y : (w.adicCompletion F)ˣ) :
    mulSingleAt w (x * y) = mulSingleAt w x * mulSingleAt w y := by
  refine Units.ext (Subtype.ext (funext fun v => ?_))
  change Pi.mulSingle w ((x * y : (w.adicCompletion F)ˣ) : w.adicCompletion F) v =
    Pi.mulSingle w (x : w.adicCompletion F) v * Pi.mulSingle w (y : w.adicCompletion F) v
  rw [Units.val_mul, Pi.mulSingle_mul]
  rfl

theorem mulSingleAt_one (w : HeightOneSpectrum (𝓞 F)) : mulSingleAt w 1 = 1 := by
  refine Units.ext (Subtype.ext (funext fun v => ?_))
  change Pi.mulSingle w ((1 : (w.adicCompletion F)ˣ) : w.adicCompletion F) v = 1
  rw [Units.val_one, Pi.mulSingle_one]
  rfl

/-- The single-place section $F_w^\times\to\mathbb A_f^\times$ as a homomorphism. -/
def mulSingleAtHom (w : HeightOneSpectrum (𝓞 F)) : (w.adicCompletion F)ˣ →* AFˣ where
  toFun := mulSingleAt w
  map_one' := mulSingleAt_one w
  map_mul' := mulSingleAt_mul w

variable (F) in
/-- **The chart data of $\mathbb A_f^\times$**. -/
def ideleChart : ChartData AFˣ (HeightOneSpectrum (𝓞 F)) fun v => (v.adicCompletion F)ˣ where
  p := unitAtHom
  s := mulSingleAtHom
  K := unitsVSub
  p_s_self w x := unitAt_mulSingleAt w x
  p_s_of_ne _ _ h x := unitAt_mulSingleAt_of_ne h x
  isOpen_K := isOpen_unitsVSub
  one_mem_K := one_mem_unitsVSub

theorem chartBox_ideleChart (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)ˣ) : (ideleChart F).chartBox S U = ideleBox S U :=
  rfl

theorem chartBox_empty_ideleChart :
    (ideleChart F).chartBox ∅ (fun v => (ideleChart F).K v) = (OHatUnits F : Set AFˣ) :=
  ideleBox_empty _

/-- **The chart lemma on $\mathbb A_f^\times$ for arbitrary measurable $U_v$.** -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure ∏_v λ_v^{-1}ω_v on the charts)"]
theorem muFinUnits_ideleBox_of_measurable (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)ˣ) (hU : ∀ v ∈ S, MeasurableSet (U v)) :
    muFinUnits F (ideleBox S U) =
      muFinUnits F (OHatUnits F) * ∏ v ∈ S, omegaV v (U v) / omegaV v (unitsVSub v) := by
  have h0 : muFinUnits F ((ideleChart F).chartBox ∅ fun v => (ideleChart F).K v) ≠ ⊤ := by
    rw [chartBox_empty_ideleChart, muFinUnits_OHatUnits]; exact ENNReal.ofReal_ne_top
  have := (ideleChart F).measure_chartBox_of_measurable (fun v => continuous_unitAt v) (muFinUnits F)
    (fun v => omegaV v) omegaV_unitsVSub_ne_top h0 S U hU
  rw [chartBox_ideleChart, chartBox_empty_ideleChart] at this
  exact this

/-- **The chart lemma on $\mathbb A_f^\times$ as an equality of measures**: on $\{g : g_v\in\mathcal O_v^\times\ (v\notin S)\}$,
$(g_v)_{v\in S}$ pushes $\mu_f$ to $\mu_f(\hat{\mathcal O}^\times)\bigotimes_{v\in S}\omega_v(\mathcal O_v^\times)^{-1}\omega_v$. -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure ∏_v λ_v^{-1}ω_v on the charts)"]
theorem map_restrict_idele_eq_pi (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ((muFinUnits F).restrict {g : AFˣ | ∀ v, v ∉ S → unitAt g v ∈ unitsVSub v}).map
        (fun g (v : S) => unitAt g v) =
      muFinUnits F (OHatUnits F) •
        Measure.pi (fun v : S => ((omegaV v.1 (unitsVSub v.1)).toNNReal)⁻¹ • omegaV v.1) := by
  have hO : muFinUnits F ((ideleChart F).chartBox ∅ fun v => (ideleChart F).K v) = ENNReal.ofReal (ohatVol F) := by
    rw [chartBox_empty_ideleChart, muFinUnits_OHatUnits]
  have := (ideleChart F).map_restrict_chart_eq_pi (fun v => continuous_unitAt v) (muFinUnits F)
    (fun v => omegaV v) omegaV_unitsVSub_ne_top (by rw [hO]; exact ENNReal.ofReal_ne_top)
    (by rw [hO]; exact ENNReal.ofReal_pos.mpr ohatVol_pos |>.ne') S
  rw [chartBox_empty_ideleChart] at this
  exact this

/-! ### Quaternions -/

variable {a b : F}
  (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
  (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1)
  (ha0 : a ≠ 0) (hb0 : b ≠ 0)

include ha hb ha0 hb0 in
/-- **The chart lemma on $(\mathbb H\otimes\mathbb A_f)^\times$ for arbitrary measurable $U_v$.** -/
@[kb "weil1982" "§2.3, p. 21 (the measure ∏_v λ_v^{-1}ω_v on the charts)"]
theorem muFinQuat_quatBox_of_measurable (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (QuatV a b v)ˣ) (hU : ∀ v ∈ S, MeasurableSet (U v)) :
    muFinQuat a b (quatBox a b S U) =
      ENNReal.ofReal (quatHatVol a b) * ∏ v ∈ S, omegaQuatV v a b (U v) / omegaQuatV v a b (lamLocUnits a b v) := by
  have := isHaarMeasure_muFinQuat ha hb ha0 hb0
  have h0 := chartBox_empty_quatChart a b
  have hK : muFinQuat a b ((quatChart a b).chartBox ∅ fun v => (quatChart a b).K v) ≠ ⊤ := by
    rw [h0, muFinQuat_lamHatUnits]; exact ENNReal.ofReal_ne_top
  have := (quatChart a b).measure_chartBox_of_measurable (continuous_unitAtQ a b) (muFinQuat a b)
    (fun v => omegaQuatV v a b) (omegaQuatV_lamLocUnits_ne_top a b) hK S U hU
  rw [quatBox, this, h0, muFinQuat_lamHatUnits]
  rfl

include ha hb ha0 hb0 in
/-- **The chart lemma on $(\mathbb H\otimes\mathbb A_f)^\times$ as an equality of measures**: on
$\{x : x_v\in\Lambda_v^\times\ (v\notin S)\}$, $(x_v)_{v\in S}$ pushes `muFinQuat` to
$\mu(\hat\Lambda^\times)\bigotimes_{v\in S}\omega_v(\Lambda_v^\times)^{-1}\omega_v$. -/
@[kb "weil1982" "§2.3, p. 21 (the measure ∏_v λ_v^{-1}ω_v on the charts)"]
theorem map_restrict_quat_eq_pi (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ((muFinQuat a b).restrict {x : (QuatFin a b)ˣ | ∀ v, v ∉ S → unitAtQ a b v x ∈ lamLocUnits a b v}).map
        (fun x (v : S) => unitAtQ a b v x) =
      ENNReal.ofReal (quatHatVol a b) •
        Measure.pi (fun v : S => ((omegaQuatV v.1 a b (lamLocUnits a b v.1)).toNNReal)⁻¹ • omegaQuatV v.1 a b) := by
  have := isHaarMeasure_muFinQuat ha hb ha0 hb0
  have hO : muFinQuat a b ((quatChart a b).chartBox ∅ fun v => (quatChart a b).K v) =
      ENNReal.ofReal (quatHatVol a b) := by
    rw [chartBox_empty_quatChart, muFinQuat_lamHatUnits]
  have := (quatChart a b).map_restrict_chart_eq_pi (continuous_unitAtQ a b) (muFinQuat a b)
    (fun v => omegaQuatV v a b) (omegaQuatV_lamLocUnits_ne_top a b) (by rw [hO]; exact ENNReal.ofReal_ne_top)
    (by rw [hO]; exact (ENNReal.ofReal_pos.mpr (quatHatVol_pos ha hb ha0 hb0)).ne') S
  rw [hO] at this
  exact this

end

end QuadFormsKB.Tamagawa.Measure.Weil
