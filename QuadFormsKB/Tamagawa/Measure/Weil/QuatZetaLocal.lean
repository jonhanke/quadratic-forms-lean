import QuadFormsKB.Tamagawa.Measure.Weil.QuatVolumeConstant
import QuadFormsKB.Tamagawa.ZetaResidue
import QuadFormsKB.Tamagawa.QuaternionZeta
import QuadFormsKB.Weil.ProductFormulas

/-!
# The local zeta integrals of $\mathbb H[F,a,b]$ at the finite places

Weil's multiplicative calculation (AAG §3.1, pp. 36–38) for $A = \mathbb H[F,a,b]$, $a, b\in\mathcal O_F\setminus0$, one finite
place at a time. $\omega_v = \|\operatorname{nrd}x\|_v^{-2}dx_v$ (`omegaQuatV`, $dx_v$ the self-dual coordinate measure) and
$\Lambda_v = \mathcal O_v\langle1,i,j,k\rangle$ (`lamLoc`).

* `lintegral_fin_nat_prod_eq_prod`, `lintegral_fintype_prod_eq_prod` (generic, Mathlib-only; upstreamable): Tonelli for
  a product of functions of separate coordinates over `Measure.pi` (Mathlib v4.35 has only the Bochner version
  `integral_fintype_prod_eq_prod`).
* **`quatLocalZeta v a b s`** $=\int_{(\mathbb H\otimes F_v)^\times}\mathbf 1_{\Lambda_v}(x)\,\|\operatorname{nrd}x\|_v^s\,\omega_v(x)$, and
  **`quatLocalZeta_eq`**: for $s > 2$ it is the self-dual local zeta function of the norm form
  $\langle1,-a,-b,ab\rangle$ (`QuatZeta.normForm`) at $s - 2$:
  $$\int\mathbf 1_{\Lambda_v}\|\operatorname{nrd}x\|_v^s\,\omega_v = \int_{\mathcal O_v^4}|Q(c)|_v^{s-2}\,dc^{\mathrm{sd}} = Z_v^{\mathrm{sd}}(s-2)$$
  (`LocalZeta.zetaInt v (selfDualV v) (NF.Qp v (normForm a b))`), the local factor.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology Set NumberField.mixedEmbedding
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

/-! ### Tonelli for finite products of one-variable functions -/

section Fubini

set_option backward.isDefEq.respectTransparency false in
/-- **Tonelli in $n$ variables for products** (lintegral version of Mathlib's `integral_fin_nat_prod_eq_prod`). -/
theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      calc
        _ = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin n, ∫⁻ (x : E (Fin.succ i)), f (Fin.succ i) x ∂(μ i.succ) := by
          rw [← n_ih (fun i => f i.succ) (fun i => hf i.succ), ← lintegral_prod_mul (hf 0).aemeasurable]
          exact (Finset.measurable_prod _ fun i _ => (hf i.succ).comp (measurable_pi_apply i)).aemeasurable
        _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

/-- **Tonelli for products, any finite index type.** -/
theorem lintegral_fintype_prod_eq_prod {ι : Type*} [Fintype ι] {E : ι → Type*} (f : (i : ι) → E i → ℝ≥0∞)
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_nat_prod_eq_prod (fun i => f (e i)) (fun i => hf (e i))

end Fubini

variable {F : Type} [Field F] [NumberField F]

set_option synthInstance.maxHeartbeats 400000

/-! ### The local zeta integral -/

section Local

variable (v : HeightOneSpectrum (𝓞 F)) (a b : F)

local notation "Kv" => v.adicCompletion F

/-- **The local zeta integral of $\mathbb H$ at $v$** for $\Phi_v = \mathbf 1_{\Lambda_v}$:
$Z_v(s) = \int_{(\mathbb H\otimes F_v)^\times}\mathbf 1_{\Lambda_v}(x)\,\|\operatorname{nrd}x\|_v^s\,\omega_v(x)$. -/
@[kb "weil1982" "§3.1, the local factors of the multiplicative calculation, pp. 36-38"]
def quatLocalZeta (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, (lamLoc a b v).indicator (fun _ => (1 : ℝ≥0∞)) (u : QuatV a b v) *
    ENNReal.ofReal ‖nrdLoc _ _ (u : QuatV a b v)‖ ^ s ∂omegaQuatV v a b

theorem distribHaarChar_adic_eq_norm (u : (Kv)ˣ) : (distribHaarChar Kv u : ℝ) = ‖(u : Kv)‖ := by
  have h := QuadFormsKB.WeilRep.modK_eq_norm v (Units.ne_zero u)
  rw [Analysis.Weil.modK_of_ne (Units.ne_zero u), Units.mk0_val] at h
  exact h

theorem measurable_nrdLoc_norm : Measurable fun x : QuatV a b v => ‖nrdLoc _ _ x‖ :=
  (continuous_norm.comp (continuous_nrdLoc _ _)).measurable

theorem measurableSet_lamLoc : MeasurableSet (lamLoc a b v) := (isOpen_lamLoc a b v).measurableSet

/-- The integrand of `quatLocalZeta`, rewritten on the additive group: for $s > 2$ and every $x\in\mathbb H_v$,
$\|\operatorname{nrd}x\|^{-2}\cdot\mathbf 1_{\Lambda_v}(x)\|\operatorname{nrd}x\|^s = \mathbf 1_{\Lambda_v}(x)\|\operatorname{nrd}x\|^{s-2}$
(both sides vanish when $\operatorname{nrd}x = 0$). -/
theorem inv_sq_mul_eq {t : ℝ} (ht : 0 ≤ t) {s : ℝ} (hs : 2 < s) (c : ℝ≥0∞) :
    (ENNReal.ofReal t ^ 2)⁻¹ * (c * ENNReal.ofReal t ^ s) = c * ENNReal.ofReal (t ^ (s - 2)) := by
  rcases ht.eq_or_lt with rfl | ht0
  · rw [ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos (by linarith), mul_zero, mul_zero,
      Real.zero_rpow (by linarith), ENNReal.ofReal_zero, mul_zero]
  · rw [ENNReal.ofReal_rpow_of_pos ht0, ← ENNReal.ofReal_pow ht0.le, ← ENNReal.ofReal_inv_of_pos (by positivity),
      mul_left_comm, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [Real.rpow_sub ht0, Real.rpow_two, div_eq_inv_mul]

/-- **The local zeta integral in coordinates**: for $s > 2$,
$Z_v(s) = \int_{\mathcal O_v^4}\|\operatorname{nrd}(c)\|_v^{s-2}\,dc$ for the self-dual coordinate measure. -/
theorem quatLocalZeta_eq_coord {s : ℝ} (hs : 2 < s) :
    quatLocalZeta v a b s = ∫⁻ c, (LocalZeta.latL v 4).indicator (fun c => ENNReal.ofReal
      (‖nrdForm (algebraMap F Kv a) (algebraMap F Kv b) c‖ ^ (s - 2))) c
        ∂(Measure.pi fun _ : Fin 4 => Analysis.selfDualV v) := by
  set ν := quatLocVol (algebraMap F Kv a) (algebraMap F Kv b) (Analysis.selfDualV v)
  set G : QuatV a b v → ℝ≥0∞ := fun x => (lamLoc a b v).indicator (fun _ => (1 : ℝ≥0∞)) x *
    ENNReal.ofReal (‖nrdLoc _ _ x‖ ^ (s - 2)) with hG
  have hGm : Measurable G :=
    (measurable_const.indicator (measurableSet_lamLoc v a b)).mul
      (ENNReal.measurable_ofReal.comp ((measurable_nrdLoc_norm v a b).pow_const _))
  have hval := isOpenEmbedding_val_quatLoc (algebraMap F Kv a) (algebraMap F Kv b)
  have he := hval.measurableEmbedding
  -- Step 1: the density form of ω_v.
  have h1 : quatLocalZeta v a b s = ∫⁻ u : (QuatV a b v)ˣ, G u ∂(ν.comap Units.val) := by
    rw [quatLocalZeta, omegaQuatV, omegaQuatLoc_eq, lintegral_withDensity_eq_lintegral_mul]
    · refine lintegral_congr fun u => ?_
      simp only [Pi.mul_apply, hG]
      rw [show ((distribHaarChar Kv (nrdLocUnit _ _ u) : ℝ≥0∞)) = ENNReal.ofReal ‖nrdLoc _ _ (u : QuatV a b v)‖ by
        rw [← ENNReal.ofReal_coe_nnreal, distribHaarChar_adic_eq_norm, nrdLocUnit_val]]
      exact inv_sq_mul_eq (norm_nonneg _) hs _
    · exact ((ENNReal.continuous_coe.comp ((continuous_distribHaarChar_adic v).comp
        (continuous_nrdLocUnit _ _))).measurable.pow_const 2).inv
    · exact (((measurable_const.indicator (measurableSet_lamLoc v a b)).comp Units.continuous_val.measurable).mul
        (((ENNReal.measurable_ofReal.comp (measurable_nrdLoc_norm v a b)).pow_const s).comp
          Units.continuous_val.measurable))
  -- Step 2: from the units to the whole algebra (G vanishes off the units).
  have h2 : ∫⁻ u : (QuatV a b v)ˣ, G u ∂(ν.comap Units.val) = ∫⁻ x, G x ∂ν := by
    rw [← lintegral_map hGm Units.continuous_val.measurable, he.map_comap]
    refine setLIntegral_eq_of_support_subset fun x hx => ?_
    by_contra hxr
    apply hx
    have h0 : nrdLoc _ _ x = 0 := by
      by_contra hn
      exact hxr ⟨((isUnit_iff_nrdLoc_ne_zero _ _ x).mpr hn).unit, rfl⟩
    simp only [hG, h0, norm_zero, Real.zero_rpow (show s - 2 ≠ 0 by linarith), ENNReal.ofReal_zero, mul_zero]
  -- Step 3: transport to coordinates.
  rw [h1, h2]
  change ∫⁻ x, G x ∂((Measure.pi fun _ : Fin 4 => Analysis.selfDualV v).map
    (quatLocCLE (algebraMap F Kv a) (algebraMap F Kv b)).symm) = _
  rw [lintegral_map hGm (quatLocCLE _ _).symm.continuous.measurable]
  refine lintegral_congr fun c => ?_
  simp only [hG]
  have hc : quatLocCoord _ _ ((quatLocCLE (algebraMap F Kv a) (algebraMap F Kv b)).symm c) = c :=
    (quatLocCLE _ _).apply_symm_apply c
  rw [nrdLoc_eq_nrdForm, show quatLocCoord _ _ ((quatLocCLE (algebraMap F Kv a) (algebraMap F Kv b)).symm c) = c
    from hc]
  by_cases hmem : c ∈ LocalZeta.latL v 4
  · rw [indicator_of_mem hmem, indicator_of_mem, one_mul]
    rw [lamLoc_eq, mem_preimage]
    rw [hc]
    exact fun i _ => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hmem i)
  · rw [indicator_of_notMem hmem, indicator_of_notMem, zero_mul]
    rw [lamLoc_eq, mem_preimage]
    rw [hc]
    exact fun h => hmem fun i => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h i (mem_univ _))

/-- The norm form $\langle1,-a,-b,ab\rangle$ of $\Lambda$ over $\mathcal O_v$ evaluates to $c_0^2 - ac_1^2 - bc_2^2 + abc_3^2$. -/
theorem evalIn_Qp_normForm (a b : 𝓞 F) (c : Fin 4 → Kv) :
    (LocalDensity.NF.Qp v (QuatZeta.normForm a b)).evalIn Kv c =
      nrdForm (algebraMap F Kv (a : F)) (algebraMap F Kv (b : F)) c := by
  have h1 : (LocalDensity.NF.Qp v (QuatZeta.normForm a b)).evalIn Kv c =
      ((QuatZeta.normForm a b).map (algebraMap (𝓞 F) F)).evalIn Kv c := by
    simp only [QuadForm.evalIn, LocalDensity.NF.Qp, QuadForm.map, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 2
  rw [h1, QuatZeta.map_normForm]
  simp [QuadForm.evalIn, Quat.nrdForm, QuadForm.diag, Fin.sum_univ_four, nrdForm, Matrix.diagonal]
  ring

/-- **The local zeta integral of $\mathbb H$ is the local zeta function of the norm form**: for $s > 2$,
$Z_v(s) = Z_v^{\mathrm{sd}}(s-2) = \int_{\mathcal O_v^4}|Q(c)|_v^{s-2}\,dc^{\mathrm{sd}}$, $Q = \langle1,-a,-b,ab\rangle$. -/
@[kb "weil1982" "§3.1, the local factors of the multiplicative calculation, pp. 36-38; §4.3, (2), p. 89"]
theorem quatLocalZeta_eq (a b : 𝓞 F) {s : ℝ} (hs : 2 < s) :
    quatLocalZeta v (a : F) (b : F) s =
      ENNReal.ofReal (LocalZeta.zetaInt v (Analysis.selfDualV v) (LocalDensity.NF.Qp v (QuatZeta.normForm a b))
        (s - 2)) := by
  rw [quatLocalZeta_eq_coord v _ _ hs, LocalZeta.zetaInt]
  set π := Measure.pi fun _ : Fin 4 => Analysis.selfDualV v
  have hL : MeasurableSet (LocalZeta.latL v 4) := by
    have : LocalZeta.latL v 4 = Set.pi univ fun _ => (v.adicCompletionIntegers F : Set Kv) := by
      ext c; simp [LocalZeta.latL, HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [this]; exact MeasurableSet.univ_pi fun _ => (isOpen_adicCompletionIntegers v).measurableSet
  have hcont : Continuous fun c : Fin 4 → Kv => ‖nrdForm (algebraMap F Kv (a : F)) (algebraMap F Kv (b : F)) c‖ := by
    unfold nrdForm; fun_prop
  have hbd : ∀ c ∈ LocalZeta.latL v 4,
      ‖nrdForm (algebraMap F Kv (a : F)) (algebraMap F Kv (b : F)) c‖ ^ (s - 2) ≤ 1 := by
    intro c hc
    refine Real.rpow_le_one (norm_nonneg _) ?_ (by linarith)
    refine LocalZeta.norm_le_one_of_valued v ?_
    have hmem : ∀ i, c i ∈ v.adicCompletionIntegers F := fun i =>
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hc i)
    have ha' : algebraMap F Kv (a : F) ∈ v.adicCompletionIntegers F := by
      rw [show algebraMap F Kv (a : F) = algebraMap (𝓞 F) Kv a from (IsScalarTower.algebraMap_apply _ _ _ _).symm]
      exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v a
    have hb' : algebraMap F Kv (b : F) ∈ v.adicCompletionIntegers F := by
      rw [show algebraMap F Kv (b : F) = algebraMap (𝓞 F) Kv b from (IsScalarTower.algebraMap_apply _ _ _ _).symm]
      exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v b
    have : nrdForm (algebraMap F Kv (a : F)) (algebraMap F Kv (b : F)) c ∈ v.adicCompletionIntegers F := by
      unfold nrdForm
      have := v.adicCompletionIntegers F
      exact Subring.add_mem _ (Subring.sub_mem _ (Subring.sub_mem _ (Subring.pow_mem _ (hmem 0) _)
        (Subring.mul_mem _ ha' (Subring.pow_mem _ (hmem 1) _)))
        (Subring.mul_mem _ hb' (Subring.pow_mem _ (hmem 2) _)))
        (Subring.mul_mem _ (Subring.mul_mem _ ha' hb') (Subring.pow_mem _ (hmem 3) _))
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp this
  have hfin : π (LocalZeta.latL v 4) < ⊤ := by
    have : LocalZeta.latL v 4 = Set.pi univ fun _ => (v.adicCompletionIntegers F : Set Kv) := by
      ext c; simp [LocalZeta.latL, HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [this]
    exact (isCompact_univ_pi fun _ => isCompact_adicCompletionIntegers v).measure_lt_top
  have hint : IntegrableOn (fun c : Fin 4 → Kv =>
      ‖nrdForm (algebraMap F Kv (a : F)) (algebraMap F Kv (b : F)) c‖ ^ (s - 2)) (LocalZeta.latL v 4) π := by
    refine Measure.integrableOn_of_bounded (M := 1) hfin.ne ?_ ?_
    · exact ((hcont.measurable.pow_const _)).aestronglyMeasurable
    · refine (ae_restrict_iff' hL).mpr (Eventually.of_forall fun c hc => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact hbd c hc
  simp_rw [evalIn_Qp_normForm]
  rw [lintegral_indicator hL, ← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun c => Real.rpow_nonneg (norm_nonneg _) _)]

end Local

end

end QuadFormsKB.Tamagawa.Measure.Weil
