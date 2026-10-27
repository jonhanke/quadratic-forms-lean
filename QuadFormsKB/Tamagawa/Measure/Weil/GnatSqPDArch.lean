/-
# The test set $H$ and the centre fibre, every number field

**Layer:** $F$ an arbitrary number field (no total reality), $a, b\in\mathcal O_F\setminus0$, $S$ a finite set of finite
places, $m_v\ge1$ levels as in `GnatSqImage.lean`.

* `Hset`: for $W\subseteq G_\infty = \prod_wSO(Q^w)(F_w)$, the set of $\beta\in(D\otimes\mathbb A)^\times$ whose archimedean
  component conjugates into $W$ and whose finite component lies in $\hat\Lambda^\times$ with level structure at $S$.
* **`muPD_pdMk_Hset`**: $\mu_{PD}(\operatorname{pd}(\mathrm{Hset}(W))) =
  \mu^{\mathrm{Tam}}_\infty(W)\cdot\mu_f(\mathrm{box})$, for every number field and every measurable $W$. The proof
  transports $\mu_{PD}$ to $PD^\times(F_\infty)\times PD^\times(\mathbb A_f)$ (`muPD_map_pdSplit`) where it is the product
  $K_\infty^{-1}(\nu_\infty\times\mu_{PD,f})$, and $K_\infty = r_f$ (`rF_toReal_eq_kInf`) cancels the constant of `muPDFin`.
* **`tamIdeles_center_fibre`**: for $\beta\in\mathrm{Hset}(W)$ the centre fibre
  $\mathrm{tamIdeles}\{u : \beta u\in\mathrm{Hset}(W),\ u^2\operatorname{nrd}(\beta)\in B'\}$ equals
  $\omega_\infty(V_1)\,\mu_f(\hat{\mathcal O}^\times)$, with $B'$, $V_1$ the shells with $|x_w|\in(1,4)$, $(1,2)$
  at every place; it is independent of $\beta$ and $W$. The square root of $\operatorname{nrd}(\beta)_\infty$ is a
  translation of the Haar measure $\omega_\infty$ (real or complex scalar $\sqrt{|t_w|}$ at each place).
* `omegaInf_Vone_ne_zero`, `omegaInf_Vone_ne_top`, `measurableSet_Bset'`.

Source: Weil 1982, §3.7(a), p. 63 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqPD
import QuadFormsKB.Tamagawa.Measure.Weil.PDArchRatio
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqCombine
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqShell

open Matrix NumberField NumberField.InfinitePlace NumberField.mixedEmbedding IsDedekindDomain WithZero MeasureTheory Set Filter Function
open scoped ENNReal Quaternion

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices LerayPadic

variable {F : Type} [Field F] [NumberField F] (a b : 𝓞 F)

/-! ### The test set -/

section Hset

variable (S : Finset (HeightOneSpectrum (𝓞 F))) (m : HeightOneSpectrum (𝓞 F) → ℕ) (hm1 : ∀ v, 1 ≤ m v)

/-- **The test set** $H(W) = \{\beta\in(D\otimes\mathbb A)^\times : c_\infty(\beta_\infty)\in W,\ \beta_f\in
\hat\Lambda^\times\text{ with level }m_v\text{ at }v\in S\}$ for $W\subseteq G_\infty$, where $c_\infty$ is
the conjugation `conjInf` onto $G_\infty=\prod_wSO(Q^w)(F_w)$. -/
def Hset (W : Set (GInfSO (QuatZeta.pureFormO a b))) : Set (QuatAdele (a : F) (b : F))ˣ :=
  {β | conjInf a b ((quatUnitsEquiv (a : F) (b : F) β).1) ∈ W ∧ quatFinPart a b β ∈ quatCongS a b S m hm1}

theorem isOpen_Hset {W : Set (GInfSO (QuatZeta.pureFormO a b))} (hW : IsOpen W) :
    IsOpen (Hset a b S m hm1 W) := by
  have h1 : Continuous fun β : (QuatAdele (a : F) (b : F))ˣ => conjInf a b ((quatUnitsEquiv (a : F) (b : F) β).1) :=
    (continuous_conjInf a b).comp (continuous_fst.comp (quatUnitsEquiv (a : F) (b : F)).continuous)
  exact (hW.preimage h1).inter ((isOpen_quatCongS S m hm1).preimage (continuous_quatFinPart a b))

theorem measurableSet_Hset {W : Set (GInfSO (QuatZeta.pureFormO a b))} (hW : MeasurableSet W) :
    MeasurableSet (Hset a b S m hm1 W) := by
  have h1 : Continuous fun β : (QuatAdele (a : F) (b : F))ˣ => conjInf a b ((quatUnitsEquiv (a : F) (b : F) β).1) :=
    (continuous_conjInf a b).comp (continuous_fst.comp (quatUnitsEquiv (a : F) (b : F)).continuous)
  exact (hW.preimage h1.measurable).inter
    ((isOpen_quatCongS S m hm1).preimage (continuous_quatFinPart a b)).measurableSet

/-- **Weil's measure of the test set**, every number field:
$\mu_{PD}(\operatorname{pd}(H(W))) = \mu^{\mathrm{Tam}}_\infty(W)\cdot\mu_f(\mathrm{box})$. -/
@[kb "weil1982" "Thm 3.2.1, p. 43; §3.7(a), p. 63 [unverified page]"]
theorem muPD_pdMk_Hset (ha : a ≠ 0) (hb : b ≠ 0)
    (hS : ∀ v ∉ S, Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1)
    (hmS : ∀ v ∈ S, 2 * sExp v < m v ∧ sExp v + eExp a ha v ≤ m v)
    {W : Set (GInfSO (QuatZeta.pureFormO a b))} (hW : MeasurableSet W) :
    muPD (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha) (by simpa using hb)
        (pdMk (a : F) (b : F) '' Hset a b S m hm1 W) =
      muArchTamSO (QuatZeta.pureFormO a b) (nondegenerate_pureFormO a b ha hb) W *
        QuadFormsKB.Tamagawa.Measure.muFin (QuatZeta.pureFormO a b) (fun _ => 1)
          (QuadFormsKB.Tamagawa.Measure.boxSO (QuatZeta.pureFormO a b) S (congSO3S m hm1)) := by
  set Winf : Set (PDInf a b) := pdInfEquiv a b ha hb ⁻¹' W with hWinf_def
  set Wfin : Set (PDFin a b) :=
    (QuotientGroup.mk : (QuatFin (a : F) (b : F))ˣ → PDFin a b) '' (quatCongS a b S m hm1 : Set _) with hWfin_def
  have hset : pdMk (a : F) (b : F) '' Hset a b S m hm1 W = pdSplit a b ha hb ⁻¹' (Winf ×ˢ Wfin) := by
    ext q
    obtain ⟨x, rfl⟩ := pdMk_surjective (a : F) (b : F) q
    have hps := pdSplit_mk ha hb x
    constructor
    · rintro ⟨y, ⟨hyW, hyS⟩, hyx⟩
      rw [mem_preimage, ← hyx]
      have hpy := pdSplit_mk ha hb y
      change pdSplit a b ha hb (QuotientGroup.mk y) ∈ _
      rw [hpy]
      exact ⟨hyW, ⟨_, hyS, rfl⟩⟩
    · intro h
      have h' : pdSplit a b ha hb (QuotientGroup.mk x) ∈ Winf ×ˢ Wfin := h
      rw [hps] at h'
      obtain ⟨hx1, y, hy, hyx⟩ := h'
      rw [QuotientGroup.eq] at hyx
      obtain ⟨c, hc⟩ := hyx
      have hx2 : (quatUnitsEquiv (a : F) (b : F) x).2 = y * finScalar (a : F) (b : F) c := by
        rw [hc]; group
      set z : (Adeles F)ˣ := (idelesEquiv F).symm (1, c⁻¹) with hz
      set x' := x * quatScalar (a : F) (b : F) z with hx'
      have hq : quatUnitsEquiv (a : F) (b : F) x' = ((quatUnitsEquiv (a : F) (b : F) x).1, y) := by
        rw [hx', quatUnitsEquiv_mul_quatScalar, hz]
        simp only [idelesEquiv_apply, ContinuousMulEquiv.apply_symm_apply, map_one, mul_one, map_inv]
        rw [hx2, mul_inv_cancel_right]
      have hpd : pdMk (a : F) (b : F) x' = pdMk (a : F) (b : F) x := by
        have : pdMk (a : F) (b : F) (quatScalar (a : F) (b : F) z) = 1 :=
          (mem_ker_pdMk (a : F) (b : F)).2 ⟨z, rfl⟩
        rw [hx', map_mul, this, mul_one]
      refine ⟨x', ⟨?_, ?_⟩, hpd⟩
      · show conjInf a b ((quatUnitsEquiv (a : F) (b : F) x').1) ∈ W
        rw [hq]; exact hx1
      · show (quatUnitsEquiv (a : F) (b : F) x').2 ∈ quatCongS a b S m hm1
        rw [hq]; exact hy
  have hWinf : MeasurableSet Winf := (pdInfEquiv a b ha hb).continuous.measurable hW
  have hWfin : MeasurableSet Wfin :=
    (QuotientGroup.isOpenMap_coe _ (isOpen_quatCongS S m hm1)).measurableSet
  have hI : (Measure.map (⇑(pdInfEquiv a b ha hb).symm)
      (muArchTamSO (QuatZeta.pureFormO a b) (nondegenerate_pureFormO a b ha hb))) Winf =
      muArchTamSO (QuatZeta.pureFormO a b) (nondegenerate_pureFormO a b ha hb) W := by
    rw [Measure.map_apply (map_continuous (pdInfEquiv a b ha hb).symm).measurable hWinf]
    congr 1
    ext g
    simp [hWinf_def]
  have hF : muPDFin ha hb Wfin = rF a b * QuadFormsKB.Tamagawa.Measure.muFin (QuatZeta.pureFormO a b) (fun _ => 1)
      (QuadFormsKB.Tamagawa.Measure.boxSO (QuatZeta.pureFormO a b) S (congSO3S m hm1)) := by
    rw [muPDFin, Measure.smul_apply,
      Measure.map_apply (map_continuous (pdFinEquiv a b ha hb).symm).measurable hWfin, smul_eq_mul]
    congr 2
    rw [← coe_map_quatCongS ha hb S m hm1 hS hmS]
    ext g
    simp only [mem_preimage, hWfin_def, mem_image, SetLike.mem_coe, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyg⟩
      refine ⟨y, hy, ?_⟩
      have := congrArg (pdFinEquiv a b ha hb) hyg
      rw [ContinuousMulEquiv.apply_symm_apply] at this
      exact this
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, hy, (pdFinEquiv a b ha hb).injective ?_⟩
      rw [ContinuousMulEquiv.apply_symm_apply]
      rfl
  have hK : ENNReal.ofReal (kInf F a b) = rF a b := by
    rw [← rF_toReal_eq_kInf a b ha hb, ENNReal.ofReal_toReal (rF_ne_top ha hb)]
  rw [hset, ← Measure.map_apply (map_continuous (pdSplit a b ha hb)).measurable (hWinf.prod hWfin),
    muPD_map_pdSplit a b ha hb, Measure.smul_apply, nuRef, Measure.prod_prod, smul_eq_mul, hI, hF, hK]
  have hinv := ENNReal.inv_mul_cancel (rF_ne_zero ha hb) (rF_ne_top ha hb)
  generalize (muArchTamSO (QuatZeta.pureFormO a b) (nondegenerate_pureFormO a b ha hb)) W = A
  generalize (QuadFormsKB.Tamagawa.Measure.muFin (QuatZeta.pureFormO a b) (fun _ => 1))
    (QuadFormsKB.Tamagawa.Measure.boxSO (QuatZeta.pureFormO a b) S (congSO3S m hm1)) = M
  generalize rF a b = r at hinv ⊢
  calc r⁻¹ * (A * (r * M)) = (r⁻¹ * r) * (A * M) := by ring
    _ = A * M := by rw [hinv, one_mul]

end Hset

/-! ### Shells in $F_\infty^\times$ -/

/-- The shell $\{t : |t_w|\in(1,4)\text{ at every real place},\ \|t_w\|\in(1,4)\text{ at every complex place}\}$. -/
def Binf : Set (mixedSpace F)ˣ :=
  {t | (∀ w, |(t : mixedSpace F).1 w| ∈ Set.Ioo (1:ℝ) 4) ∧ ∀ w, ‖(t : mixedSpace F).2 w‖ ∈ Set.Ioo (1:ℝ) 4}

/-- The shell $\{v : |v_w|\in(1,2)\text{ at every real place},\ \|v_w\|\in(1,2)\text{ at every complex place}\}$. -/
def Vone : Set (mixedSpace F)ˣ :=
  {v | (∀ w, |(v : mixedSpace F).1 w| ∈ Set.Ioo (1:ℝ) 2) ∧ ∀ w, ‖(v : mixedSpace F).2 w‖ ∈ Set.Ioo (1:ℝ) 2}

/-- The adelic shell $B' = \{t\in\mathbb A^\times : t_\infty\in B_\infty,\ t_f\in\hat{\mathcal O}^\times\}$. -/
def Bset' : Set (Adeles F)ˣ := idelesEquiv F ⁻¹' (Binf ×ˢ (OHatUnits F : Set (FiniteAdeleRing (𝓞 F) F)ˣ))

theorem continuous_inf_fst (w : {w : InfinitePlace F // w.IsReal}) :
    Continuous fun t : (mixedSpace F)ˣ => (t : mixedSpace F).1 w :=
  (continuous_apply w).comp (continuous_fst.comp Units.continuous_val)

theorem continuous_inf_snd (w : {w : InfinitePlace F // w.IsComplex}) :
    Continuous fun t : (mixedSpace F)ˣ => (t : mixedSpace F).2 w :=
  (continuous_apply w).comp (continuous_snd.comp Units.continuous_val)

theorem isOpen_shell (c d : ℝ) :
    IsOpen {t : (mixedSpace F)ˣ | (∀ w, |(t : mixedSpace F).1 w| ∈ Set.Ioo c d) ∧
      ∀ w, ‖(t : mixedSpace F).2 w‖ ∈ Set.Ioo c d} := by
  have h1 : {t : (mixedSpace F)ˣ | (∀ w, |(t : mixedSpace F).1 w| ∈ Set.Ioo c d) ∧
      ∀ w, ‖(t : mixedSpace F).2 w‖ ∈ Set.Ioo c d} =
      (⋂ w : {w : InfinitePlace F // w.IsReal}, (fun t : (mixedSpace F)ˣ => |(t : mixedSpace F).1 w|) ⁻¹' Set.Ioo c d) ∩
      ⋂ w : {w : InfinitePlace F // w.IsComplex}, (fun t : (mixedSpace F)ˣ => ‖(t : mixedSpace F).2 w‖) ⁻¹' Set.Ioo c d := by
    ext t; simp
  rw [h1]
  refine (isOpen_iInter_of_finite fun w => isOpen_Ioo.preimage ((continuous_inf_fst w).abs)).inter
    (isOpen_iInter_of_finite fun w => isOpen_Ioo.preimage ((continuous_inf_snd w).norm))

theorem isOpen_Binf : IsOpen (Binf (F := F)) := isOpen_shell 1 4
theorem isOpen_Vone : IsOpen (Vone (F := F)) := isOpen_shell 1 2

theorem measurableSet_Binf : MeasurableSet (Binf (F := F)) := isOpen_Binf.measurableSet

theorem measurableSet_Bset' : MeasurableSet (Bset' (F := F)) :=
  (measurableSet_Binf.prod (isOpen_OHatUnits (F := F)).measurableSet).preimage
    (idelesEquiv F).continuous.measurable

/-- The unit of $F_\infty$ with real components $f$ and complex components $g$ (all nonzero). -/
def mkInfUnitRC (f : {w : InfinitePlace F // w.IsReal} → ℝ) (g : {w : InfinitePlace F // w.IsComplex} → ℂ)
    (hf : ∀ w, f w ≠ 0) (hg : ∀ w, g w ≠ 0) : (mixedSpace F)ˣ where
  val := (f, g)
  inv := (fun w => (f w)⁻¹, fun w => (g w)⁻¹)
  val_inv := Prod.ext (funext fun w => mul_inv_cancel₀ (hf w)) (funext fun w => mul_inv_cancel₀ (hg w))
  inv_val := Prod.ext (funext fun w => inv_mul_cancel₀ (hf w)) (funext fun w => inv_mul_cancel₀ (hg w))

@[simp] theorem mkInfUnitRC_val_fst (f : {w : InfinitePlace F // w.IsReal} → ℝ) (g : {w : InfinitePlace F // w.IsComplex} → ℂ)
    (hf : ∀ w, f w ≠ 0) (hg : ∀ w, g w ≠ 0) (w : {w : InfinitePlace F // w.IsReal}) :
    ((mkInfUnitRC f g hf hg : (mixedSpace F)ˣ) : mixedSpace F).1 w = f w := rfl

@[simp] theorem mkInfUnitRC_val_snd (f : {w : InfinitePlace F // w.IsReal} → ℝ) (g : {w : InfinitePlace F // w.IsComplex} → ℂ)
    (hf : ∀ w, f w ≠ 0) (hg : ∀ w, g w ≠ 0) (w : {w : InfinitePlace F // w.IsComplex}) :
    ((mkInfUnitRC f g hf hg : (mixedSpace F)ˣ) : mixedSpace F).2 w = g w := rfl

theorem unit_fst_ne_zero (t : (mixedSpace F)ˣ) (w : {w : InfinitePlace F // w.IsReal}) :
    (t : mixedSpace F).1 w ≠ 0 :=
  isUnit_iff_ne_zero.1 (Pi.isUnit_iff.1 (Prod.isUnit_iff.1 t.isUnit).1 w)

theorem unit_snd_ne_zero (t : (mixedSpace F)ˣ) (w : {w : InfinitePlace F // w.IsComplex}) :
    (t : mixedSpace F).2 w ≠ 0 :=
  isUnit_iff_ne_zero.1 (Pi.isUnit_iff.1 (Prod.isUnit_iff.1 t.isUnit).2 w)

/-! ### Positivity and finiteness of $\omega_\infty(V_1)$ -/

theorem omegaInf_Vone_ne_zero : omegaInf F (Vone (F := F)) ≠ 0 := by
  have hne : (Vone (F := F)).Nonempty := by
    refine ⟨mkInfUnitRC (fun _ => 3 / 2) (fun _ => ((3 / 2 : ℝ) : ℂ)) (fun _ => by norm_num)
      (fun _ => by norm_num), fun w => ?_, fun w => ?_⟩
    · simp only [mkInfUnitRC_val_fst]
      rw [abs_of_pos (by norm_num)]; constructor <;> norm_num
    · simp only [mkInfUnitRC_val_snd]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]; constructor <;> norm_num
  exact (isOpen_Vone.measure_pos (omegaInf F) hne).ne'

theorem omegaInf_Vone_ne_top : omegaInf F (Vone (F := F)) ≠ ∞ := by
  set A : Set (mixedSpace F) := {x | (∀ w : {w : InfinitePlace F // w.IsReal}, x.1 w ∈ Icc (-2 : ℝ) 2) ∧
    ∀ w : {w : InfinitePlace F // w.IsComplex}, ‖x.2 w‖ ≤ 2} with hA
  have hAc : IsCompact A := by
    have : A = (Set.univ.pi fun _ => Icc (-2 : ℝ) 2) ×ˢ (Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) 2) := by
      ext x; simp only [hA, mem_setOf_eq, mem_prod, mem_univ_pi, mem_closedBall_zero_iff]
    rw [this]
    exact (isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_closedBall _ _)
  set K : Set (mixedSpace F)ˣ := {x | (∀ w : {w : InfinitePlace F // w.IsReal}, 1 ≤ |(x : mixedSpace F).1 w| ∧ |(x : mixedSpace F).1 w| ≤ 2) ∧
    ∀ w : {w : InfinitePlace F // w.IsComplex}, 1 ≤ ‖(x : mixedSpace F).2 w‖ ∧ ‖(x : mixedSpace F).2 w‖ ≤ 2} with hK
  -- `K` is closed in the units and its image is compact
  have hKc : IsCompact K := by
    set B : Set (mixedSpace F) := {x | (∀ w : {w : InfinitePlace F // w.IsReal}, 1 ≤ |x.1 w| ∧ |x.1 w| ≤ 2) ∧
      ∀ w : {w : InfinitePlace F // w.IsComplex}, 1 ≤ ‖x.2 w‖ ∧ ‖x.2 w‖ ≤ 2} with hB
    have hBcl : IsClosed B := by
      have : B = (⋂ w : {w : InfinitePlace F // w.IsReal}, {x : mixedSpace F | 1 ≤ |x.1 w| ∧ |x.1 w| ≤ 2}) ∩
          ⋂ w : {w : InfinitePlace F // w.IsComplex}, {x : mixedSpace F | 1 ≤ ‖x.2 w‖ ∧ ‖x.2 w‖ ≤ 2} := by
        ext x; simp [hB]
      rw [this]
      refine (isClosed_iInter fun w => ?_).inter (isClosed_iInter fun w => ?_)
      · have c1 : Continuous fun x : mixedSpace F => |x.1 w| := (continuous_apply w |>.comp continuous_fst).abs
        exact (isClosed_le continuous_const c1).inter (isClosed_le c1 continuous_const)
      · have c1 : Continuous fun x : mixedSpace F => ‖x.2 w‖ := (continuous_apply w |>.comp continuous_snd).norm
        exact (isClosed_le continuous_const c1).inter (isClosed_le c1 continuous_const)
    have hBsub : B ⊆ A := fun x hx =>
      ⟨fun w => ⟨by have := (hx.1 w).2; rw [abs_le] at this; exact this.1, by have := (hx.1 w).2; rw [abs_le] at this; exact this.2⟩,
        fun w => (hx.2 w).2⟩
    have hBc : IsCompact B := hAc.of_isClosed_subset hBcl hBsub
    have hKB : K = Units.val ⁻¹' B := by ext x; simp [hK, hB]
    rw [hKB, isOpenEmbedding_val_mixedSpace.isEmbedding.isCompact_preimage_iff]
    · exact hBc
    · intro x hx
      have hu : IsUnit x := by
        rw [Prod.isUnit_iff]
        refine ⟨Pi.isUnit_iff.2 fun w => isUnit_iff_ne_zero.2 ?_, Pi.isUnit_iff.2 fun w => isUnit_iff_ne_zero.2 ?_⟩
        · intro h; have := (hx.1 w).1; rw [h, abs_zero] at this; linarith
        · intro h; have := (hx.2 w).1; rw [h, norm_zero] at this; linarith
      exact ⟨hu.unit, rfl⟩
  have hsub : Vone (F := F) ⊆ K := fun v hv =>
    ⟨fun w => ⟨(hv.1 w).1.le, (hv.1 w).2.le⟩, fun w => ⟨(hv.2 w).1.le, (hv.2 w).2.le⟩⟩
  exact ne_of_lt (lt_of_le_of_lt (measure_mono hsub) hKc.measure_lt_top)

/-! ### The centre fibre -/

section Fibre

/-- `finPart_nrd_mem_OHat` for every number field (the original sits in a totally real section). -/
theorem finPart_nrd_mem_OHat' (x : (QuatAdele (a : F) (b : F))ˣ)
    (hx : ∀ v, unitAtA (a : F) (b : F) v x ∈ lamLocUnits (a : F) (b : F) v) :
    finPart (nrdUnit x) ∈ OHatUnits F := by
  rw [finPart_mem_OHatUnits_iff]
  intro v
  rw [← nrd_unitAtA, ← nrdLoc_eq_nrd]
  exact ((mem_lamLocUnits_iff (fun w => valued_algebraMap_le_one a w) (fun w => valued_algebraMap_le_one b w) _).1
    (hx v)).2

theorem infPart_pow'(u : (Adeles F)ˣ) (n : ℕ) : infPart (u ^ n) = infPart u ^ n := map_pow (Units.map _) u n
theorem finPart_pow' (u : (Adeles F)ˣ) (n : ℕ) : finPart (u ^ n) = finPart u ^ n := map_pow (Units.map _) u n

variable (S : Finset (HeightOneSpectrum (𝓞 F))) (m : HeightOneSpectrum (𝓞 F) → ℕ) (hm1 : ∀ v, 1 ≤ m v)

/-- Left translation of $\omega_\infty$: $\omega_\infty\{v : v^2t\in B_\infty\} = \omega_\infty(V_1)$ for $t\in F_\infty^\times$
(the translation is by the unit $s$ with $s_w = \sqrt{|t_w|}$ at real and $\sqrt{\|t_w\|}$ at complex places). -/
theorem omegaInf_sq_mul_Binf (t : (mixedSpace F)ˣ) :
    omegaInf F {v : (mixedSpace F)ˣ | v ^ 2 * t ∈ Binf} = omegaInf F (Vone (F := F)) := by
  set s := mkInfUnitRC (F := F) (fun w => Real.sqrt |(t : mixedSpace F).1 w|)
    (fun w => ((Real.sqrt ‖(t : mixedSpace F).2 w‖ : ℝ) : ℂ))
    (fun w => (Real.sqrt_pos.2 (abs_pos.2 (unit_fst_ne_zero t w))).ne')
    (fun w => by
      have := Real.sqrt_pos.2 (norm_pos_iff.2 (unit_snd_ne_zero t w))
      exact_mod_cast this.ne') with hs
  have hsq_fst : ∀ (v : (mixedSpace F)ˣ) (w : {w : InfinitePlace F // w.IsReal}),
      ((v ^ 2 : (mixedSpace F)ˣ) : mixedSpace F).1 w = ((v : mixedSpace F).1 w) ^ 2 := fun v w => by
    rw [Units.val_pow_eq_pow_val]; rfl
  have hsq_snd : ∀ (v : (mixedSpace F)ˣ) (w : {w : InfinitePlace F // w.IsComplex}),
      ((v ^ 2 : (mixedSpace F)ˣ) : mixedSpace F).2 w = ((v : mixedSpace F).2 w) ^ 2 := fun v w => by
    rw [Units.val_pow_eq_pow_val]; rfl
  have hset : {v : (mixedSpace F)ˣ | v ^ 2 * t ∈ Binf} = (fun v => s * v) ⁻¹' Vone := by
    ext v
    simp only [mem_setOf_eq, mem_preimage, Binf, Vone]
    have sq : ∀ x : ℝ, 0 ≤ x → ((1 < x ^ 2 ∧ x ^ 2 < 4) ↔ (1 < x ∧ x < 2)) := by
      intro x hx
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, by nlinarith⟩
      · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, by nlinarith⟩
    refine and_congr (forall_congr' fun w => ?_) (forall_congr' fun w => ?_)
    · have e : |((v ^ 2 * t : (mixedSpace F)ˣ) : mixedSpace F).1 w| =
          (|((s * v : (mixedSpace F)ˣ) : mixedSpace F).1 w|) ^ 2 := by
        rw [Units.val_mul, Units.val_mul, Prod.fst_mul, Prod.fst_mul, Pi.mul_apply, Pi.mul_apply, hsq_fst v w,
          hs, mkInfUnitRC_val_fst, abs_mul, abs_mul, abs_pow, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
          Real.sq_sqrt (abs_nonneg _)]
        ring
      simp only [mem_Ioo]
      rw [e]
      exact sq _ (abs_nonneg _)
    · have e : ‖((v ^ 2 * t : (mixedSpace F)ˣ) : mixedSpace F).2 w‖ =
          (‖((s * v : (mixedSpace F)ˣ) : mixedSpace F).2 w‖) ^ 2 := by
        rw [Units.val_mul, Units.val_mul, Prod.snd_mul, Prod.snd_mul, Pi.mul_apply, Pi.mul_apply, hsq_snd v w,
          hs, mkInfUnitRC_val_snd, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (norm_nonneg _)]
        ring
      simp only [mem_Ioo]
      rw [e]
      exact sq _ (norm_nonneg _)
  rw [hset, measure_preimage_mul]

/-- **The centre fibre constant**, every number field: for every $\beta\in H(W)$ (any $W$),
$\mathrm{tamIdeles}\{u : \beta u\in H(W),\ u^2\operatorname{nrd}(\beta)\in B'\} =
\omega_\infty(V_1)\,\mu_f(\hat{\mathcal O}^\times)$. -/
@[kb "weil1982" "§2.3, p. 21; §3.7(a), p. 63 [unverified page]"]
theorem tamIdeles_center_fibre (ha : a ≠ 0) (W : Set (GInfSO (QuatZeta.pureFormO a b)))
    (β : (QuatAdele (a : F) (b : F))ˣ) (hβ : β ∈ Hset a b S m hm1 W) :
    tamIdeles F {u | β * quatScalar (a : F) (b : F) u ∈ Hset a b S m hm1 W ∧ u ^ 2 * nrdUnit β ∈ Bset'} =
      omegaInf F (Vone (F := F)) * muFinUnits F (OHatUnits F) := by
  have hβS : β ∈ HS a b S m hm1 := hβ.2
  -- the scalar condition
  have hscal : ∀ u : (Adeles F)ˣ, β * quatScalar (a : F) (b : F) u ∈ Hset a b S m hm1 W ↔
      finPart u ∈ OHatUnits F := by
    intro u
    have hinf : conjInf a b ((quatUnitsEquiv (a : F) (b : F) (β * quatScalar (a : F) (b : F) u)).1) =
        conjInf a b ((quatUnitsEquiv (a : F) (b : F) β).1) := by
      rw [quatUnitsEquiv_mul_quatScalar, map_mul]
      have : conjInf a b (infScalar (a : F) (b : F) (idelesEquiv F u).1) = 1 :=
        (conjInf_eq_one_iff a b ha _).2 ⟨_, rfl⟩
      rw [this, mul_one]
    have hfin : β * quatScalar (a : F) (b : F) u ∈ HS a b S m hm1 ↔ finPart u ∈ OHatUnits F := by
      rw [(HS a b S m hm1).mul_mem_cancel_left hβS, quatScalar_mem_HS_iff S m hm1 ha]
    constructor
    · intro h; exact hfin.1 h.2
    · intro h; exact ⟨by rw [hinf]; exact hβ.1, hfin.2 h⟩
  have hnrd : finPart (nrdUnit β) ∈ OHatUnits F :=
    finPart_nrd_mem_OHat' a b β ((mem_HS a b S m hm1).1 hβS).1
  set t := infPart (nrdUnit β) with ht
  have hset : {u | β * quatScalar (a : F) (b : F) u ∈ Hset a b S m hm1 W ∧ u ^ 2 * nrdUnit β ∈ Bset'} =
      idelesEquiv F ⁻¹' ({v : (mixedSpace F)ˣ | v ^ 2 * t ∈ Binf} ×ˢ (OHatUnits F : Set (FiniteAdeleRing (𝓞 F) F)ˣ)) := by
    ext u
    simp only [mem_setOf_eq, Bset', mem_preimage, mem_prod, idelesEquiv_apply, SetLike.mem_coe, hscal]
    rw [infPart_mul, infPart_pow', finPart_mul, finPart_pow']
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩
      exact ⟨h1, h2, (OHatUnits F).mul_mem ((OHatUnits F).pow_mem h1 2) hnrd⟩
  rw [hset, tamIdeles_prod, omegaInf_sq_mul_Binf]

end Fibre

end QuadFormsKB.Tamagawa.Measure.Weil

end
