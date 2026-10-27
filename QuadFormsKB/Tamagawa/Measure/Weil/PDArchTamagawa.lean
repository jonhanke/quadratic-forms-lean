import QuadFormsKB.Tamagawa.Measure.Weil.PDArchInfVol

/-!
# The archimedean comparison for $PD^\times \cong SO(D^0)$, every number field and signature

**Layer:** $F$ a number field, $a, b \in \mathcal O_F\setminus 0$, $D = (a,b)_F$ (any signature, division or not),
$Q_0 = \langle -a,-b,ab\rangle$.

**Proves** `haarConst_eq`: write Weil's measure `muPD` on $PD^\times(\mathbb A)$ as
$c^{-1}\,(\nu_\infty\times\mu_{PD,f})$ with $\nu_\infty$ the transport of $\mu^{\mathrm{Tam}}_\infty$ (`muArchTamSO`) and
$\mu_{PD,f}$ `muPDFin` (Haar uniqueness, `nuRef_map_eq_smul_muPD`). Then
$$c = K_\infty = c_F\prod_{w\ \mathrm{real}}|8a^3b^3|_w^{-1}\prod_{w\ \mathrm{complex}}|8a^3b^3|_w^{-1}.$$
*Proof.* On the boxes $E_\delta\times J$ (`box_identity`): $\mu^{\mathrm{Tam}}_\infty(c_\infty E_\delta)\,\omega_\infty(T_\delta)
= c\,\omega^{D^\times}_\infty(S_\delta)$. The left side is $c_F\,2^{3r_2}\prod_w\mu_{Q^w}(\mathcal A_{w,\delta})$
(`image_pdInfEquiv_sBall`: $c_\infty E_\delta$ is the product of the local chart neighbourhoods), and the local Leray
asymptotics (`tendsto_leray_quatBall`, `tendsto_lerayC_quatBall`) give its first-order behaviour; the right side is
$c\,\omega_\infty(T_\delta)\mathrm{vol}(B_\delta)(1 + o(1))$ (`tendsto_box_ratio`); $\mathrm{vol}(B_\delta) =
2^{3r_2}\prod_w\mathrm{vol}_w(B_\delta)$ for the self-dual measure (`selfDual3_ball`), and the two factors $2^{3r_2}$
(Weil's normalization at the complex places, `cxWeil`) cancel.
-/

open MeasureTheory Set Metric Filter Topology Quaternion NumberField IsDedekindDomain NumberField.mixedEmbedding
  NumberField.InfinitePlace Matrix
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.QuatZeta QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Siegel
  QuadFormsKB.Tamagawa.ArchSOMeasure

section Generic

variable {K : Type*} [Field K] {A B : K}

theorem nMat_smul (r : K) (x : ℍ[K,A,B]) : nMat (r • x) = r ^ 2 • nMat x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nMat, imv, Quat.pure, Pi.single_apply] <;> ring

/-- **Scalars do not change the chart**: $c(r(1+y)) = c(1+y)$. -/
theorem conjGL_eq_cMat_of_smul (u : (ℍ[K,A,B])ˣ) (r : K) (y : Fin 3 → K) (hr : r ≠ 0)
    (hy : 1 + qPure A B y ≠ 0) (hu : (u : ℍ[K,A,B]) = r • (1 + Quat.pure y)) :
    ((conjGL u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = cMat A B y := by
  have hinv : nrd ((u⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B]) = (nrd (u : ℍ[K,A,B]))⁻¹ := by
    have h := nrd_mul (u : ℍ[K,A,B]) ((u⁻¹ : (ℍ[K,A,B])ˣ) : ℍ[K,A,B])
    rw [Units.mul_inv, nrd_one] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hn : nrd (u : ℍ[K,A,B]) = r ^ 2 * (1 + qPure A B y) := by
    rw [hu, ← nrd_one_add_pure_eq, Algebra.smul_def, nrd_mul]
    simp [nrd]
  rw [conjGL_val, hinv, hn, hu, nMat_smul, smul_smul, cMat]
  congr 1
  field_simp

end Generic

open scoped Classical

section Places

variable {F : Type} [Field F] [NumberField F] (a b : 𝓞 F)

local notation "Q₀" => pureFormO a b

/-- The real embedding at a real place. -/
abbrev sR (w : {w : InfinitePlace F // w.IsReal}) : F →+* ℝ := embedding_of_isReal w.2

/-- The chosen complex embedding at a complex place. -/
abbrev sC (w : {w : InfinitePlace F // w.IsComplex}) : F →+* ℂ := w.1.embedding

/-- The chart neighbourhood at a real place. -/
def aRw (w : {w : InfinitePlace F // w.IsReal}) (δ : ℝ) : Set (ArchSO (QRe Q₀ w)) :=
  {g | ∃ z ∈ ball (0 : Fin 3 → ℝ) δ, ArchSOInst.mat _ g = cMat (sR w (a : F)) (sR w (b : F)) z}

/-- The chart neighbourhood at a complex place. -/
def aCw (w : {w : InfinitePlace F // w.IsComplex}) (δ : ℝ) : Set (LerayComplex.ArchSOC (QCx Q₀ w)) :=
  {g | ∃ z ∈ ball (0 : Fin 3 → ℂ) δ, LerayComplex.ArchSOC.mat _ g = cMat (sC w (a : F)) (sC w (b : F)) z}

/-- The real component of $y \in F_\infty^3$ at $w$. -/
def yR (y : Fin 3 → mixedSpace F) (w : {w : InfinitePlace F // w.IsReal}) : Fin 3 → ℝ := fun i => (y i).1 w

/-- The complex component of $y \in F_\infty^3$ at $w$. -/
def yC (y : Fin 3 → mixedSpace F) (w : {w : InfinitePlace F // w.IsComplex}) : Fin 3 → ℂ := fun i => (y i).2 w

theorem norm_yR_le (y : Fin 3 → mixedSpace F) (w : {w : InfinitePlace F // w.IsReal}) : ‖yR y w‖ ≤ ‖y‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
    ((norm_le_pi_norm (y i).1 w).trans (norm_fst_le (y i))).trans (norm_le_pi_norm y i)

theorem norm_yC_le (y : Fin 3 → mixedSpace F) (w : {w : InfinitePlace F // w.IsComplex}) : ‖yC y w‖ ≤ ‖y‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
    ((norm_le_pi_norm (y i).2 w).trans (norm_snd_le (y i))).trans (norm_le_pi_norm y i)

theorem projR_boxMap (w : {w : InfinitePlace F // w.IsReal}) (p : (mixedSpace F)ˣ × (Fin 3 → mixedSpace F)) :
    projR (a : F) (b : F) w (boxMap a b p) = ((p.1 : mixedSpace F).1 w) • (1 + Quat.pure (yR p.2 w)) := by
  ext <;> simp [boxMap_re, boxMap_imI, boxMap_imJ, boxMap_imK, yR, Quat.pure]

theorem projC_boxMap (w : {w : InfinitePlace F // w.IsComplex}) (p : (mixedSpace F)ˣ × (Fin 3 → mixedSpace F)) :
    projC (a : F) (b : F) w (boxMap a b p) = ((p.1 : mixedSpace F).2 w) • (1 + Quat.pure (yC p.2 w)) := by
  ext <;> simp [boxMap_re, boxMap_imI, boxMap_imJ, boxMap_imK, yC, Quat.pure]

theorem ne_zero_of_isUnit_R {t : mixedSpace F} (ht : IsUnit t) (w : {w : InfinitePlace F // w.IsReal}) :
    t.1 w ≠ 0 :=
  ((Prod.isUnit_iff.mp ht).1.map (Pi.evalRingHom _ w)).ne_zero

theorem ne_zero_of_isUnit_C {t : mixedSpace F} (ht : IsUnit t) (w : {w : InfinitePlace F // w.IsComplex}) :
    t.2 w ≠ 0 :=
  ((Prod.isUnit_iff.mp ht).2.map (Pi.evalRingHom _ w)).ne_zero

theorem mat_conjR_boxMap (w : {w : InfinitePlace F // w.IsReal}) (x : (QuatInf (a : F) (b : F))ˣ)
    (p : (mixedSpace F)ˣ × (Fin 3 → mixedSpace F)) (hx : (x : QuatInf (a : F) (b : F)) = boxMap a b p)
    (hy : 1 + qPure (sR w (a : F)) (sR w (b : F)) (yR p.2 w) ≠ 0) :
    ArchSOInst.mat _ (conjR a b w x) = cMat (sR w (a : F)) (sR w (b : F)) (yR p.2 w) := by
  change ((conjGL (Units.map (projR (a : F) (b : F) w).toMonoidHom x) : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = _
  refine conjGL_eq_cMat_of_smul _ ((p.1 : mixedSpace F).1 w) _ (ne_zero_of_isUnit_R p.1.isUnit w) hy ?_
  rw [Units.coe_map]
  change projR (a : F) (b : F) w (x : QuatInf (a : F) (b : F)) = _
  rw [hx, projR_boxMap]

theorem mat_conjC_boxMap (w : {w : InfinitePlace F // w.IsComplex}) (x : (QuatInf (a : F) (b : F))ˣ)
    (p : (mixedSpace F)ˣ × (Fin 3 → mixedSpace F)) (hx : (x : QuatInf (a : F) (b : F)) = boxMap a b p)
    (hy : 1 + qPure (sC w (a : F)) (sC w (b : F)) (yC p.2 w) ≠ 0) :
    LerayComplex.ArchSOC.mat _ (conjC a b w x) = cMat (sC w (a : F)) (sC w (b : F)) (yC p.2 w) := by
  change ((conjGL (Units.map (projC (a : F) (b : F) w).toMonoidHom x) : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) = _
  refine conjGL_eq_cMat_of_smul _ ((p.1 : mixedSpace F).2 w) _ (ne_zero_of_isUnit_C p.1.isUnit w) hy ?_
  rw [Units.coe_map]
  change projC (a : F) (b : F) w (x : QuatInf (a : F) (b : F)) = _
  rw [hx, projC_boxMap]

/-- The radius conditions on $\delta$. -/
structure RadOK (δ : ℝ) : Prop where
  pos : 0 < δ
  lt1 : δ < 1
  ltQ : δ ≤ rQ F a b
  ltR : ∀ w : {w : InfinitePlace F // w.IsReal}, δ ≤ rad0 (sR w (a : F)) (sR w (b : F))
  ltC : ∀ w : {w : InfinitePlace F // w.IsComplex}, δ ≤ rad0 (sC w (a : F)) (sC w (b : F))

theorem eventually_radOK : ∀ᶠ δ in 𝓝[>] (0 : ℝ), RadOK a b δ := by
  have h1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < min 1 (rQ F a b) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (lt_min one_pos (rQ_pos a b)))
  have h2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ w : {w : InfinitePlace F // w.IsReal},
      δ ≤ rad0 (sR w (a : F)) (sR w (b : F)) :=
    Filter.eventually_all.2 fun w => nhdsWithin_le_nhds (Iic_mem_nhds (rad0_pos _ _))
  have h3 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ w : {w : InfinitePlace F // w.IsComplex},
      δ ≤ rad0 (sC w (a : F)) (sC w (b : F)) :=
    Filter.eventually_all.2 fun w => nhdsWithin_le_nhds (Iic_mem_nhds (rad0_pos _ _))
  filter_upwards [h1, h2, h3, eventually_mem_nhdsWithin] with δ h1 h2 h3 h0
  exact ⟨h0, h1.trans_le (min_le_left _ _), (le_of_lt h1).trans (min_le_right _ _), h2, h3⟩

variable {a b} in
/-- **The box in $PD^\times(F_\infty)$ is the product of the local chart neighbourhoods** (in $G_\infty$). -/
theorem image_pdInfEquiv_sBall (ha : a ≠ 0) (hb : b ≠ 0) {δ : ℝ} (hδ : RadOK a b δ) :
    pdInfEquiv a b ha hb '' ((QuotientGroup.mk : (QuatInf (a : F) (b : F))ˣ → PDInf a b) '' sBall a b δ) =
      (univ.pi fun w => aRw a b w δ) ×ˢ (univ.pi fun w => aCw a b w δ) := by
  rw [image_image]
  have hconj : ∀ x : (QuatInf (a : F) (b : F))ˣ, pdInfEquiv a b ha hb (QuotientGroup.mk x) = conjInf a b x :=
    fun x => rfl
  simp_rw [hconj]
  have hqR : ∀ (w : {w : InfinitePlace F // w.IsReal}) (z : Fin 3 → ℝ), ‖z‖ < δ →
      1 + qPure (sR w (a : F)) (sR w (b : F)) z ≠ 0 := fun w z hz =>
    one_add_qPure_ne_zero _ _ (hz.trans_le ((hδ.ltR w).trans (min_le_right _ _)))
  have hqC : ∀ (w : {w : InfinitePlace F // w.IsComplex}) (z : Fin 3 → ℂ), ‖z‖ < δ →
      1 + qPure (sC w (a : F)) (sC w (b : F)) z ≠ 0 := fun w z hz =>
    one_add_qPure_ne_zero _ _ (hz.trans_le ((hδ.ltC w).trans (min_le_right _ _)))
  ext g
  constructor
  · rintro ⟨x, ⟨t, ht, y, hy, hx⟩, rfl⟩
    have hy' : ‖y‖ < δ := mem_ball_zero_iff.mp hy
    refine ⟨fun w _ => ⟨yR y w, mem_ball_zero_iff.mpr ((norm_yR_le y w).trans_lt hy'), ?_⟩,
      fun w _ => ⟨yC y w, mem_ball_zero_iff.mpr ((norm_yC_le y w).trans_lt hy'), ?_⟩⟩
    · exact mat_conjR_boxMap a b w x (t, y) hx (hqR w _ ((norm_yR_le y w).trans_lt hy'))
    · exact mat_conjC_boxMap a b w x (t, y) hx (hqC w _ ((norm_yC_le y w).trans_lt hy'))
  · rintro ⟨hR, hC⟩
    choose zR hzR hgR using fun w => hR w (mem_univ w)
    choose zC hzC hgC using fun w => hC w (mem_univ w)
    set y : Fin 3 → mixedSpace F := fun i => ((fun w => zR w i), (fun w => zC w i))
    have hyR : ∀ w, yR y w = zR w := fun w => rfl
    have hyC : ∀ w, yC y w = zC w := fun w => rfl
    have hy : ‖y‖ < δ := by
      rw [pi_norm_lt_iff hδ.pos]
      intro i
      rw [Prod.norm_def, max_lt_iff, pi_norm_lt_iff hδ.pos, pi_norm_lt_iff hδ.pos]
      exact ⟨fun w => (norm_le_pi_norm (zR w) i).trans_lt (mem_ball_zero_iff.mp (hzR w)),
        fun w => (norm_le_pi_norm (zC w) i).trans_lt (mem_ball_zero_iff.mp (hzC w))⟩
    have hu := isUnit_one_add_pureI a b (hy.trans_le hδ.ltQ)
    have hx : ((hu.unit : (QuatInf (a : F) (b : F))ˣ) : QuatInf (a : F) (b : F)) = boxMap a b (1, y) := by
      simp [boxMap]
    refine ⟨hu.unit, ⟨1, by simp [tBall, hδ.pos], y, mem_ball_zero_iff.mpr hy, by rw [hx]; rfl⟩, ?_⟩
    refine Prod.ext (funext fun w => archSO_ext (Units.ext ?_)) (funext fun w => Subtype.ext (Units.ext ?_))
    · have := mat_conjR_boxMap a b w hu.unit (1, y) hx (hqR w _ ((norm_yR_le y w).trans_lt hy))
      rw [hyR] at this
      exact this.trans (hgR w).symm
    · have := mat_conjC_boxMap a b w hu.unit (1, y) hx (hqC w _ ((norm_yC_le y w).trans_lt hy))
      rw [hyC] at this
      exact this.trans (hgC w).symm

/-! ### Volumes of balls -/

variable (F) in
theorem selfDual_ball {δ : ℝ} (hδ : 0 < δ) :
    Analysis.selfDualInf (F := F) (ball 0 δ) = (2 : ℝ≥0∞) ^ nrComplexPlaces F *
      (volume (ball (0 : ℝ) δ) ^ Fintype.card {w : InfinitePlace F // w.IsReal} *
        volume (ball (0 : ℂ) δ) ^ Fintype.card {w : InfinitePlace F // w.IsComplex}) := by
  rw [Analysis.selfDualInf, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
    show (0 : mixedSpace F) = (0, 0) from rfl, ← ball_prod_same, Measure.volume_eq_prod, Measure.prod_prod,
    volume_pi_ball _ hδ, volume_pi_ball _ hδ]
  simp only [Pi.zero_apply, Finset.prod_const, Finset.card_univ]
  push_cast; rfl

variable (F) in
theorem selfDual3_ball {δ : ℝ} (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin 3 => Analysis.selfDualInf (F := F)) (ball 0 δ) =
      ((2 : ℝ≥0∞) ^ nrComplexPlaces F) ^ 3 *
        (∏ _w : {w : InfinitePlace F // w.IsReal}, volume (ball (0 : Fin 3 → ℝ) δ)) *
        (∏ _w : {w : InfinitePlace F // w.IsComplex}, volume (ball (0 : Fin 3 → ℂ) δ)) := by
  have hL : (Measure.pi fun _ : Fin 3 => Analysis.selfDualInf (F := F)) (ball 0 δ) =
      Analysis.selfDualInf (F := F) (ball 0 δ) ^ 3 := by
    rw [ball_pi _ hδ, Measure.pi_pi]; simp
  rw [hL, selfDual_ball F hδ, volume_pi_ball _ hδ, volume_pi_ball _ hδ]
  simp only [Pi.zero_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

/-! ### Measurability and the local limits -/

theorem continuousOn_cMatK {𝕜 : Type*} [RCLike 𝕜] (A B : 𝕜) {δ : ℝ} (hδ : δ ≤ rad0 A B) :
    ContinuousOn (fun y : Fin 3 → 𝕜 => colsK (cMat A B y)) (ball 0 δ) := by
  have hq : ContinuousOn (fun y : Fin 3 → 𝕜 => (1 + qPure A B y)⁻¹) (ball 0 δ) := by
    refine ContinuousOn.inv₀ (by unfold qPure; fun_prop) fun y hy => one_add_qPure_ne_zero A B
      ((mem_ball_zero_iff.mp hy).trans_le (hδ.trans (min_le_right _ _)))
  have hn : Continuous fun y : Fin 3 → 𝕜 => colsK (nMat (1 + Quat.pure y : ℍ[𝕜,A,B])) := by
    refine continuous_pi fun j => continuous_pi fun i => ?_
    simp only [colsK]
    fin_cases i <;> fin_cases j <;> simp [nMat, imv, Quat.pure, Pi.single_apply] <;> fun_prop
  have : (fun y : Fin 3 → 𝕜 => colsK (cMat A B y)) =
      fun y => (1 + qPure A B y)⁻¹ • colsK (nMat (1 + Quat.pure y : ℍ[𝕜,A,B])) := by
    funext y; funext j i; simp [colsK, cMat]
  rw [this]
  exact hq.smul hn.continuousOn

theorem injOn_cMatK {𝕜 : Type*} [RCLike 𝕜] {A B : 𝕜} (hA : A ≠ 0) {δ : ℝ} (hδ : δ ≤ rad0 A B) :
    InjOn (fun y : Fin 3 → 𝕜 => colsK (cMat A B y)) (ball 0 δ) := by
  intro y hy y' hy' h
  have hq : ∀ z ∈ ball (0 : Fin 3 → 𝕜) δ, 1 + qPure A B z ≠ 0 := fun z hz => one_add_qPure_ne_zero A B
    ((mem_ball_zero_iff.mp hz).trans_le (hδ.trans (min_le_right _ _)))
  refine cMat_injective two_ne_zero hA (hq y hy) (hq y' hy') ?_
  ext i j; exact congrFun (congrFun h j) i

theorem measurableSet_aRw (w : {w : InfinitePlace F // w.IsReal}) {δ : ℝ}
    (ha : a ≠ 0) (hδ : δ ≤ rad0 (sR w (a : F)) (sR w (b : F))) : MeasurableSet (aRw a b w δ) := by
  have hA : sR w (a : F) ≠ 0 := (map_ne_zero _).2 (by exact_mod_cast ha)
  have himg := measurableSet_ball.image_of_continuousOn_injOn (continuousOn_cMatK _ _ hδ) (injOn_cMatK hA hδ)
  have hpre : aRw a b w δ = (fun g => colsK (ArchSOInst.mat _ g)) ⁻¹'
      ((fun y : Fin 3 → ℝ => colsK (cMat (sR w (a : F)) (sR w (b : F)) y)) '' ball 0 δ) := by
    ext g
    simp only [aRw, mem_ofPred_eq, mem_preimage, mem_image]
    constructor
    · rintro ⟨y, hy, h⟩; exact ⟨y, hy, by rw [h]⟩
    · rintro ⟨y, hy, h⟩; exact ⟨y, hy, by ext i j; exact (congrFun (congrFun h j) i).symm⟩
  rw [hpre]
  exact himg.preimage (continuous_pi fun j => continuous_pi fun i =>
    (ArchSOInst.continuous_mat _).matrix_elem i j).measurable

theorem measurableSet_aCw (w : {w : InfinitePlace F // w.IsComplex}) {δ : ℝ}
    (ha : a ≠ 0) (hδ : δ ≤ rad0 (sC w (a : F)) (sC w (b : F))) : MeasurableSet (aCw a b w δ) := by
  have hA : sC w (a : F) ≠ 0 := (map_ne_zero _).2 (by exact_mod_cast ha)
  have himg := measurableSet_ball.image_of_continuousOn_injOn (continuousOn_cMatK _ _ hδ) (injOn_cMatK hA hδ)
  have hpre : aCw a b w δ = (fun g => colsK (LerayComplex.ArchSOC.mat _ g)) ⁻¹'
      ((fun y : Fin 3 → ℂ => colsK (cMat (sC w (a : F)) (sC w (b : F)) y)) '' ball 0 δ) := by
    ext g
    simp only [aCw, mem_ofPred_eq, mem_preimage, mem_image]
    constructor
    · rintro ⟨y, hy, h⟩; exact ⟨y, hy, by rw [h]⟩
    · rintro ⟨y, hy, h⟩; exact ⟨y, hy, by ext i j; exact (congrFun (congrFun h j) i).symm⟩
  rw [hpre]
  exact himg.preimage (continuous_pi fun j => continuous_pi fun i =>
    (LerayComplex.ArchSOC.continuous_mat _).matrix_elem i j).measurable

theorem qRe_eq (w : {w : InfinitePlace F // w.IsReal}) : QRe Q₀ w = pureForm (sR w (a : F)) (sR w (b : F)) := by
  rw [QRe, hQF, pureForm_map_ringHom]

theorem qCx_eq (w : {w : InfinitePlace F // w.IsComplex}) : QCx Q₀ w = pureForm (sC w (a : F)) (sC w (b : F)) := by
  rw [QCx, hQF, pureForm_map_ringHom]

theorem tendsto_aRw (ha : a ≠ 0) (hb : b ≠ 0) (w : {w : InfinitePlace F // w.IsReal})
    (hQ : gramDetR (QRe Q₀ w) ≠ 0) :
    Tendsto (fun δ => (lerayMeasure (QRe Q₀ w) hQ (aRw a b w δ)).toReal / (volume (ball (0 : Fin 3 → ℝ) δ)).toReal)
      (𝓝[>] 0) (𝓝 (1 / (8 * |sR w (a : F)| ^ 3 * |sR w (b : F)| ^ 3))) := by
  have hA : sR w (a : F) ≠ 0 := (map_ne_zero _).2 (by exact_mod_cast ha)
  have hB : sR w (b : F) ≠ 0 := (map_ne_zero _).2 (by exact_mod_cast hb)
  have key : ∀ (Q : QuadForm ℝ 3) (hQe : Q = pureForm (sR w (a : F)) (sR w (b : F))) (hQ : gramDetR Q ≠ 0),
      Tendsto (fun δ => (lerayMeasure Q hQ {g | ∃ z ∈ ball (0 : Fin 3 → ℝ) δ,
        ArchSOInst.mat Q g = cMat (sR w (a : F)) (sR w (b : F)) z}).toReal /
          (volume (ball (0 : Fin 3 → ℝ) δ)).toReal) (𝓝[>] 0)
        (𝓝 (1 / (8 * |sR w (a : F)| ^ 3 * |sR w (b : F)| ^ 3))) := by
    intro Q hQe hQ
    subst hQe
    exact tendsto_leray_quatBall hA hB hQ
  exact key _ (qRe_eq a b w) hQ

theorem tendsto_aCw (ha : a ≠ 0) (hb : b ≠ 0) (w : {w : InfinitePlace F // w.IsComplex})
    (hQ : LerayComplex.gramDetC (QCx Q₀ w) ≠ 0) :
    Tendsto (fun δ => (LerayComplex.lerayMeasureC (QCx Q₀ w) hQ (aCw a b w δ)).toReal /
      (volume (ball (0 : Fin 3 → ℂ) δ)).toReal)
      (𝓝[>] 0) (𝓝 (1 / (8 * ‖sC w (a : F)‖ ^ 3 * ‖sC w (b : F)‖ ^ 3) ^ 2)) := by
  have hA : sC w (a : F) ≠ 0 := (map_ne_zero _).2 (by exact_mod_cast ha)
  have hB : sC w (b : F) ≠ 0 := (map_ne_zero _).2 (by exact_mod_cast hb)
  have key : ∀ (Q : QuadForm ℂ 3) (hQe : Q = pureForm (sC w (a : F)) (sC w (b : F)))
      (hQ : LerayComplex.gramDetC Q ≠ 0),
      Tendsto (fun δ => (LerayComplex.lerayMeasureC Q hQ {g | ∃ z ∈ ball (0 : Fin 3 → ℂ) δ,
        LerayComplex.ArchSOC.mat Q g = cMat (sC w (a : F)) (sC w (b : F)) z}).toReal /
          (volume (ball (0 : Fin 3 → ℂ) δ)).toReal) (𝓝[>] 0)
        (𝓝 (1 / (8 * ‖sC w (a : F)‖ ^ 3 * ‖sC w (b : F)‖ ^ 3) ^ 2)) := by
    intro Q hQe hQ
    subst hQe
    exact tendsto_lerayC_quatBall hA hB hQ
  exact key _ (qCx_eq a b w) hQ

/-! ### The Haar constant -/

variable (F) in
/-- **The archimedean constant** $K_\infty = c_F\prod_{w\ \mathrm{real}}|8a^3b^3|_w^{-1}
\prod_{w\ \mathrm{complex}}|8a^3b^3|_w^{-1}$ ($|x|_w = |x|^2$ at a complex place $w$). *Update:* before Weil's
normalization at the complex places entered `muArchTamSO`, this constant carried an extra factor $2^{-3r_2}$. -/
def kInf : ℝ := cF F 3 * (∏ w : {w : InfinitePlace F // w.IsReal}, 1 / (8 * |sR w (a : F)| ^ 3 * |sR w (b : F)| ^ 3)) *
  (∏ w : {w : InfinitePlace F // w.IsComplex}, 1 / (8 * ‖sC w (a : F)‖ ^ 3 * ‖sC w (b : F)‖ ^ 3) ^ 2)

theorem muArchTamSO_prod (ha : a ≠ 0) (hb : b ≠ 0) (δ : ℝ) :
    muArchTamSO Q₀ (nondegenerate_pureFormO a b ha hb)
        ((univ.pi fun w => aRw a b w δ) ×ˢ (univ.pi fun w => aCw a b w δ)) =
      ENNReal.ofReal (cF F 3 * cxWeil F 3) *
        ((∏ w, lerayMeasure (QRe Q₀ w) (gramDetR_QRe_ne_zero Q₀ (nondegenerate_pureFormO a b ha hb) w)
          (aRw a b w δ)) *
        (∏ w, LerayComplex.lerayMeasureC (QCx Q₀ w)
          (gramDetC_QCx_ne_zero Q₀ (nondegenerate_pureFormO a b ha hb) w) (aCw a b w δ))) := by
  have hQ := nondegenerate_pureFormO a b ha hb
  have hsf : ∀ w, SigmaFinite (lerayMeasure (QRe Q₀ w) (gramDetR_QRe_ne_zero Q₀ hQ w)) := fun w => by
    have := isHaarMeasure_lerayMeasure (gramDetR_QRe_ne_zero Q₀ hQ w); infer_instance
  have hsfC : ∀ w, SigmaFinite (LerayComplex.lerayMeasureC (QCx Q₀ w) (gramDetC_QCx_ne_zero Q₀ hQ w)) :=
    fun w => by have := LerayComplex.isHaarMeasure_lerayMeasureC (gramDetC_QCx_ne_zero Q₀ hQ w); infer_instance
  rw [muArchTamSO, Measure.smul_apply, smul_eq_mul, LerayArch.muArchNF, LerayArch.muArchLeray, Measure.prod_prod,
    Measure.pi_pi, Measure.pi_pi]

theorem measurableSet_E (ha : a ≠ 0) (hb : b ≠ 0) {δ : ℝ} (hδ : RadOK a b δ) :
    MeasurableSet ((QuotientGroup.mk : (QuatInf (a : F) (b : F))ˣ → PDInf a b) '' sBall a b δ) := by
  have h : (QuotientGroup.mk : (QuatInf (a : F) (b : F))ˣ → PDInf a b) '' sBall a b δ =
      pdInfEquiv a b ha hb ⁻¹' (pdInfEquiv a b ha hb ''
        ((QuotientGroup.mk : (QuatInf (a : F) (b : F))ˣ → PDInf a b) '' sBall a b δ)) :=
    ((pdInfEquiv a b ha hb).toEquiv.preimage_image _).symm
  rw [h, image_pdInfEquiv_sBall ha hb hδ]
  refine ((MeasurableSet.univ_pi fun w => measurableSet_aRw a b w ha (hδ.ltR w)).prod
    (MeasurableSet.univ_pi fun w => measurableSet_aCw a b w ha (hδ.ltC w))).preimage
    (pdInfEquiv a b ha hb).continuous.measurable

/-- **The Haar constant is $K_\infty$**: Weil's measure on $PD^\times(\mathbb A)$ against
$\mu^{\mathrm{Tam}}_\infty\times\mu_{PD,f}$. -/
theorem haarConst_eq (ha : a ≠ 0) (hb : b ≠ 0) (c : ℝ≥0)
    (hc : (nuRef ha hb).map (pdSplit a b ha hb).symm =
      (c : ℝ≥0∞) • muPD (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha) (by simpa using hb)) :
    (c : ℝ) = kInf F a b := by
  have hQ := nondegenerate_pureFormO a b ha hb
  set Lr : {w : InfinitePlace F // w.IsReal} → ℝ → ℝ := fun w δ =>
    (lerayMeasure (QRe Q₀ w) (gramDetR_QRe_ne_zero Q₀ hQ w) (aRw a b w δ)).toReal
  set Lc : {w : InfinitePlace F // w.IsComplex} → ℝ → ℝ := fun w δ =>
    (LerayComplex.lerayMeasureC (QCx Q₀ w) (gramDetC_QCx_ne_zero Q₀ hQ w) (aCw a b w δ)).toReal
  set vR : ℝ → ℝ := fun δ => (volume (ball (0 : Fin 3 → ℝ) δ)).toReal
  set vC : ℝ → ℝ := fun δ => (volume (ball (0 : Fin 3 → ℂ) δ)).toReal
  set LHS : ℝ → ℝ := fun δ => cF F 3 * cxWeil F 3 * (∏ w, Lr w δ / vR δ) * (∏ w, Lc w δ / vC δ) /
    ((2 : ℝ) ^ nrComplexPlaces F) ^ 3
  have tL : Tendsto LHS (𝓝[>] 0) (𝓝 (kInf F a b)) := by
    have t1 := tendsto_finsetProd (Finset.univ : Finset {w : InfinitePlace F // w.IsReal})
      fun w _ => tendsto_aRw a b ha hb w (gramDetR_QRe_ne_zero Q₀ hQ w)
    have t2 := tendsto_finsetProd (Finset.univ : Finset {w : InfinitePlace F // w.IsComplex})
      fun w _ => tendsto_aCw a b ha hb w (gramDetC_QCx_ne_zero Q₀ hQ w)
    have h := ((t1.const_mul (cF F 3 * cxWeil F 3)).mul t2).div_const (((2 : ℝ) ^ nrComplexPlaces F) ^ 3)
    have h2 : ((2 : ℝ) ^ nrComplexPlaces F) ^ 3 ≠ 0 := by positivity
    have hk : cF F 3 * cxWeil F 3 * (∏ w : {w : InfinitePlace F // w.IsReal},
        1 / (8 * |sR w (a : F)| ^ 3 * |sR w (b : F)| ^ 3)) *
        (∏ w : {w : InfinitePlace F // w.IsComplex}, 1 / (8 * ‖sC w (a : F)‖ ^ 3 * ‖sC w (b : F)‖ ^ 3) ^ 2) /
          ((2 : ℝ) ^ nrComplexPlaces F) ^ 3 = kInf F a b := by
      rw [kInf, cxWeil_three, show (8 : ℝ) ^ nrComplexPlaces F = ((2 : ℝ) ^ nrComplexPlaces F) ^ 3 by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num]
      field_simp
    rw [hk] at h
    exact h
  have tR := (tendsto_box_ratio a b).const_mul (c : ℝ)
  rw [mul_one] at tR
  refine tendsto_nhds_unique (tR.congr' ?_) tL
  have hT0 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (omegaInf F (tBall F δ)).toReal ≠ 0 :=
    (tendsto_omegaInf_tBall (F := F)).eventually_ne one_ne_zero |>.mp
      (Eventually.of_forall fun δ h h0 => h (by rw [h0, zero_div]))
  filter_upwards [eventually_radOK a b, hT0] with δ hδ hT
  have hbox := box_identity ha hb c hc (measurableSet_tBall δ) measurableSet_ball (measurableSet_E a b ha hb hδ)
  rw [show sInf a b (tBall F δ) (ball 0 δ) = sBall a b δ from rfl, image_pdInfEquiv_sBall ha hb hδ,
    muArchTamSO_prod a b ha hb δ] at hbox
  have hr := congrArg ENNReal.toReal hbox
  simp only [ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.coe_toReal] at hr
  have hsd := congrArg ENNReal.toReal (selfDual3_ball F hδ.pos)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at hsd
  have hvR : vR δ ≠ 0 := (toReal_volume_ball_pos volume hδ.pos).ne'
  have hvC : vC δ ≠ 0 := (toReal_volume_ball_pos volume hδ.pos).ne'
  have h2 : ((2 : ℝ) ^ nrComplexPlaces F) ^ 3 ≠ 0 := by positivity
  simp only [LHS, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  change (c : ℝ) * ((omegaQuatInf (a : F) (b : F) (sBall a b δ)).toReal / (omegaInf F (tBall F δ)).toReal /
    ((Measure.pi fun _ : Fin 3 => Analysis.selfDualInf (F := F)) (ball 0 δ)).toReal) = _
  rw [hsd]
  have hcF : 0 ≤ cF F 3 * cxWeil F 3 := mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) cxWeil_pos.le
  rw [ENNReal.toReal_ofReal hcF] at hr
  simp only [Finset.prod_const, Finset.card_univ] at hr ⊢
  have hX : (vR δ) ^ Fintype.card {w : InfinitePlace F // w.IsReal} ≠ 0 := pow_ne_zero _ hvR
  have hY : (vC δ) ^ Fintype.card {w : InfinitePlace F // w.IsComplex} ≠ 0 := pow_ne_zero _ hvC
  change (c : ℝ) * ((omegaQuatInf (a : F) (b : F) (sBall a b δ)).toReal / (omegaInf F (tBall F δ)).toReal /
    (((2 : ℝ) ^ nrComplexPlaces F) ^ 3 * (vR δ) ^ Fintype.card {w : InfinitePlace F // w.IsReal} *
      (vC δ) ^ Fintype.card {w : InfinitePlace F // w.IsComplex})) = _
  rw [← mul_div_assoc, ← mul_div_assoc, ← hr]
  field_simp
  rfl

end Places

end QuadFormsKB.Tamagawa.Measure.Weil
